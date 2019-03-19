module Compile where

import Parse (file,Statement(Assign,Exit,Print,Call,Write,Fn,Return,PrimitiveFn),Expr(Literalu8,LiteralListu8,Var,MethodCall))
import Parse (AsmDef(asm_prefix,asm_vex,asm_op,asm_w,asm_mmmmm,asm_slash))
import Parse (AsmVex(Vex,Vex128,Vex256,Evex,Evex128,Evex256,Evex512,Unspecified))
import Parse (AsmPrefix(Optional66,Prefix66,PrefixF3,PrefixF2))
import Parse (AsmM(M0F,M0F38,M0F3A), AsmW(W0,W1,WIG))
import Parse (Type(ByReg,ByRM,ByMem,Known),PlainType(U8,U16,U8Q,U8X,U8Y,U8Z,U8V,U16Q,U16X,U16Y,U16Z,U16V))
import X86

import Control.Monad.State (State,get,put,runState)
import Text.Parsec.String (parseFromFile)
import Text.Parsec.Error (ParseError)
import Data.ByteString.Builder
import qualified Data.ByteString.Lazy as L
import Data.List (sort)
import Data.Word (Word8)
import Data.Monoid ((<>))
import System.IO (withBinaryFile,IOMode (WriteMode))

data InstrTech = Mmx | Sse | Avx | Avx2 deriving (Eq,Show)
data InstrR = RConst Word8 | RArg Int | RRet | RNone | RDest deriving (Eq,Show)
data InstrRM = RMArg Int | RMRet | RMNone | RMDest deriving (Eq,Show)
data InstrV = VArg Int | VRet | V15 | NoV deriving (Eq,Show)
data AsmInstr = AsmInstr {
    instr_width :: Int,     -- 64, 128, 256 or 512
    instr_tech :: InstrTech,-- which technology level & instruction encoding to use for this instruction
    instr_pp :: Word8,      -- 0->none, 1->66, 2->F3, 3->F2
    instr_mmmmm :: Word8,   -- 1->0F, 2->0F38, 3->0F3A
    instr_w :: Word8,       -- 0 or 1. Currently set to 0 for "WIG" (W-ignored) instructions
    instr_op :: Word8,      -- the single byte primary opcode
    instr_args :: Int,      -- argument count.
    instr_r :: InstrR,      -- set the ModR/M r value to this argument, return register or constant value. If RNone, no ModR/M byte.
    instr_rm :: InstrRM,    -- set the ModR/M rm value to this argument or return register.
    instr_vvvv :: InstrV,   -- set the VEX.vvvv value to this argument, or to 15 if not present
    instr_imbytes :: Int    -- number of bytes in the immediate value, or 0 if there isn't one. Immediate is always written last.
    } deriving (Eq,Show)
data Primitive = Primitive [(String,Type)] Type AsmInstr deriving (Eq,Show)
data EnvThing = ERX Reg | ERY Reg | ERQ Reg | Label Int | Prim [Primitive] deriving Eq
data Width = WidthX | WidthY | WidthZ | WidthQ | WidthB deriving (Eq,Show)
data EnvKey = EVar String | EUniform Word8 | ETemp deriving (Eq,Show)
type Env = [(EnvKey,EnvThing)]
type Literals = Code
type Elf = Code
data Fixup = JmpFixup Int String deriving (Eq,Show)
type Fixups = [Fixup]
data Result = ResR Reg | ResL Int deriving (Eq,Show)

type Compilation a = State (Env,Literals,Code,Fixups) a

-- Must compare address first
instance Ord Fixup where
    compare (JmpFixup a x) (JmpFixup b y) = compare (a,x) (b,y)

base_addr_for_literals = 0x08000000
stack_hi = 0x0a000000  -- it grows downwards
stack_lo = 0x09000000
use_evex = False

--------------------------------

-- until I figure out how to correctly choose between different instruction technologies
want_tech :: (InstrTech,Int) -> Bool
want_tech (Avx,_) = True
want_tech (_,_) = False

asm_widths :: AsmDef -> [(InstrTech,Int)]
asm_widths a =
    let
        mmx = (Mmx,64)
        sse = (Sse,128)
        x = (Avx,128)
        y = (Avx,256)
        x' = (Avx2,128)
        y' = (Avx2,256)
        z' = (Avx2,512)
    in filter want_tech (if asm_prefix a == Optional66 then
        if asm_vex a == Unspecified then
            [mmx, sse, x, y, x', y', z']
        else
            error "(66) cannot be combined with VEX or EVEX"
    else
        case asm_vex a of
            Unspecified -> [sse, x, y, x', y', z']
            Vex -> [x, y, x', y', z']
            Vex128 -> [x, x']
            Vex256 -> [y, y']
            Evex -> [x', y', z']
            Evex128 -> [x']
            Evex256 -> [y']
            Evex512 -> [z'])

translate_pp :: Int -> AsmPrefix -> Word8
translate_pp 64 Optional66 = 0
translate_pp _ Optional66 = 1
translate_pp _ Prefix66 = 1
translate_pp _ PrefixF3 = 2
translate_pp _ PrefixF2 = 3

translate_mmmmm :: AsmM -> Word8
translate_mmmmm M0F = 1
translate_mmmmm M0F38 = 2
translate_mmmmm M0F3A = 3

supports_vex :: AsmVex -> Bool
supports_vex Unspecified = True
supports_vex Vex = True
supports_vex Vex128 = True
supports_vex Vex256 = True
supports_vex _ = False

translate_imm :: [Type] -> (Int,[Type])
translate_imm [] = (0,[])
translate_imm xs =
    case last xs of
        Known U8 -> (1, init xs)
        Known U16 -> (2, init xs)
        Known t -> error ("Unknown immediate type: " ++ show t)
        _ -> (0, xs)

instr_r_rm_v :: Bool -> [Type] -> Maybe Word8 -> (InstrR,InstrRM,InstrV)
instr_r_rm_v False [_] (Just n) = (RConst n, RMDest, NoV)     -- e.g. psslw(imm)
instr_r_rm_v True  [_] (Just n) = (RConst n, RMArg 0, VRet)   -- e.g. vpsllw(imm)
instr_r_rm_v False [_] Nothing = (RRet, RMArg 0, NoV)   -- e.g. pabsb
instr_r_rm_v True  [_] Nothing = (RRet, RMArg 0, V15)   -- e.g. vpbroadcastb
instr_r_rm_v False [ByReg _,ByRM _] Nothing = (RDest, RMArg 1, NoV)     -- e.g. paddb
instr_r_rm_v True  [ByReg _,ByRM _] Nothing = (RRet, RMArg 1, VArg 0)   -- e.g. vpaddb

translate_asm_width :: [Type] -> Type -> AsmDef -> (InstrTech,Int) -> AsmInstr
translate_asm_width args ret a (tech,width) =
    let
        (imbytes, args') = translate_imm args
        is_avx = tech /= Mmx && tech /= Sse
        (r, rm, vvvv) = instr_r_rm_v is_avx args' (asm_slash a)
    in AsmInstr {
        instr_width = width,
        instr_tech = tech,
        instr_pp = translate_pp width (asm_prefix a),
        instr_mmmmm = translate_mmmmm (asm_mmmmm a),
        instr_w = (if asm_w a == W1 then 1 else 0),
        instr_op = asm_op a,
        instr_args = length args,
        instr_r = r,
        instr_rm = rm,
        instr_vvvv = vvvv,
        instr_imbytes = imbytes
        }

translate_asm :: [Type] -> Type -> AsmDef -> [AsmInstr]
translate_asm args ret a = map (translate_asm_width args ret a) (asm_widths a)

--------------------------------
emit :: Code -> Compilation ()
emit code' = do
    (env,lit,code,fix) <- get
    put (env, lit, code <> code', fix)

emit_jmp :: String -> (Int -> Code) -> Compilation ()
emit_jmp label codef = do
    (env,lit,code,fix) <- get
    case lookup (EVar label) env of
        Just (Label a) -> put (env, lit, code <> codef a, fix)
        Nothing -> let code' = code <> codef 0 in
            put (env, lit, code', JmpFixup (clength code' - 4) label : fix)

padding :: Int -> Int -> Code
padding align codelen =
    case codelen `mod` align of
        0 -> mempty
        n -> zeros (align-n)

alloc_literal_aligned :: Int -> [Word8] -> Compilation Int
alloc_literal_aligned align xs = do
    (env,lit,code,fix) <- get
    let lit' = lit <> padding align (clength lit)
    put (env, lit' <> bytes xs, code, fix)
    return (base_addr_for_literals + clength lit')

env_contains_reg :: Env -> Reg -> Bool
env_contains_reg [] _ = False
env_contains_reg ((x,r):e) reg = r==ERX reg || r==ERY reg || r==ERQ reg || env_contains_reg e reg

env_contains_uniform :: Env -> Word8 -> Maybe Reg
env_contains_uniform [] _ = Nothing
env_contains_uniform ((EUniform n',ERY r):e) n = if n'==n then Just r else env_contains_uniform e n
env_contains_uniform ((x,_):e) n = env_contains_uniform e n

fresh_xmm_from :: Word8 -> Env -> Reg
fresh_xmm_from n env =
    if env_contains_reg env (Xmm n) then
        fresh_xmm_from (n+1) env
    else if n >= 16 then
        error "Run out of vector registers"
    else
        Xmm n

fresh_gpr_from :: Word8 -> Env -> Reg
fresh_gpr_from n env =
    if env_contains_reg env (Gpr n) then
        fresh_gpr_from (n+1) env
    else if n >= 16 then
        error "Run out of general purpose registers"
    else
        Gpr n

fresh_ymm :: EnvKey -> Compilation Reg
fresh_ymm x = do
    (env,lit,code,fix) <- get
    let result = fresh_xmm_from 0 env
    put (env ++ [(x,ERY result)],lit,code,fix)
    return result

fresh_gpr :: String -> Compilation Reg
fresh_gpr x = do
    (env,lit,code,fix) <- get
    let result = fresh_gpr_from 0 env
    put (env ++ [(EVar x,ERQ result)],lit,code,fix)
    return result

env_lookup :: String -> Compilation (Maybe EnvThing)
env_lookup x = do
    (env,_,_,_) <- get
    return $ lookup (EVar x) env

env_lookup_uniform :: Word8 -> Compilation (Maybe Reg)
env_lookup_uniform n = do
    (env,_,_,_) <- get
    return (env_contains_uniform env n)

fresh_temp_ymm :: Compilation Reg
fresh_temp_ymm = fresh_ymm ETemp


find_or_fresh_xmm :: String -> Compilation Reg
find_or_fresh_xmm x = do
    mb <- env_lookup x
    case mb of
        Nothing -> fresh_ymm (EVar x)
        Just (ERX (Xmm r)) -> return (Xmm r)
        Just (ERY (Xmm r)) -> return (Xmm r)
        Just _ -> error ("Found " ++ x ++ " but it wasn't an xmm regiser")

find_xmm :: String -> Compilation (Reg,Width)
find_xmm x = do
    mb <- env_lookup x
    case mb of
        Nothing -> error ("Could not find xmm register for " ++ x)
        Just (ERX (Xmm r)) -> return (Xmm r,WidthX)
        Just (ERY (Xmm r)) -> return (Xmm r,WidthY)
        Just _ -> error ("Found " ++ x ++ " but it wasn't an xmm regiser")

find_reg :: String -> Compilation (Reg,Width)
find_reg x = do
    mb <- env_lookup x
    case mb of
        Nothing -> error ("Could not find xmm register for " ++ x)
        Just (ERX (Xmm r)) -> return (Xmm r, WidthX)
        Just (ERY (Xmm r)) -> return (Xmm r, WidthY)
        Just _ -> error ("Found " ++ x ++ " but it wasn't an xmm regiser")

find_or_emit_uniform :: Word8 -> Compilation Reg
find_or_emit_uniform n = do
    mb <- env_lookup_uniform n
    case mb of
        Just r -> return r
        Nothing -> do
            let name = show n
            if use_evex then do
                xreg <- fresh_gpr name
                yreg <- fresh_ymm (EVar name)
                emit (old_oi mov_oi8 xreg (fromIntegral n))
                emit (evex256_rm evpbroadcastb_gpr_rm yreg (R xreg))
                return yreg
            else do
                addr <- alloc_literal_aligned 1 [n]
                yreg <- fresh_ymm (EVar name)
                emit (vex256_rm vpbroadcastb_rm yreg (AbsMem addr))
                return yreg

args_to_env :: Word8 -> [String] -> Env
args_to_env _ [] = []
args_to_env n (x:xs) = (EVar x, ERX (Xmm n)) : args_to_env (n+1) xs

is_global :: (EnvKey,EnvThing) -> Bool
is_global (_,Label _) = True
is_global (_,Prim _) = True
is_global _ = False

start_new_function :: String -> [String] -> Compilation ()
start_new_function f args = do
    (env,lit,code,fix) <- get
    let env' = args_to_env 0 args ++ [(EVar f,Label (clength code))] ++ filter is_global env
    put (env',lit,code,fix)

thing_tweak_width :: Width -> EnvThing -> EnvThing
thing_tweak_width WidthX (ERX reg) = ERX reg
thing_tweak_width WidthX (ERY reg) = ERX reg
thing_tweak_width WidthY (ERX reg) = ERY reg
thing_tweak_width WidthY (ERY reg) = ERY reg

env_tweak_width :: Width -> String -> Env -> Env
env_tweak_width _ x [] = error ("env_tweak_width: variable " ++ x ++ " not found")
env_tweak_width width x ((y,thing):env)
    | EVar x == y = (y,thing_tweak_width width thing):env
    | otherwise = (y,thing) : env_tweak_width width x env

tweak_width :: Width -> String -> Compilation ()
tweak_width width x = do
    (env,lit,code,fix) <- get
    let env' = env_tweak_width width x env
    put (env',lit,code,fix)

is_not_temp :: (EnvKey,EnvThing) -> Bool
is_not_temp (ETemp,_) = False
is_not_temp _ = True

discard_temps :: Compilation ()
discard_temps = do
    (env,lit,code,fix) <- get
    let env' = filter is_not_temp env
    put (env',lit,code,fix)

env_replace :: EnvKey -> EnvThing -> Env -> Env
env_replace x thing [] = error ("env_replace: variable " ++ show x ++ " not found")
env_replace x thing ((y,t):env)
    | x == y = ((x,thing):env)
    | otherwise = (y,t):env_replace x thing env

map_type :: (PlainType -> PlainType) -> Type -> Type
map_type f (ByReg t) = ByReg (f t)
map_type f (ByMem t) = ByMem (f t)
map_type f (ByRM t) = ByRM (f t)
map_type f (Known t) = Known (f t)

specialize_plain :: Int -> PlainType -> PlainType
specialize_plain 64 U8V = U8Q
specialize_plain 128 U8V = U8X
specialize_plain 256 U8V = U8Y
specialize_plain 512 U8V = U8Z
specialize_plain 64 U16V = U16Q
specialize_plain 128 U16V = U16X
specialize_plain 256 U16V = U16Y
specialize_plain 512 U16V = U16Z
specialize_plain _ t = t

specialize_type :: AsmInstr -> Type -> Type
specialize_type a = map_type (specialize_plain (instr_width a))

specialize_args :: AsmInstr -> [(String,Type)] -> [(String,Type)]
specialize_args a args = map (\(x,t) -> (x, specialize_type a t)) args

define_primitive_function :: String -> [(String,Type)] -> Type -> [AsmInstr] -> Compilation ()
define_primitive_function f args ret instrs = do
    (env,lit,code,fix) <- get
    let newprims = [Primitive (specialize_args a args) (specialize_type a ret) a | a <- instrs]
    let env' = (case lookup (EVar f) env of
            Nothing -> (EVar f, Prim newprims) : env
            Just (Prim oldprims) -> env_replace (EVar f) (Prim (newprims++oldprims)) env)
    put (env',lit,code,fix)

---------------------------------
emit_binop :: Width -> String -> Reg -> Reg -> RM -> Compilation ()
emit_binop WidthX "addb" x y z = emit (vex128_rrm vpaddb_rrm x y z)
emit_binop WidthY "addb" x y z = emit (vex256_rrm vpaddb_rrm x y z)
emit_binop WidthX "and" x y z = emit (vex128_rrm vpand_rrm x y z)
emit_binop WidthY "and" x y z = emit (vex256_rrm vpand_rrm x y z)
emit_binop WidthX "cmpgtb" x y z = emit (vex128_rrm vpcmpgtb_rrm x y z)
emit_binop WidthY "cmpgtb" x y z = emit (vex256_rrm vpcmpgtb_rrm x y z)
emit_binop WidthX "or" x y z = emit (vex128_rrm vpor_rrm x y z)
emit_binop WidthY "or" x y z = emit (vex256_rrm vpor_rrm x y z)

emit_shift :: Width -> String -> Reg -> RM -> Word8 -> Compilation ()
emit_shift WidthX "sllw" x y im = emit (vex128_rmi_slash vpsllw_rmi_slash x y im)
emit_shift WidthY "sllw" x y im = emit (vex256_rmi_slash vpsllw_rmi_slash x y im)
emit_shift WidthX "srlw" x y im = emit (vex128_rmi_slash vpsrlw_rmi_slash x y im)
emit_shift WidthY "srlw" x y im = emit (vex256_rmi_slash vpsrlw_rmi_slash x y im)

emit_uop :: Width -> String -> Reg -> RM -> Compilation ()
emit_uop WidthX "zxbw" x y = emit (vex128_rm vpmovzxbw_rm x y)
emit_uop WidthY "zxbw" x y = emit (vex256_rm vpmovzxbw_rm x y)

is_binop :: String -> Bool
is_binop x = x `elem` ["addb","and","cmpgtb","or"]

is_shift :: String -> Bool
is_shift x = x `elem` ["sllw","srlw"]

is_uop :: String -> Bool
is_uop x = x `elem` ["zxbw"]

get_constant_u8 :: Expr -> Word8
get_constant_u8 (Literalu8 n) = n
get_constant_u8 e = error ("Cannot interpret expression as constant u8: " ++ show e)

width_of :: PlainType -> Width
width_of U8Q = WidthQ
width_of U16Q = WidthQ
width_of U8X = WidthX
width_of U16X = WidthX
width_of U8Y = WidthY
width_of U16Y = WidthY
width_of U8Z = WidthZ
width_of U16Z = WidthZ
width_of x = error ("Why do you want the width of " ++ show x)

unwrap_type :: Type -> PlainType
unwrap_type (ByReg t) = t
unwrap_type (ByMem t) = t
unwrap_type (ByRM t) = t
unwrap_type (Known t) = t

arg_matches :: (Result,Width) -> (String,Type) -> Bool
arg_matches (ResR _,w) (_,ByReg t) = width_of t == w
arg_matches (ResR _,w) (_,ByRM t) = width_of t == w
arg_matches (ResL _,WidthB) (_,Known U8) = True
arg_matches (ResL _,WidthB) (_,ByReg U8X) = True   -- auto-broadcasts and auto-regifies
arg_matches (ResL _,WidthB) (_,ByRM U8X) = True    --
arg_matches (ResL _,WidthB) (_,ByReg U8Y) = True   --
arg_matches (ResL _,WidthB) (_,ByRM U8Y) = True    --
arg_matches _ _ = False

find_or_emit_uniform_result :: Int -> Compilation Result
find_or_emit_uniform_result n = do
    r <- find_or_emit_uniform (fromIntegral n)
    return (ResR r)

-- assumes has already passed arg_matches
autoconvert :: ((Result,Width),(String,Type)) -> Compilation Result
autoconvert ((ResR r,_),(_,ByReg _)) = return (ResR r)
autoconvert ((ResR r,_),(_,ByRM _)) = return (ResR r)
autoconvert ((ResL n,WidthB),(_,Known U8)) = return (ResL n)
autoconvert ((ResL n,WidthB),(_,ByReg U8X)) = find_or_emit_uniform_result n
autoconvert ((ResL n,WidthB),(_,ByRM U8X)) = find_or_emit_uniform_result n
autoconvert ((ResL n,WidthB),(_,ByReg U8Y)) = find_or_emit_uniform_result n
autoconvert ((ResL n,WidthB),(_,ByRM U8Y)) = find_or_emit_uniform_result n

prim_matches :: [(Result,Width)] -> Primitive -> Bool
prim_matches ws (Primitive args' _ _) = length ws == length args' && and (zipWith arg_matches ws args')

lookup_prim :: String -> [(Result,Width)] -> Compilation Primitive
lookup_prim f ws = do
    (env,_,_,_) <- get
    case lookup (EVar f) env of
        Just (Prim candidates) ->
            case filter (prim_matches ws) candidates of
                [x] -> return x
                [] -> error ("No candidates matched for primitive fn " ++ f ++ show ws ++ ". Considered:\n" ++ concat (map (\(Primitive args _ _)->show args ++ "\n") candidates))
                er -> error ("Multiple candidates matched for primitive fn " ++ f ++ show ws ++ ":\n" ++ concat (map (\(Primitive args _ a)->show args ++ " " ++ show (instr_tech a) ++ "\n") er))
        Nothing -> error ("Could not find primitive fn " ++ f ++ " in " ++ show (map fst env))

vex_width_code :: Int -> Word8
vex_width_code 128 = 0
vex_width_code 256 = 1
vex_width_code 512 = 2

insist_reg :: Result -> Reg
insist_reg (ResR r) = r

insist_rm :: Result -> RM
insist_rm (ResR r) = R r

insist_lit :: Result -> Int
insist_lit (ResL n) = n

lookup_instr_r :: InstrR -> [Result] -> Reg -> Reg
lookup_instr_r (RConst n) _ _ = Slash n
lookup_instr_r (RArg i) args _ = insist_reg (args !! i)
lookup_instr_r RRet _ ret = ret
lookup_instr_r RNone _ _ = NoReg
lookup_instr_r RDest args _ = insist_reg (args !! 0)

lookup_instr_rm :: InstrRM -> [Result] -> Reg -> RM
lookup_instr_rm (RMArg i) args _ = insist_rm (args !! i)
lookup_instr_rm RMRet _ ret = R ret
lookup_instr_rm RMNone _ _ = NoRM
lookup_instr_rm RMDest args _ = insist_rm (args !! 0)

lookup_instr_v :: InstrV -> [Result] -> Reg -> Reg
lookup_instr_v (VArg i) args _ = insist_reg (args !! i)
lookup_instr_v VRet _ ret = ret
lookup_instr_v V15 _ ret = NoReg

lookup_instr_imm :: Int -> [Result] -> Code
lookup_instr_imm 0 _ = mempty
lookup_instr_imm imbytes args = int_as_n_bytes imbytes $ insist_lit $ last args

emit_prim :: AsmInstr -> [Result] -> Reg -> Compilation ()
emit_prim a args ret =
    -- vex_misc w pp m_mmmm l op r rv rm imm
    if instr_tech a == Avx then
        emit (vex_misc
            (instr_w a)
            (instr_pp a)
            (instr_mmmmm a)
            (vex_width_code $ instr_width a)
            (instr_op a)
            (lookup_instr_r (instr_r a) args ret)
            (lookup_instr_v (instr_vvvv a) args ret)
            (lookup_instr_rm (instr_rm a) args ret)
            (lookup_instr_imm (instr_imbytes a) args))
    else
        error ("Not currently encoding technology " ++ show (instr_tech a))

compile_expr_to :: Reg -> Expr -> Compilation Width
compile_expr_to xreg (Var y) = do
    (yreg,yw) <- find_xmm y
    if xreg == yreg then do
        return yw
    else if yw == WidthX then do
        emit (vex128_rm vmovdqa_mr xreg (R yreg))
        return WidthX
    else if yw == WidthY then do
        emit (vex256_rm vmovdqa_mr xreg (R yreg))
        return WidthY
    else
        error ("Cannot move " ++ show yw)
compile_expr_to xreg (LiteralListu8 ls) =
    if length ls == 16 then
        do
            addr <- alloc_literal_aligned 16 ls
            emit (vex128_rm vmovdqa_rm xreg (AbsMem addr))
            return WidthX
    else
        error "Expected exactly 16 bytes"

compile_expr_to xreg (MethodCall ye f arges) = do
    args <- mapM (compile_expr Nothing) (ye:arges)
    Primitive formals rt asm <- lookup_prim f args
    ress <- mapM autoconvert (zip args formals)
    emit_prim asm ress xreg
    return $ width_of $ unwrap_type rt

{-compile_expr_to xreg (MethodCall ye "zxbw" []) = do
    (yreg,yw) <- compile_expr Nothing ye
    if yw == WidthX then do
        emit (vex256_rm vpmovzxbw_rm xreg (R yreg))
        return WidthY
    else
        error ("Cannot zxbw " ++ show yw)
compile_expr_to xreg (MethodCall ye binop [ze])
    | is_binop binop = do
        (yreg,yw) <- compile_expr Nothing ye
        (zreg,zw) <- compile_expr (Just yw) ze
        if yw == WidthX && zw == WidthX then do
            emit_binop WidthX binop xreg yreg (R zreg)
            return WidthX
        else if yw == WidthY && zw == WidthY then do
            emit_binop WidthY binop xreg yreg (R zreg)
            return WidthY
        else
            error ("Cannot " ++ show binop ++ " " ++ show yw ++ " " ++ show zw)
    | is_shift binop = do
        (yreg,yw) <- compile_expr Nothing ye
        let imm = get_constant_u8 ze
        emit_shift yw binop xreg (R yreg) imm
        return yw
-}
compile_expr_to _ e = error ("currently unable to compile expression " ++ show e)

compile_expr :: Maybe Width -> Expr -> Compilation (Result,Width)
compile_expr _ (Var x) = do
    (r,w) <- find_xmm x
    return (ResR r,w)
compile_expr (Just hint) (Literalu8 l) = do
    reg <- find_or_emit_uniform (fromIntegral l)
    return (ResR reg, hint)
compile_expr Nothing (Literalu8 n) = return (ResL (fromIntegral n),WidthB)
compile_expr _ e = do
    xreg <- fresh_temp_ymm
    width <- compile_expr_to xreg e
    return (ResR xreg,width)

reserve_for_args :: [Reg] -> Compilation [Reg]
reserve_for_args [] = return []
reserve_for_args (reg:regs) = do
    results <- reserve_for_args regs
    (env,lit,code,fix) <- get
    let (env',results') = (if env_contains_reg env reg
        then (env, results)
        else
            ((ETemp,ERY reg):env, reg:results))
    put (env',lit,code,fix)
    return results'

compile_args :: [Expr] -> Compilation ()
compile_args args = do
    let indices = [0..fromIntegral (length args)-1]
    reserved <- reserve_for_args $ map Xmm indices
    mapM_ (\(arg,i) -> compile_expr_to (Xmm i) arg) $ zip args indices

compile_statement :: Statement -> Compilation ()
compile_statement (Assign x e) = do
    xreg <- find_or_fresh_xmm x
    width <- compile_expr_to xreg e
    discard_temps
    tweak_width width x
compile_statement (Exit (Literalu8 l)) = do
    emit (old_oi mov_oi64 _di (fromIntegral l))   -- Pad l to 8 bytes, move into rdi for first argument to syscall
    emit (old_oi mov_oi64 _ax 60)                 -- syscall 60 is exit
    emit (sse_zo syscall_zo)
compile_statement (Call f args) = do
    compile_args args
    emit_jmp f (old_i call_i32)
compile_statement (Fn f args) = do
    start_new_function f args
compile_statement (Print (Var x)) = do
    (xreg,WidthX) <- find_xmm x
    yreg <- fresh_temp_ymm
    zreg <- fresh_temp_ymm
    ureg15 <- find_or_emit_uniform 0x0f
    ureg48 <- find_or_emit_uniform 48    -- difference between 0 and '0'
    ureg39 <- find_or_emit_uniform 39    -- difference between '9'+1 and 'a'
    ureg57 <- find_or_emit_uniform 57    -- '9'
    emit (vex128_rrm vpand_rrm yreg xreg (R ureg15))  -- y[]u8 contains lower nibbles
    emit (vex128_rmi_slash vpsrlw_rmi_slash zreg (R xreg) 4)
    emit (vex128_rrm vpand_rrm zreg zreg (R ureg15))  -- z[]u8 contains upper nibbles
    emit (vex256_rm vpmovzxbw_rm yreg (R yreg))       -- expand y[]u8 to y[]u16
    emit (vex256_rm vpmovzxbw_rm zreg (R zreg))       -- expand z[]u8 to z[]u16
    emit (vex256_rmi_slash vpsllw_rmi_slash yreg (R yreg) 8)       -- move lower nibbles into upper bytes
    emit (vex256_rrm vpor_rrm yreg yreg (R zreg))
    emit (vex256_rrm vpaddb_rrm yreg yreg (R ureg48)) -- turn 0 into '0', 9 into '9' and 10 into '9'+1
    emit (vex256_rrm vpcmpgtb_rrm zreg yreg (R ureg57))   -- z[]bool holds (y[] > '9')
    emit (vex256_rrm vpand_rrm zreg zreg (R ureg39))  -- z[]u8 holds (y[] > '9') ? 39 : 0
    emit (vex256_rrm vpaddb_rrm yreg yreg (R zreg))   -- 0->'0', 9->'9', 10->'a', 15->'f'
    emit (old_mi_slash sub_mi8_slash (R _sp) 32)
    emit (vex256_mr vmovdqu_mr (RegMem _sp) yreg)
    -- now do the write syscall
    emit (old_oi mov_oi64 _di 1)    -- stdout
    emit (old_rm mov_rm _si (R _sp))-- buf = rsp
    emit (old_oi mov_oi64 _dx 32)   -- count = 32
    emit (old_oi mov_oi64 _ax 1)    -- syscall 1 is write
    emit (sse_zo syscall_zo)
    emit (old_mi_slash add_mi8_slash (R _sp) 32)
compile_statement (Write (Var x)) = do
    (xreg,WidthY) <- find_xmm x
    emit (old_mi_slash sub_mi8_slash (R _sp) 32)
    emit (vex256_mr vmovdqu_mr (RegMem _sp) xreg)
    -- now do the write syscall
    emit (old_oi mov_oi64 _di 1)    -- stdout
    emit (old_rm mov_rm _si (R _sp))-- buf = rsp
    emit (old_oi mov_oi64 _dx 32)   -- count = 32
    emit (old_oi mov_oi64 _ax 1)    -- syscall 1 is write
    emit (sse_zo syscall_zo)
    emit (old_mi_slash add_mi8_slash (R _sp) 32)
compile_statement Return = do
    emit (old_zo ret_zo)
compile_statement (PrimitiveFn f args ret asm) = do
    let argtypes = map snd args
    let instrs = translate_asm argtypes ret asm
    define_primitive_function f args ret instrs
compile_statement x = error ("currently unable to compile " ++ show x)

setup_stack :: Compilation ()
setup_stack = do
    emit (old_oi mov_oi64 _sp (fromIntegral stack_hi))  -- remember, it grows downwards

compile_with :: [Statement] -> Compilation ()
compile_with [] = return ()
compile_with (s:ss) = do
    compile_statement s
    compile_with ss

---------------------------------
insist_label :: Env -> String -> Int
insist_label env x =
    case lookup (EVar x) env of
        Just (Label n) -> n
        _ -> error ("Could not find label: " ++ x)

perform_sorted_fixups :: Env -> Int -> Int -> L.ByteString -> [Fixup] -> Code
perform_sorted_fixups _ _ remaining lb [] = Code (lazyByteString lb) remaining
perform_sorted_fixups env pos remaining lb (JmpFixup addr x:fix) =
    let
        n = addr - pos
        (lb0, lb1) = L.splitAt (fromIntegral n) lb
        lb2 = L.drop 4 lb1
        value = insist_label env x - (addr+4)
        fixed = int_as_four_bytes value
        fixed' = perform_sorted_fixups env (addr + 4) (remaining - n - 4) lb2 fix
        code0 = Code (lazyByteString lb0) n
    in
        code0 <> fixed <> fixed'

perform_fixups :: Env -> Code -> Fixups -> Code
perform_fixups env code fixups =
    let
        lb = toLazyByteString $ code_as_builder code
        len = clength code
    in
        perform_sorted_fixups env 0 len lb (sort fixups)

make_elf :: Literals -> Code -> Elf
make_elf lit code =
    let
        lit' = lit <> padding 4096 (clength lit)
        code_start = fromIntegral (base_addr_for_literals + clength lit')
        entry_point = code_start
 
        strings = "\0.shstrtab\0.rodata\0.text\0"
        string_null = 0
        string_shstrtab = string_null + 1
        string_rodata = string_shstrtab + 10
        string_text = string_rodata + 8

        phnum = 3
        shnum = 4
        offset_padding = 0x40 + fromIntegral phnum * 0x38
        pad = padding 4096 (fromIntegral offset_padding)
        offset0 = offset_padding + fromIntegral (clength pad)
        offset1 = offset0 + fromIntegral (clength lit')
        offset_shstrtab = offset1 + fromIntegral (clength code)
        shoff = offset_shstrtab + fromIntegral (length strings)

        ei_mag = b 0x7f <> b 0x45 <> b 0x4c <> b 0x46  -- magic number
        ei_class = b 2   -- 64-bit
        ei_dat = b 1     -- little-endian
        ei_version = b 1
        ei_osabi = b 3   -- linux
        ei_pad = zeros 8
        e_ident = ei_mag <> ei_class <> ei_dat <> ei_version <> ei_osabi <> ei_pad
        e_type = wd 2     -- EXEC
        e_machine = wd 0x3e  -- x86-64
        e_version = dw 1
        e_entry = qw entry_point
        e_phoff = qw 0x40
        e_shoff = qw shoff
        e_flags = dw 0
        e_ehsize = wd 0x40
        e_phentsize = wd 0x38
        e_phnum = wd phnum
        e_shentsize = wd 0x40
        e_shnum = wd shnum
        e_shstrndx = wd 1

        elf_header = e_ident <> e_type <> e_machine <> e_version <> e_entry <> e_phoff <> e_shoff <> e_flags <> e_ehsize <> e_phentsize <> e_phnum <> e_shentsize <> e_shnum <> e_shstrndx

        p0_type = dw 1    -- LOAD
        p0_flags = dw 4   -- r
        p0_offset = qw offset0
        p0_vaddr = qw $ fromIntegral base_addr_for_literals
        p0_paddr = p0_vaddr
        p0_filesz = qw $ fromIntegral $ clength lit'
        p0_memsz = p0_filesz
        p0_align = qw 4096
        p0 = p0_type <> p0_flags <> p0_offset <> p0_vaddr <> p0_paddr <> p0_filesz <> p0_memsz <> p0_align
        
        p1_type = dw 1    -- LOAD
        p1_flags = dw 5   -- r+x
        p1_offset = qw offset1
        p1_vaddr = qw code_start
        p1_paddr = p1_vaddr
        p1_filesz = qw $ fromIntegral $ clength code
        p1_memsz = p1_filesz
        p1_align = qw 4096
        p1 = p1_type <> p1_flags <> p1_offset <> p1_vaddr <> p1_paddr <> p1_filesz <> p1_memsz <> p1_align

        p2_type = dw 1    -- LOAD
        p2_flags = dw 6   -- r+w
        p2_offset = qw 0
        p2_vaddr = qw stack_lo
        p2_paddr = p2_vaddr
        p2_filesz = qw 0
        p2_memsz = qw (stack_hi - stack_lo)
        p2_align = qw 4096
        p2 = p2_type <> p2_flags <> p2_offset <> p2_vaddr <> p2_paddr <> p2_filesz <> p2_memsz <> p2_align

        shstrtab = strbytes strings

        sh0_name = dw string_null
        sh0_type = dw 0  -- NULL
        sh0_flags = qw 0
        sh0_addr = qw 0
        sh0_offset = qw 0
        sh0_size = qw 0
        sh0_link = dw 0
        sh0_info = dw 0
        sh0_addralign = qw 0
        sh0_entsize = qw 0
        sh0 = sh0_name <> sh0_type <> sh0_flags <> sh0_addr <> sh0_offset <> sh0_size <> sh0_link <> sh0_info <> sh0_addralign <> sh0_entsize

        sh1_name = dw string_shstrtab
        sh1_type = dw 3  -- STRTAB
        sh1_flags = qw 0
        sh1_addr = qw 0
        sh1_offset = qw offset_shstrtab
        sh1_size = qw $ fromIntegral $ length strings
        sh1_link = dw 0
        sh1_info = dw 0
        sh1_addralign = qw 0
        sh1_entsize = qw 0
        sh1 = sh1_name <> sh1_type <> sh1_flags <> sh1_addr <> sh1_offset <> sh1_size <> sh1_link <> sh1_info <> sh1_addralign <> sh1_entsize

        sh2_name = dw string_rodata
        sh2_type = dw 1   -- PROGBITS
        sh2_flags = qw 2  -- ALLOC
        sh2_addr = p0_vaddr
        sh2_offset = p0_offset
        sh2_size = p0_filesz
        sh2_link = dw 0
        sh2_info = dw 0
        sh2_addralign = qw 4096
        sh2_entsize = qw 0
        sh2 = sh2_name <> sh2_type <> sh2_flags <> sh2_addr <> sh2_offset <> sh2_size <> sh2_link <> sh2_info <> sh2_addralign <> sh2_entsize

        sh3_name = dw string_text
        sh3_type = dw 1   -- PROGBITS
        sh3_flags = qw 6  -- ALLOC|EXECINSTR
        sh3_addr = p1_vaddr
        sh3_offset = p1_offset
        sh3_size = p1_filesz
        sh3_link = dw 0
        sh3_info = dw 0
        sh3_addralign = qw 4096
        sh3_entsize = qw 0
        sh3 = sh3_name <> sh3_type <> sh3_flags <> sh3_addr <> sh3_offset <> sh3_size <> sh3_link <> sh3_info <> sh3_addralign <> sh3_entsize
    in
        elf_header <> p0 <> p1 <> p2 <> pad <> lit' <> code <> shstrtab <> sh0 <> sh1 <> sh2 <> sh3

compile :: [Statement] -> Elf
compile ss =
    let
        ((),(env,lit,code,fix)) = runState (setup_stack >> compile_with ss) ([],mempty,mempty,[])
        code' = perform_fixups env code fix
    in
        make_elf lit code'

compile_test :: IO ()
compile_test = do
    a <- parseFromFile file "somecode.txt"
    case a of
        Left e -> print e
        Right ss -> withBinaryFile "output.elf" WriteMode (\h -> do
            hPutBuilder h (code_as_builder $ compile ss)
            putStrLn "written output.elf"
            )


