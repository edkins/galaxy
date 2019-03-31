module Compile where

import Parse (file,Statement(Assign,Exit,Print,PlainExpr,Write,Fn,Return,PrimitiveFn,SyscallFn,Loop,BreakIf))
import Parse (Expr(Literali8,Literalu8,Literalu64,LiteralListu8,Var,MethodCall,Le,Slice,Uninit))
import Parse (AsmDef(asm_prefix,asm_vex,asm_op,asm_w,asm_mmmmm,asm_plusr,asm_slash,asm_mr))
import Parse (AsmVex(Vex,Vex128,Vex256,Evex,Evex128,Evex256,Evex512,Unspecified))
import Parse (AsmPrefix(Optional66,Prefix66,PrefixF3,PrefixF2,NoPrefix))
import Parse (AsmM(M0F,M0F38,M0F3A,NoM), AsmW(W0,W1,WIG))
import Parse (Type(ByReg,ByRM,ByMem,Known,DoesNotReturn,Void,Uninitialized))
import Parse (PlainType(I8,U8,U16,U8Q,U8X,U8Y,U8Z,U8V,U16Q,U16X,U16Y,U16Z,U16V,I32,U64,Array))
import X86

import Debug.Trace (trace)
import Control.Monad.State (State,get,put,runState)
import Text.Parsec.String (parseFromFile)
import Text.Parsec.Error (ParseError)
import Data.ByteString.Builder
import qualified Data.ByteString.Lazy as L
import Data.List (sort)
import Data.Word (Word8)
import Data.Monoid ((<>))
import Data.Bits ((.&.))
import System.IO (withBinaryFile,IOMode (WriteMode))

data InstrTech = Old | Mmx | Sse | Avx | Avx2 deriving (Eq,Show)
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
    instr_plusr :: Bool,    -- whether the register operand gets added to the opcode
    instr_args :: Int,      -- argument count.
    instr_r :: InstrR,      -- set the ModR/M r value to this argument, return register or constant value. If RNone, no ModR/M byte.
    instr_rm :: InstrRM,    -- set the ModR/M rm value to this argument or return register.
    instr_vvvv :: InstrV,   -- set the VEX.vvvv value to this argument, or to 15 if not present
    instr_imbytes :: Int    -- number of bytes in the immediate value, or 0 if there isn't one. Immediate is always written last.
    } deriving (Eq,Show)
data Primitive = Primitive [(String,Type)] Type AsmInstr Bool deriving (Eq,Show)
data Syscall = Syscall [(String,Type)] [(String,Type)] Int deriving (Eq,Show)
data EnvThing = ERX Reg | ERY Reg | ERQ Reg | Label Int | Prim [Primitive] | Sys Syscall | Stack Int Type deriving (Eq,Show)
data EnvKey = EVar String | EUniform Word8 | ETemp deriving (Eq,Show)
type Env = [(EnvKey,EnvThing)]
type Literals = Code
type Elf = Code
data Fixup = JmpFixup Int String deriving (Eq,Show)
type Fixups = [Fixup]
data RegCombo = RegCombo Int [(Reg,Int)] deriving (Eq,Show)
data Result = ResR Reg | ResL Int | Linker String | Relative Int | ResM RegCombo deriving (Eq,Show)

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
want_tech (Old,_) = True
want_tech (Avx,_) = True
want_tech (_,_) = False

asm_widths :: AsmDef -> [(InstrTech,Int)]
asm_widths a =
    let
        old = (Old,64)
        mmx = (Mmx,64)
        sse = (Sse,128)
        x = (Avx,128)
        y = (Avx,256)
        x' = (Avx2,128)
        y' = (Avx2,256)
        z' = (Avx2,512)
    in filter want_tech (if asm_prefix a == NoPrefix then
            [old]
    else if asm_prefix a == Optional66 then
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

is_rm :: Type -> Bool
is_rm (ByRM _) = True
is_rm _ = False

asm_rm :: [Type] -> Type -> [Bool]
asm_rm args ret = if any is_rm (ret:args) then [False,True] else [False]

asm_widths_and_rm :: [Type] -> Type -> AsmDef -> [(InstrTech,Int,Bool)]
asm_widths_and_rm args ret a = [(tech,width,rm) | (tech,width) <- asm_widths a, rm <- asm_rm args ret]

translate_pp :: Int -> AsmPrefix -> Word8
translate_pp 64 Optional66 = 0
translate_pp _ Optional66 = 1
translate_pp _ Prefix66 = 1
translate_pp _ PrefixF3 = 2
translate_pp _ PrefixF2 = 3
translate_pp _ NoPrefix = 0

translate_mmmmm :: AsmM -> Word8
translate_mmmmm NoM = 0
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
        Known I8 -> (1, init xs)
        Known U16 -> (2, init xs)
        Known I32 -> (4, init xs)
        Known U64 -> (8, init xs)
        Known t -> error ("Unknown immediate type: " ++ show t)
        _ -> (0, xs)

instr_r_rm_v :: Bool -> [Type] -> Type -> Maybe Word8 -> Bool -> (InstrR,InstrRM,InstrV)
instr_r_rm_v False [_] _ (Just n) False = (RConst n, RMDest, NoV)     -- e.g. psslw(imm)
instr_r_rm_v True  [_] _ (Just n) False = (RConst n, RMArg 0, VRet)   -- e.g. vpsllw(imm)
instr_r_rm_v False [_] _ Nothing False = (RRet, RMArg 0, NoV)   -- e.g. pabsb
instr_r_rm_v True  [_] _ Nothing False = (RRet, RMArg 0, V15)   -- e.g. vpbroadcastb
instr_r_rm_v True  [_] _ Nothing True = (RArg 0, RMRet, V15)    -- e.g. movdqa_mr
instr_r_rm_v False [ByReg _,ByRM _] _ Nothing False = (RDest, RMArg 1, NoV)     -- e.g. paddb
instr_r_rm_v True  [ByReg _,ByRM _] _ Nothing False = (RRet, RMArg 1, VArg 0)   -- e.g. vpaddb
instr_r_rm_v False [ByRM _,ByReg _] _ Nothing True = (RArg 1, RMArg 0, NoV)     -- e.g. cmp
instr_r_rm_v False [] DoesNotReturn Nothing False = (RNone, RMNone, NoV)    -- e.g. jmp
instr_r_rm_v False [] Void Nothing False = (RNone, RMNone, NoV)    -- e.g. jge
instr_r_rm_v False [] (ByReg _) Nothing False = (RRet, RMNone, NoV)    -- e.g. mov(imm)
instr_r_rm_v avx args ret slash mr = error ("Need instr_r_rm " ++ show avx ++ " " ++ show args ++ " " ++ show ret ++ " " ++ show slash ++ " " ++ show mr)

translate_asm_width :: [Type] -> Type -> AsmDef -> (InstrTech,Int,Bool) -> (AsmInstr,Bool)
translate_asm_width args ret a (tech,width,rm_is_r) =
    let
        (imbytes, args') = translate_imm args
        is_avx = tech /= Old && tech /= Mmx && tech /= Sse
        (r, rm, vvvv) = instr_r_rm_v is_avx args' ret (asm_slash a) (asm_mr a)
    in (AsmInstr {
        instr_width = width,
        instr_tech = tech,
        instr_pp = translate_pp width (asm_prefix a),
        instr_mmmmm = translate_mmmmm (asm_mmmmm a),
        instr_w = (if asm_w a == W1 then 1 else 0),
        instr_op = asm_op a,
        instr_plusr = asm_plusr a,
        instr_args = length args,
        instr_r = r,
        instr_rm = rm,
        instr_vvvv = vvvv,
        instr_imbytes = imbytes
        },rm_is_r)

translate_asm :: [Type] -> Type -> AsmDef -> [(AsmInstr,Bool)]
translate_asm args ret a = map (translate_asm_width args ret a) (asm_widths_and_rm args ret a)

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

fresh_gpr :: EnvKey -> Compilation Reg
fresh_gpr x = do
    (env,lit,code,fix) <- get
    let result = fresh_gpr_from 0 env
    put (env ++ [(x,ERQ result)],lit,code,fix)
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

fresh_temp_gpr :: Compilation Reg
fresh_temp_gpr = fresh_gpr ETemp

find_xmm_maybe :: String -> Compilation (Maybe (Reg,Type))
find_xmm_maybe x = do
    mb <- env_lookup x
    case mb of
        Nothing -> return Nothing
        Just (ERX (Xmm r)) -> return (Just (Xmm r,ByReg U8X))
        Just (ERY (Xmm r)) -> return (Just (Xmm r,ByReg U8Y))
        Just _ -> error ("Found " ++ x ++ " but it wasn't an xmm regiser")

find_xmm :: String -> Compilation (Reg,Type)
find_xmm x = do
    mb <- env_lookup x
    case mb of
        Nothing -> error ("Could not find xmm register for " ++ x)
        Just (ERX (Xmm r)) -> return (Xmm r,ByReg U8X)
        Just (ERY (Xmm r)) -> return (Xmm r,ByReg U8Y)
        Just _ -> error ("Found " ++ x ++ " but it wasn't an xmm regiser")

find_reg :: String -> Compilation (Reg,Type)
find_reg x = do
    mb <- env_lookup x
    case mb of
        Nothing -> error ("Could not find xmm register for " ++ x)
        Just (ERX (Xmm r)) -> return (Xmm r, ByReg U8X)
        Just (ERY (Xmm r)) -> return (Xmm r, ByReg U8Y)
        Just (ERQ (Gpr r)) -> return (Gpr r, ByReg U64)
        Just thing -> error ("Found " ++ x ++ " but it wasn't a regiser, instead " ++ show thing)

find_gpr :: String -> Compilation (Reg,Type)
find_gpr x = do
    mb <- env_lookup x
    case mb of
        Nothing -> error ("Could not find gpr register for " ++ x)
        Just (ERQ (Gpr r)) -> return (Gpr r,ByReg U64)
        Just _ -> error ("Found " ++ x ++ " but it wasn't a gpr regiser")

find_gpr_maybe :: String -> Compilation (Maybe(Reg,Type))
find_gpr_maybe x = do
    mb <- env_lookup x
    case mb of
        Nothing -> return Nothing
        Just (ERQ (Gpr r)) -> return $ Just(Gpr r,ByReg U64)
        Just _ -> error ("Found " ++ x ++ " but it wasn't a gpr regiser")

find_mem :: String -> Compilation (RegCombo,Type)
find_mem x = do
    mb <- env_lookup x
    case mb of
        Nothing -> error ("Could not find mem for " ++ x)
        Just (Stack n t) -> return (RegCombo n [(_sp,1)], t)
        Just _ -> error ("Found " ++ x ++ " but it wasn't a mem thing")

find_or_emit_uniform :: Word8 -> Compilation Reg
find_or_emit_uniform n = do
    mb <- env_lookup_uniform n
    case mb of
        Just r -> return r
        Nothing -> do
            let name = show n
            if use_evex then do
                xreg <- fresh_gpr (EVar name)
                yreg <- fresh_ymm (EVar name)
                emit (old_oi mov_oi8 xreg (fromIntegral n))
                emit (evex256_rm evpbroadcastb_gpr_rm yreg (R xreg))
                return yreg
            else do
                addr <- alloc_literal_aligned 1 [n]
                yreg <- fresh_ymm (EVar name)
                emit (vex256_rm vpbroadcastb_rm yreg (AbsMem addr))
                return yreg

mem_offset' :: [(Reg,Int)] -> Reg -> Int -> [(Reg,Int)]
mem_offset' [] r n = [(r,n)]
mem_offset' ((r',n'):rns) r n
    | r' == r && n' + n == 0 = rns
    | r' == r = (r', n' + n) : rns
    | otherwise = (r',n'):mem_offset' rns r n

mem_offset :: RegCombo -> Reg -> Int -> RegCombo
mem_offset (RegCombo n rc) reg multiplier = RegCombo n (mem_offset' rc reg multiplier)

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

insert_label_here :: String -> Compilation ()
insert_label_here x = do
    (env,lit,code,fix) <- get
    let env' = [(EVar x,Label (clength code))] ++ env
    put (env',lit,code,fix)

thing_tweak_type :: Type -> EnvThing -> EnvThing
thing_tweak_type (ByReg U8X) (ERX reg) = ERX reg
thing_tweak_type (ByReg U8X) (ERY reg) = ERX reg
thing_tweak_type (ByReg U8Y) (ERX reg) = ERY reg
thing_tweak_type (ByReg U8Y) (ERY reg) = ERY reg
thing_tweak_type (ByReg U64) (ERQ reg) = ERQ reg
thing_tweak_type a b = error ("Need to thing_tweak_type " ++ show a ++ " and " ++ show b)

env_tweak_type :: Type -> String -> Env -> Env
env_tweak_type_ x [] = error ("env_tweak_type: variable " ++ x ++ " not found")
env_tweak_type width x ((y,thing):env)
    | EVar x == y = (y,thing_tweak_type width thing):env
    | otherwise = (y,thing) : env_tweak_type width x env

tweak_type :: Type -> String -> Compilation ()
tweak_type width x = do
    (env,lit,code,fix) <- get
    let env' = env_tweak_type width x env
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

env_insert :: EnvKey -> EnvThing -> Env -> Env
env_insert x thing env =
    case lookup x env of
        Nothing -> (x,thing):env
        Just y -> error ("env_insert: variable " ++ show x ++ " already in environment")

insert_env :: EnvKey -> EnvThing -> Compilation ()
insert_env x thing = do
    (env,lit,code,fix) <- get
    let env' = env_insert x thing env
    put (env',lit,code,fix)

map_type :: Bool -> (PlainType -> PlainType) -> Type -> Type
map_type _ f (ByReg t) = ByReg (f t)
map_type _ f (ByMem t) = ByMem (f t)
map_type True f (ByRM t) = ByReg (f t)
map_type False f (ByRM t) = ByMem (f t)
map_type _ f (Known t) = Known (f t)

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

specialize_type :: AsmInstr -> Bool -> Type -> Type
specialize_type a rm_r = map_type rm_r (specialize_plain (instr_width a))

specialize_args :: AsmInstr -> Bool -> [(String,Type)] -> [(String,Type)]
specialize_args a rm_r args = map (\(x,t) -> (x, specialize_type a rm_r t)) args

define_primitive_function :: String -> [(String,Type)] -> Type -> [(AsmInstr,Bool)] -> Bool -> Compilation ()
define_primitive_function f args ret instrs incidental = do
    (env,lit,code,fix) <- get
    let newprims = [Primitive (specialize_args a rm_r args) (specialize_type a rm_r ret) a incidental | (a,rm_r) <- instrs]
    let env' = (case lookup (EVar f) env of
            Nothing -> (EVar f, Prim newprims) : env
            Just (Prim oldprims) -> env_replace (EVar f) (Prim (newprims++oldprims)) env)
    put (env',lit,code,fix)

define_syscall_function :: String -> [(String,Type)] -> [(String,Type)] -> Int -> Compilation ()
define_syscall_function f args ret n = do
    (env,lit,code,fix) <- get
    let sys = Syscall args ret n
    let env' = (EVar f, Sys sys) : env
    put (env',lit,code,fix)

---------------------------------
{-
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
-}
get_constant_u8 :: Expr -> Word8
get_constant_u8 (Literalu8 n) = n
get_constant_u8 e = error ("Cannot interpret expression as constant u8: " ++ show e)

unwrap_type :: Type -> PlainType
unwrap_type (ByReg t) = t
unwrap_type (ByMem t) = t
unwrap_type (ByRM t) = t
unwrap_type (Known t) = t

arg_type_matches :: Type -> Type -> Bool
arg_type_matches (ByReg t) (ByRM t') = t == t'
arg_type_matches (ByMem t) (ByRM t') = t == t'
arg_type_matches (Known U8) (ByReg U8X) = True  -- auto-broadcasts and auto-regifies
arg_type_matches (Known U8) (ByRM U8X) = True   -- auto-broadcasts and auto-regifies
arg_type_matches (Known U8) (ByReg U8Y) = True  -- auto-broadcasts and auto-regifies
arg_type_matches (Known U8) (ByRM U8Y) = True   -- auto-broadcasts and auto-regifies
arg_type_matches t t' = t == t'

arg_matches :: (Result,Type) -> (String,Type) -> Bool
arg_matches (_,t) (_,t') = arg_type_matches t t'

{-
arg_matches :: (Result,Type) -> (String,Type) -> Bool
arg_matches (ResR _,ByReg w) (_,ByRM t) = t == w
arg_matches (ResM _,ByMem w) (_,ByRM t) = t == w
arg_matches (ResR _,w) (_,t) = t == w
arg_matches (ResM _,w) (_,t) = t == w
arg_matches (ResL _,Known U8) (_,Known U8) = True
arg_matches (ResL _,Known U64) (_,Known U64) = True
arg_matches (ResL _,Known I32) (_,Known I32) = True
arg_matches (ResL _,Known U8) (_,ByReg U8X) = True   -- auto-broadcasts and auto-regifies
arg_matches (ResL _,Known U8) (_,ByRM U8X) = True    --
arg_matches (ResL _,Known U8) (_,ByReg U8Y) = True   --
arg_matches (ResL _,Known U8) (_,ByRM U8Y) = True    --
arg_matches _ _ = False
-}

find_or_emit_uniform_result :: Int -> Compilation Result
find_or_emit_uniform_result n = do
    r <- find_or_emit_uniform (fromIntegral n)
    return (ResR r)

-- assumes has already passed arg_matches
autoconvert :: ((Result,Type),(String,Type)) -> Compilation Result
autoconvert ((ResR r,_),(_,ByReg _)) = return (ResR r)
autoconvert ((ResL n,Known U8),(_,Known U8)) = return (ResL n)
autoconvert ((ResL n,Known I8),(_,Known I8)) = return (ResL n)
autoconvert ((ResL n,Known U8),(_,ByReg U8X)) = find_or_emit_uniform_result n
autoconvert ((ResL n,Known U8),(_,ByReg U8Y)) = find_or_emit_uniform_result n
autoconvert (a,b) = error ("Need to autoconvert " ++ show a ++ " to " ++ show b)

prim_matches :: [(Result,Type)] -> Primitive -> Bool
prim_matches ws (Primitive args' _ _ _) = length ws == length args' && and (zipWith arg_matches ws args')

prim_matches_by_type :: [Type] -> Primitive -> Bool
prim_matches_by_type ts (Primitive args' _ _ _) = length ts == length args' && and (zipWith arg_type_matches ts (map snd args'))

lookup_prim :: String -> [(Result,Type)] -> Compilation Primitive
lookup_prim f ws = do
    (env,_,_,_) <- get
    case lookup (EVar f) env of
        Just (Prim candidates) ->
            case filter (prim_matches ws) candidates of
                [x] -> return x
                [] -> error ("No candidates matched for primitive fn " ++ f ++ show ws ++ ". Considered:\n" ++ concat (map (\(Primitive args _ _ _)->show args ++ "\n") candidates))
                er -> error ("Multiple candidates matched for primitive fn " ++ f ++ show ws ++ ":\n" ++ concat (map (\(Primitive args _ a _)->show args ++ " " ++ show (instr_tech a) ++ "\n") er))
        Nothing -> error ("Could not find primitive fn " ++ f ++ " in " ++ show (map fst env))

lookup_prim_by_type :: String -> [Type] -> Compilation Primitive
lookup_prim_by_type f ws = do
    (env,_,_,_) <- get
    case lookup (EVar f) env of
        Just (Prim candidates) ->
            case filter (prim_matches_by_type ws) candidates of
                [x] -> return x
                [] -> error ("No candidates matched by type for primitive fn " ++ f ++ show ws ++ ". Considered:\n" ++ concat (map (\(Primitive args _ _ _)->show args ++ "\n") candidates))
                er -> error ("Multiple candidates matched for primitive fn " ++ f ++ show ws ++ ":\n" ++ concat (map (\(Primitive args _ a _)->show args ++ " " ++ show (instr_tech a) ++ "\n") er))
        Nothing -> error ("Could not find primitive fn " ++ f ++ " in " ++ show (map fst env))

vex_width_code :: Int -> Word8
vex_width_code 128 = 0
vex_width_code 256 = 1
vex_width_code 512 = 2

insist_reg :: Result -> Reg
insist_reg (ResR r) = r
insist_reg x = error ("insist_reg: " ++ show x)

insist_rm :: Result -> RM
insist_rm (ResR r) = R r
insist_rm (ResM (RegCombo disp [])) = AbsMem disp
insist_rm (ResM (RegCombo disp [(r,1)]))
    | r == Gpr 4 = SibMem 1 NoReg r disp    -- RSP not encodable in ModRM byte. Need to fall back to SIB byte.
    | otherwise = RegMem r disp
insist_rm (ResM (RegCombo disp [(r,n)])) = SibMem n r NoReg disp
insist_rm (ResM (RegCombo disp [(r,1),(r',1)]))
    | r == Gpr 4 && r' /= Gpr 4 = SibMem 1 r' r disp    -- RSP cannot be used as scale register
    | r /= Gpr 4 = SibMem 1 r r' disp
insist_rm (ResM (RegCombo disp [(r,1),(r',n)]))
    | n == 1 || n == 2 || n == 4 || n == 8 =
        if r' /= Gpr 4 then
            SibMem n r' r disp
        else
            error "Cannot use RSP as scale register"
    | otherwise = error ("Cannot scale " ++ show n)
insist_rm (ResM (RegCombo disp [(r',n),(r,1)]))
    | n == 1 || n == 2 || n == 4 || n == 8 =
        if r' /= Gpr 4 then
            SibMem n r' r disp
        else
            error "Cannot use RSP as scale register"
    | otherwise = error ("Cannot scale " ++ show n)
insist_rm rc = error ("Cannot encode reg combo " ++ show rc)

insist_lit :: Result -> Int
insist_lit (ResL n) = n
insist_lit x = error ("insist_lit: " ++ show x)

lookup_instr_r :: InstrR -> [Result] -> Result -> Reg
lookup_instr_r (RConst n) _ _ = Slash n
lookup_instr_r (RArg i) args _ = case args!!i of
    ResR r -> r
    z -> error ("lookup_instr_r (RArg " ++ show i ++ "), expected reg got " ++ show z)
lookup_instr_r RRet _ ret = case ret of
    ResR r -> r
    z -> error ("lookup_instr_r RRet, expected reg got " ++ show z)
lookup_instr_r RNone _ _ = NoReg
lookup_instr_r RDest args _ = case head args of
    ResR r -> r
    z -> error ("lookup_instr_r RDest, expected reg got " ++ show z)

lookup_instr_rm :: InstrRM -> [Result] -> Result -> RM
lookup_instr_rm (RMArg i) args _ = insist_rm (args !! i)
lookup_instr_rm RMRet _ ret = insist_rm ret
lookup_instr_rm RMNone _ _ = NoRM
lookup_instr_rm RMDest args _ = insist_rm (args !! 0)

lookup_instr_v :: InstrV -> [Result] -> Result -> Reg
lookup_instr_v (VArg i) args _ = insist_reg (args !! i)
lookup_instr_v VRet _ ret = insist_reg ret
lookup_instr_v V15 _ ret = NoReg

lookup_instr_imm :: Int -> [Result] -> Code
lookup_instr_imm 0 _ = mempty
lookup_instr_imm imbytes args = int_as_n_bytes imbytes $ insist_lit $ last args

reg_mod8 :: Reg -> Word8
reg_mod8 (Gpr r) = r .&. 7
reg_mod8 x = error ("reg_mod8 " ++ show x)

emit_maybe_jmp :: [Result] -> (Int -> Code) -> Compilation ()
emit_maybe_jmp args f = do
    pos <- instr_pos
    case last args of
        (ResL n) -> emit (f n)
        (Linker x) -> emit_jmp x f
        (Relative n) -> do
            let length_of_instr = clength (f 0)
            emit (f ((n - pos - length_of_instr) .&. 0xffffffff))

emit_prim :: AsmInstr -> Result -> [Result] -> Compilation ()
emit_prim a ret args =
    if instr_tech a == Old && instr_plusr a then
        emit (old_misc_no_modrm
            (instr_w a)
            (instr_pp a)
            (instr_mmmmm a)
            (instr_op a + reg_mod8 (lookup_instr_r (instr_r a) args ret))
            (lookup_instr_imm (instr_imbytes a) args))
    else if instr_tech a == Old && instr_r a == RNone && instr_rm a == RMNone then
        emit_maybe_jmp args (\imm ->
            old_misc_no_modrm
            (instr_w a)
            (instr_pp a)
            (instr_mmmmm a)
            (instr_op a)
            (int_as_n_bytes (instr_imbytes a) imm))
    else if instr_tech a == Old then
        emit (old_misc
            (instr_w a)
            (instr_pp a)
            (instr_mmmmm a)
            (instr_op a)
            (lookup_instr_r (instr_r a) args ret)
            (lookup_instr_rm (instr_rm a) args ret)
            (lookup_instr_imm (instr_imbytes a) args))
    else if instr_tech a == Avx then      -- vex_misc w pp m_mmmm l op r rv rm imm
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

-- This assumes the first argument is also the destination
emit_incidental_prim :: String -> [(Result,Type)] -> Compilation ()
emit_incidental_prim f args = do
    Primitive formals rt asm incidental <- lookup_prim f args
    if incidental then do
        let ret = fst (head args)
        emit_prim asm ret (map fst args)
    else error ("Primitive " ++ f ++ " was not declared with incidental")

-- The first argument is the destination, and is not also a source
emit_incidental_prim_mov :: String -> [(Result,Type)] -> Compilation ()
emit_incidental_prim_mov f args = do
    Primitive formals rt asm incidental <- lookup_prim f (tail args)
    if incidental then do
        let ret = fst (head args)
        emit_prim asm ret (map fst (tail args))
    else error ("Primitive " ++ f ++ " was not declared with incidental")

data FunctionType = FPrimitive | FSyscall

get_function_type :: String -> Compilation FunctionType
get_function_type f = do
    (env,_,_,_) <- get
    case lookup (EVar f) env of
        Just (Prim _) -> return FPrimitive
        Just (Sys _) -> return FSyscall
        _ -> error ("Cannot identify function type: " ++ f)

lookup_syscall :: String -> Compilation Syscall
lookup_syscall f = do
    (env,_,_,_) <- get
    case lookup (EVar f) env of
        Just (Sys s) -> return s
        _ -> error ("Not a syscall: " ++ f)

is_array_of :: Type -> PlainType -> Bool
is_array_of (ByMem (Array t _)) (t') = t == t'
is_array_of _ _ = False

env_stack_shift :: Int -> Env -> Env
env_stack_shift _ [] = []
env_stack_shift n ((x,Stack i t):env) = (x,Stack (i+n) t):env_stack_shift n env
env_stack_shift n ((x,thing):env) = (x,thing):env_stack_shift n env

stack_shift :: Int -> Compilation ()
stack_shift n = do
    (env,lit,code,fix) <- get
    let env' = env_stack_shift n env
    put (env',lit,code,fix)

---------------------------------

compile_expr_to :: Reg -> Expr -> Compilation Type
compile_expr_to xreg (Var y) = do
    (yreg,yw) <- find_reg y
    if xreg == yreg then do
        return yw
    else if yw == ByReg U8X then do
        emit (vex128_rm vmovdqa_mr xreg (R yreg))
        return yw
    else if yw == ByReg U8Y then do
        emit (vex256_rm vmovdqa_mr xreg (R yreg))
        return yw
    else if yw == ByReg U64 then do
        emit_incidental_prim_mov "mov" [(ResR xreg,ByReg U64),(ResR yreg,yw)]
        return yw
    else
        error ("Cannot move " ++ show yw)
compile_expr_to xreg (Literalu64 y) = do
    emit_incidental_prim_mov "mov" [(ResR xreg,ByReg U64),(ResL $ fromIntegral y,Known U64)]
    return (ByReg U64)
compile_expr_to xreg (LiteralListu8 ls) =
    if length ls == 16 then
        do
            addr <- alloc_literal_aligned 16 ls
            emit (vex128_rm vmovdqa_rm xreg (AbsMem addr))
            return (ByReg U8X)
    else
        error "Expected exactly 16 bytes"

compile_expr_to xreg (MethodCall ye f arges) = do
    ftype <- get_function_type f
    case ftype of
        FPrimitive -> do
            args <- mapM (compile_expr Nothing) (ye:arges)
            argts <- mapM expr_type (ye:arges)
            Primitive formals rt asm _ <- lookup_prim_by_type f argts
            ress <- mapM autoconvert (zip args formals)
            emit_prim asm (ResR xreg) ress
            return rt
        FSyscall -> do
            Syscall formals rts n <- lookup_syscall f
            let rt = snd (rts !! 0)
            compile_syscall_args n (ye:arges) (map snd formals)
            emit (sse_zo syscall_zo)
            if rt == Void || rt == DoesNotReturn then do
                return rt
            else if rt == ByReg U64 then do
                if xreg /= _ax then
                    emit_incidental_prim_mov "mov" [(ResR xreg,ByReg U64),(ResR _ax,rt)]
                else
                    return ()
                return rt
            else
                error ("Not handling syscall return type: " ++ show rt)

compile_expr_to xreg (Slice (Var buf) i (Literalu8 32)) = do
    (bmem,bt) <- find_mem buf
    (ireg,it) <- compile_expr (Just (ByReg U64)) i
    if bt `is_array_of` U8 then do
        let addr = mem_offset bmem (insist_reg ireg) 1
        emit_incidental_prim_mov "movdqu" [(ResR xreg,ByReg U8Y),(ResM addr,ByMem U8Y)]
        return (ByReg U8Y)
    else
        error ("Cannot currently subscript type " ++ show bt)

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
compile_expr_to _ e = error ("currently unable to compile expression to reg " ++ show e)

compile_expr :: Maybe Type -> Expr -> Compilation (Result,Type)
compile_expr _ (Var x) = do
    (r,w) <- find_reg x
    return (ResR r,w)
compile_expr (Just hint) (Literalu8 l) = do
    reg <- find_or_emit_uniform (fromIntegral l)
    return (ResR reg, hint)
compile_expr Nothing (Literalu8 n) = return (ResL (fromIntegral n),Known U8)
compile_expr Nothing (Literali8 n) = return (ResL (fromIntegral n),Known I8)
compile_expr _ (Uninit (Array U8 (Literalu64 size'))) = do
    let size = fromIntegral size'
    emit_incidental_prim "subq" [(ResR _sp,ByReg U64),(ResL $ fromIntegral size,Known I32)]
    stack_shift size
    return (ResM (RegCombo 0 [(_sp,1)]), ByMem (Array U8 (Literalu64 size')))
compile_expr t e = do
    t' <- case t of
        Nothing -> expr_type e
        Just t' -> return t'
    xreg <- (if t' == ByReg U8Y then
        fresh_temp_ymm
    else if t' == ByReg U8X then
        fresh_temp_ymm   -- ?
    else if t' == ByReg U64 || t' == Known U64 then
        fresh_temp_gpr
    else
        error ("Currently can't create temporary for " ++ show t))
    width <- compile_expr_to xreg e
    return (ResR xreg,width)

compile_expr_to_mem :: Type -> RegCombo -> Expr -> Compilation ()
compile_expr_to_mem t rc (Var x) = do
    (r,t') <- find_xmm x
    if t `is_array_of` U8 && t' == ByReg U8Y then
        emit_incidental_prim_mov "movdqu_mr" [(ResM rc,t),(ResR r,t')]
    else
        error ("Currently can't move type " ++ show t' ++ " to " ++ show t)

compile_expr_borrow :: Reg -> Expr -> Compilation ()
compile_expr_borrow reg (Var x) = do
    (rc,t) <- find_mem x
    emit_incidental_prim_mov "lea" [(ResR reg,ByMem U64),(ResM rc,ByMem U64)] -- TODO: we mutate the type here to &U64

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

compile_syscall_arg :: Reg -> Type -> Expr -> Compilation ()
compile_syscall_arg reg (ByReg _) arg = compile_expr_to reg arg >> return ()
compile_syscall_arg reg (ByMem _) arg = compile_expr_borrow reg arg
compile_syscall_arg reg (Uninitialized _) arg = compile_expr_borrow reg arg
compile_syscall_arg _ t arg = error ("compile_syscall_arg for " ++ show t)

compile_args :: [Expr] -> Compilation ()
compile_args args = do
    let indices = [0..fromIntegral (length args)-1]
    reserved <- reserve_for_args $ map Xmm indices
    mapM_ (\(arg,i) -> compile_expr_to (Xmm i) arg) $ zip args indices

compile_syscall_args :: Int -> [Expr] -> [Type] -> Compilation ()
compile_syscall_args n args types = do
    let regs = take (length args) [_di,_si,_dx,Gpr 10,Gpr 8,Gpr 9]
    reserved <- reserve_for_args (_ax : regs)
    mapM_ (\(arg,typ,reg) -> compile_syscall_arg reg typ arg) $ zip3 args types regs
    emit_incidental_prim_mov "mov" [(ResR _ax,ByReg U64),(ResL n,Known U64)]

instr_pos :: Compilation Int
instr_pos = do
    (_,_,code,_) <- get
    return (clength code)

branch_back :: Int -> Compilation ()
branch_back pos = do
    emit_incidental_prim "jmp" [(Relative pos, Known I32)]

reg_combo_to_stack_thing :: RegCombo -> Type -> EnvThing
reg_combo_to_stack_thing (RegCombo n [(reg,1)]) t
    | reg == _sp = Stack n t

expr_type :: Expr -> Compilation Type
expr_type (Literali8 _) = return (Known I8)
expr_type (Literalu8 _) = return (Known U8)
expr_type (Literalu64 _) = return (Known U64)
expr_type (MethodCall obje f arges) = do
    thing <- env_lookup f
    case thing of
        Just (Sys (Syscall _ ((_,rt):_) _)) -> return rt
        Just (Prim prims) -> do
            objt <- expr_type obje
            argts <- mapM expr_type arges
            Primitive _ rt _ _ <- lookup_prim_by_type f (objt:argts)
            return rt
        _ -> error ("Can't yet determine type of env thing " ++ show f ++ " - " ++ show thing)
expr_type (Slice _ _ (Literalu8 32)) = return (ByReg U8Y)
expr_type (Uninit t) = return (Uninitialized t)
expr_type (Var x) = do
    thing <- env_lookup x
    case thing of
        Nothing -> error ("Variable " ++ x ++ " is not in the environment")
        Just (ERX _) -> return (ByReg U8X)
        Just (ERY _) -> return (ByReg U8Y)
        Just (ERQ _) -> return (ByReg U64)
expr_type e = error ("Can't yet determine type of " ++ show e)

find_reg_appropriate_for :: Type -> String -> Compilation (Maybe (Reg,Type))
find_reg_appropriate_for (Known U64) x = find_gpr_maybe x
find_reg_appropriate_for (ByReg U64) x = find_gpr_maybe x
find_reg_appropriate_for (ByReg U8X) x = find_xmm_maybe x
find_reg_appropriate_for (ByReg U8Y) x = find_xmm_maybe x
find_reg_appropriate_for (Uninitialized _) x = find_gpr_maybe x
find_reg_appropriate_for t _ = error ("Need to find register appropriate for " ++ show t)

compile_statement :: Statement -> Compilation ()
compile_statement (Assign [Var x] e) = do
    exprt <- expr_type e
    o <- find_reg_appropriate_for exprt x
    case o of
        Just (xreg,t') -> do
            t <- compile_expr_to xreg e
            discard_temps
            tweak_type t x
        Nothing -> do
            (xres,t) <- compile_expr (Just exprt) e
            case (xres,t) of
                (ResR reg,ByReg U8X) -> insert_env (EVar x) (ERX reg)
                (ResR reg,ByReg U8Y) -> insert_env (EVar x) (ERY reg)
                (ResR (Gpr r),ByReg U64) -> insert_env (EVar x) (ERQ (Gpr r))
                (ResM rc,ByMem t) -> insert_env (EVar x) (reg_combo_to_stack_thing rc (ByMem t))
                (a,b) -> error ("Not sure how to insert into environment: " ++ show (a,b) ++ " (type was " ++ show exprt ++ ")")

compile_statement (Assign [Slice (Var x) (Var i) (Literalu8 32)] e) = do
    (xmem,xt) <- find_mem x
    (ireg,it) <- find_gpr i
    if xt `is_array_of` U8 && it == ByReg U64 then do
       let xmem_offset = mem_offset xmem ireg 1
       compile_expr_to_mem xt xmem_offset e
       discard_temps
    else
       error ("Slice assignment currently only supported for &u8[u64] not " ++ show xt ++ "[" ++ show it ++ "]")
compile_statement (Assign [Var x,Var y] e) = do
    compile_statement (Assign [Var x] e)
    -- TODO: handle this properly
compile_statement (Exit (Literalu8 l)) = do
    emit (old_oi mov_oi64 _di (fromIntegral l))   -- Pad l to 8 bytes, move into rdi for first argument to syscall
    emit (old_oi mov_oi64 _ax 60)                 -- syscall 60 is exit
    emit (sse_zo syscall_zo)
--compile_statement (Call f args) = do
--    compile_args args
--    emit_jmp f (old_i call_i32)
compile_statement (Fn f args) = do
    start_new_function f args
{-
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
-}
compile_statement Return = do
    emit (old_zo ret_zo)
compile_statement (PrimitiveFn f args ret asm incidental) = do
    let argtypes = map snd args
    let instrs = translate_asm argtypes ret asm
    define_primitive_function f args ret instrs incidental
compile_statement (SyscallFn f args rets n) =
    define_syscall_function f args rets n
compile_statement (PlainExpr e) = do
    compile_expr_to NoReg e
    return ()
compile_statement (Loop ss) = do
    pos0 <- instr_pos
    mapM_ compile_statement ss
    branch_back pos0
    insert_label_here "loopend"
compile_statement (BreakIf (Le xe ye)) = do
    (xres,xt) <- compile_expr Nothing xe
    (yres,yt) <- compile_expr Nothing ye
    if xt == ByReg U64 && yt == ByReg U64 then do
        emit_incidental_prim "cmp" [(xres,xt),(yres,yt)]
        emit_incidental_prim "jbe" [(Linker "loopend",Known I32)]
    else
        error ("currently unable to compare " ++ show xt ++ " and " ++ show yt)
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


