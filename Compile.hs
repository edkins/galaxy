module Compile where

import Parse (file,Statement(Assign,Exit,Print,Call,Write,Fn,Return),Expr(Literalu8,LiteralListu8,Var,MethodCall))
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

data EnvThing = ERX Reg | ERY Reg | ERQ Reg | Label Int deriving Eq
data Width = WidthX | WidthY | WidthQ deriving (Eq,Show)
type Env = [(String,EnvThing)]
type Literals = Code
type Elf = Code
data Fixup = JmpFixup Int String deriving (Eq,Show)
type Fixups = [Fixup]

type Compilation a = State (Env,Literals,Code,Fixups) a

-- Must compare address first
instance Ord Fixup where
    compare (JmpFixup a x) (JmpFixup b y) = compare (a,x) (b,y)

base_addr_for_literals = 0x08000000
stack_hi = 0x0a000000  -- it grows downwards
stack_lo = 0x09000000

use_evex = False

emit :: Code -> Compilation ()
emit code' = do
    (env,lit,code,fix) <- get
    put (env, lit, code <> code', fix)

emit_jmp :: String -> (Int -> Code) -> Compilation ()
emit_jmp label codef = do
    (env,lit,code,fix) <- get
    case lookup label env of
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
env_contains_uniform ((x,ERY r):e) n = if x==show n then Just r else env_contains_uniform e n
env_contains_uniform ((x,_):e) n = env_contains_uniform e n

fresh_xmm_from :: Word8 -> Env -> Reg
fresh_xmm_from n env =
    if env_contains_reg env (Xmm n) then
        fresh_xmm_from (n+1) env
    else
        Xmm n

fresh_gpr_from :: Word8 -> Env -> Reg
fresh_gpr_from n env =
    if env_contains_reg env (Gpr n) then
        fresh_gpr_from (n+1) env
    else
        Gpr n

fresh_ymm :: String -> Compilation Reg
fresh_ymm x = do
    (env,lit,code,fix) <- get
    let result = fresh_xmm_from 0 env
    put (env ++ [(x,ERY result)],lit,code,fix)
    return result

fresh_gpr :: String -> Compilation Reg
fresh_gpr x = do
    (env,lit,code,fix) <- get
    let result = fresh_gpr_from 0 env
    put (env ++ [(x,ERQ result)],lit,code,fix)
    return result

env_lookup :: String -> Compilation (Maybe EnvThing)
env_lookup x = do
    (env,_,_,_) <- get
    return $ lookup x env

env_lookup_uniform :: Word8 -> Compilation (Maybe Reg)
env_lookup_uniform n = do
    (env,_,_,_) <- get
    return (env_contains_uniform env n)

fresh_temp_ymm :: Compilation Reg
fresh_temp_ymm = fresh_ymm "(temp)"

find_or_fresh_xmm :: String -> Compilation Reg
find_or_fresh_xmm x = do
    mb <- env_lookup x
    case mb of
        Nothing -> fresh_ymm x
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
                yreg <- fresh_ymm name
                emit (old_oi mov_oi8 xreg (fromIntegral n))
                emit (evex256_rm evpbroadcastb_gpr_rm yreg (R xreg))
                return yreg
            else do
                addr <- alloc_literal_aligned 1 [n]
                yreg <- fresh_ymm name
                emit (vex256_rm vpbroadcastb_rm yreg (AbsMem addr))
                return yreg

args_to_env :: Word8 -> [String] -> Env
args_to_env _ [] = []
args_to_env n (x:xs) = (x, ERX (Xmm n)) : args_to_env (n+1) xs

is_global :: (String,EnvThing) -> Bool
is_global (_,Label _) = True
is_global _ = False

start_new_function :: String -> [String] -> Compilation ()
start_new_function f args = do
    (env,lit,code,fix) <- get
    let env' = args_to_env 0 args ++ [(f,Label (clength code))] ++ filter is_global env
    put (env',lit,code,fix)

thing_tweak_width :: Width -> EnvThing -> EnvThing
thing_tweak_width WidthX (ERX reg) = ERX reg
thing_tweak_width WidthX (ERY reg) = ERX reg
thing_tweak_width WidthY (ERX reg) = ERY reg
thing_tweak_width WidthY (ERY reg) = ERY reg

env_tweak_width :: Width -> String -> Env -> Env
env_tweak_width _ x [] = error ("env_tweak_width: variable " ++ x ++ " not found")
env_tweak_width width x ((y,thing):env)
    | x == y = (y,thing_tweak_width width thing):env
    | otherwise = (y,thing) : env_tweak_width width x env

tweak_width :: Width -> String -> Compilation ()
tweak_width width x = do
    (env,lit,code,fix) <- get
    let env' = env_tweak_width width x env
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
compile_expr_to xreg (MethodCall ye "zxbw" []) = do
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

compile_expr_to _ e = error ("currently unable to compile expression " ++ show e)

compile_expr :: Maybe Width -> Expr -> Compilation (Reg,Width)
compile_expr _ (Var x) = find_xmm x
compile_expr (Just hint) (Literalu8 l) = do
    reg <- find_or_emit_uniform (fromIntegral l)
    return (reg, hint)
compile_expr Nothing (Literalu8 _) = error "unknown width for literal"
compile_expr _ e = do
    xreg <- fresh_temp_ymm
    width <- compile_expr_to xreg e
    return (xreg,width)

reserve_for_args :: [Reg] -> Compilation [Reg]
reserve_for_args [] = return []
reserve_for_args (reg:regs) = do
    results <- reserve_for_args regs
    (env,lit,code,fix) <- get
    let (env',results') = (if env_contains_reg env reg
        then (env, results)
        else
            (("_temp",ERY reg):env, reg:results))
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
    case lookup x env of
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


