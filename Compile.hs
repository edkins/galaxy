module Compile where

import Parse (file,Statement(Assign),Expr(Literalu8,LiteralListu8,Var,MethodCall))
import X86

import Control.Monad.State (State,get,put,runState)
import Text.Parsec.String (parseFromFile)
import Text.Parsec.Error (ParseError)
import Data.ByteString.Builder
import Data.ByteString.Lazy (unpack)
import Data.Word (Word8)
import Data.Monoid ((<>))
import System.IO (withBinaryFile,IOMode (WriteMode))

type Env = [(String,Reg)]
type Literals = Code
type Elf = Code

type Compilation a = State (Env,Literals,Code) a

base_addr_for_literals = 4096

emit :: Code -> Compilation ()
emit code' = do
    (env,lit,code) <- get
    put (env, lit, code <> code')

padding :: Int -> Literals -> Code
padding align lit =
    case clength lit `mod` align of
        0 -> mempty
        n -> zeros (align-n)

alloc_literal_aligned :: Int -> [Word8] -> Compilation Int
alloc_literal_aligned align xs = do
    (env,lit,code) <- get
    let lit' = lit <> padding align lit
    put (env, lit' <> bytes xs, code)
    return (base_addr_for_literals + clength lit')

env_contains_reg :: Env -> Reg -> Bool
env_contains_reg [] _ = False
env_contains_reg ((x,r):e) reg = r==reg || env_contains_reg e reg

env_contains_uniform :: Env -> Int -> Maybe Reg
env_contains_uniform [] _ = Nothing
env_contains_uniform ((x,r):e) n = if x==show n then Just r else env_contains_uniform e n

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

fresh_xmm :: String -> Compilation Reg
fresh_xmm x = do
    (env,lit,code) <- get
    let result = fresh_xmm_from 0 env
    put (env ++ [(x,result)],lit,code)
    return result

fresh_gpr :: String -> Compilation Reg
fresh_gpr x = do
    (env,lit,code) <- get
    let result = fresh_gpr_from 0 env
    put (env ++ [(x,result)],lit,code)
    return result

env_lookup :: String -> Compilation (Maybe Reg)
env_lookup x = do
    (env,_,_) <- get
    return (lookup x env)

env_lookup_uniform :: Int -> Compilation (Maybe Reg)
env_lookup_uniform n = do
    (env,_,_) <- get
    return (env_contains_uniform env n)

find_or_fresh_xmm :: String -> Compilation Reg
find_or_fresh_xmm x = do
    mb <- env_lookup x
    case mb of
        Nothing -> fresh_xmm x
        Just r -> return r

find_or_emit_uniform :: Int -> Compilation Reg
find_or_emit_uniform n = do
    mb <- env_lookup_uniform n
    case mb of
        Just r -> return r
        Nothing -> do
            let name = show n
            xreg <- fresh_gpr name
            yreg <- fresh_xmm name
            emit (old_oi mov_oi8 xreg n)
            emit (evex128_rm evpbroadcastb_gpr_rm yreg (R xreg))
            return yreg

compile_statement :: Statement -> Compilation ()
compile_statement (Assign x (LiteralListu8 ls)) =
    if length ls == 16 then
        do
            addr <- alloc_literal_aligned 16 ls
            xreg <- find_or_fresh_xmm x
            emit (sse_rm movdqa_rm xreg (AbsMem addr))
    else
        error "Expected exactly 16 bytes"
compile_statement (Assign x (MethodCall (Var y) "addwrap" [Literalu8 l])) = do
    xreg <- find_or_fresh_xmm x
    ureg <- find_or_emit_uniform (fromIntegral l)
    emit (sse_rm paddb_rm xreg (R ureg))

compile_with :: [Statement] -> Compilation ()
compile_with [] = return ()
compile_with (s:ss) = do
    compile_statement s
    compile_with ss

make_elf :: Literals -> Code -> Elf
make_elf lit code =
    let
        code_start = fromIntegral (base_addr_for_literals + clength lit)
        entry_point = code_start
 
        strings = "\0.shstrtab\0.rodata\0.text\0"
        string_null = 0
        string_shstrtab = string_null + 1
        string_rodata = string_shstrtab + 10
        string_text = string_rodata + 8

        phnum = 2
        shnum = 4
        offset0 = 0x40 + fromIntegral phnum * 0x38
        offset1 = offset0 + fromIntegral (clength lit)
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
        p0_paddr = qw 0
        p0_filesz = qw $ fromIntegral $ clength lit
        p0_memsz = p0_filesz
        p0_align = qw 0x1000
        p0 = p0_type <> p0_flags <> p0_offset <> p0_vaddr <> p0_paddr <> p0_filesz <> p0_memsz <> p0_align
        
        p1_type = dw 1
        p1_flags = dw 5   -- r+x
        p1_offset = qw offset1
        p1_vaddr = qw code_start
        p1_paddr = qw 0
        p1_filesz = qw $ fromIntegral $ clength code
        p1_memsz = p1_filesz
        p1_align = qw 1
        p1 = p1_type <> p1_flags <> p1_offset <> p1_vaddr <> p1_paddr <> p1_filesz <> p1_memsz <> p1_align

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
        sh2_addralign = qw 0x1000
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
        sh3_addralign = qw 1
        sh3_entsize = qw 0
        sh3 = sh3_name <> sh3_type <> sh3_flags <> sh3_addr <> sh3_offset <> sh3_size <> sh3_link <> sh3_info <> sh3_addralign <> sh3_entsize
    in
        elf_header <> p0 <> p1 <> lit <> code <> shstrtab <> sh0 <> sh1 <> sh2 <> sh3

compile :: [Statement] -> Elf
compile ss =
    let ((),(_,lit,code)) = runState (compile_with ss) ([],mempty,mempty)
    in make_elf lit code

compile_test :: IO ()
compile_test = do
    a <- parseFromFile file "somecode.txt"
    case a of
        Left e -> print e
        Right ss -> withBinaryFile "output.elf" WriteMode (\h -> do
            hPutBuilder h (code_as_builder $ compile ss)
            putStrLn "written output.elf"
            )


