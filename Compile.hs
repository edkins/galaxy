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
            emit (vex128_rm vpbroadcastb_rm yreg (R xreg))
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
        e_shoff = qw 0
        e_flags = dw 0
        e_ehsize = wd 0x40
        e_phentsize = wd 0x38
        phnum = 2
        e_phnum = wd phnum
        e_shentsize = wd 0x40
        e_shnum = wd 0
        e_shstrndx = wd 0

        elf_header = e_ident <> e_type <> e_machine <> e_version <> e_entry <> e_phoff <> e_shoff <> e_flags <> e_ehsize <> e_phentsize <> e_phnum <> e_shentsize <> e_shnum <> e_shstrndx

        p0_type = dw 1    -- LOAD
        p0_flags = dw 4   -- r
        offset0 = 0x40 + fromIntegral phnum * 0x38
        p0_offset = qw offset0
        p0_vaddr = qw $ fromIntegral base_addr_for_literals
        p0_paddr = qw 0
        p0_filesz = qw $ fromIntegral $ clength lit
        p0_memsz = p0_filesz
        p0_align = qw 0x1000
        p0 = p0_type <> p0_flags <> p0_offset <> p0_vaddr <> p0_paddr <> p0_filesz <> p0_memsz <> p0_align
        
        p1_type = dw 1
        p1_flags = dw 5   -- r+x
        offset1 = offset0 + fromIntegral (clength lit)
        p1_offset = qw offset1
        p1_vaddr = qw code_start
        p1_paddr = qw 0
        p1_filesz = qw $ fromIntegral $ clength code
        p1_memsz = p1_filesz
        p1_align = qw 1
        p1 = p1_type <> p1_flags <> p1_offset <> p1_vaddr <> p1_paddr <> p1_filesz <> p1_memsz <> p1_align
    in
        elf_header <> p0 <> p1 <> lit <> code

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


