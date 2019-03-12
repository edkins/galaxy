module Compile where

import Parse (file,Statement(Assign),Expr(Literalu8,LiteralListu8,Var,MethodCall))
import X86

import Control.Monad.State (State,get,put,runState)
import Text.Parsec.String (parseFromFile)
import Text.Parsec.Error (ParseError)

type Env = [(String,Reg)]
type Literals = [Int]
type Code = [Int]
type Elf = [Int]

type Compilation a = State (Env,Literals,Code) a

base_addr_for_literals = 4096

emit :: [Int] -> Compilation ()
emit code' = do
    (env,lit,code) <- get
    put (env, lit, code ++ code')

padding :: Int -> Literals -> [Int]
padding align lit =
    case length lit `mod` align of
        0 -> []
        n -> replicate (align-n) 0

alloc_literal_aligned :: Int -> [Int] -> Compilation Int
alloc_literal_aligned align xs = do
    (env,lit,code) <- get
    let lit' = lit ++ padding align lit
    put (env, lit' ++ xs, code)
    return (base_addr_for_literals + length lit')

env_contains_reg :: Env -> Reg -> Bool
env_contains_reg [] _ = False
env_contains_reg ((x,r):e) reg = r==reg || env_contains_reg e reg

env_contains_uniform :: Env -> Int -> Maybe Reg
env_contains_uniform [] _ = Nothing
env_contains_uniform ((x,r):e) n = if x==show n then Just r else env_contains_uniform e n

fresh_xmm_from :: Int -> Env -> Reg
fresh_xmm_from n env =
    if env_contains_reg env (Xmm n) then
        fresh_xmm_from (n+1) env
    else
        Xmm n

fresh_gpr_from :: Int -> Env -> Reg
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
    ureg <- find_or_emit_uniform l
    emit (sse_rm paddb_rm xreg (R ureg))

compile_with :: [Statement] -> Compilation ()
compile_with [] = return ()
compile_with (s:ss) = do
    compile_statement s
    compile_with ss

make_elf :: Literals -> Code -> Elf
make_elf lit code = lit ++ code

compile :: [Statement] -> Elf
compile ss =
    let ((),(_,lit,code)) = runState (compile_with ss) ([],[],[])
    in make_elf lit code

compile_test :: IO (Either ParseError Elf)
compile_test = do
    a <- parseFromFile file "somecode.txt"
    return $ case a of
        Left e -> Left e
        Right ss -> Right (compile ss)


