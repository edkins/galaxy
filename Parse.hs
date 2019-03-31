module Parse where

import Control.Applicative ((<|>))
import Text.Parsec (try,eof)
import Text.Parsec.String (Parser,parseFromFile)
import Text.Parsec.Char (letter,oneOf,char,string,digit,anyChar)
import Text.Parsec.Combinator (many1,skipMany1,option,optional,optionMaybe,sepBy,notFollowedBy,optional,manyTill)
import Data.Word (Word8,Word64)
import Data.Int (Int8)

data Expr = LiteralListu8 [Word8] | Literalu8 Word8 | Literali8 Int8 | Literalu64 Word64 | Var String | MethodCall Expr String [Expr]
    | Uninit PlainType | MutParam Expr | Slice Expr Expr Expr | Le Expr Expr deriving (Eq,Show)
data PlainType = U8 | U8Q | U8X | U8Y | U8Z | U8V | U16 | U16Q | U16X | U16Y | U16Z | U16V | I32 | U64
    | I8
    | Array PlainType Expr deriving (Eq,Show)
data Type = ByReg PlainType | ByMem PlainType | ByRM PlainType | Known PlainType
    | Uninitialized PlainType | Mut Type Type | Switch Type Type | DoesNotReturn | Void deriving (Eq,Show)
data AsmVex = Vex | Vex128 | Vex256 | Evex | Evex128 | Evex256 | Evex512 | Unspecified deriving (Eq,Show)
data AsmPrefix = Optional66 | Prefix66 | PrefixF3 | PrefixF2 | NoPrefix deriving (Eq,Show)
data AsmM = M0F | M0F38 | M0F3A | NoM deriving (Eq,Show)
data AsmW = W0 | W1 | WIG deriving (Eq,Show)
data AsmDef = AsmDef {
    asm_mr :: Bool,
    asm_vex :: AsmVex,
    asm_prefix :: AsmPrefix,
    asm_mmmmm :: AsmM,
    asm_w :: AsmW,
    asm_op :: Word8,
    asm_plusr :: Bool,
    asm_slash :: Maybe Word8
    } deriving Show
data Statement = Noop | Assign [Expr] Expr | Exit Expr | Print Expr | Write Expr
    | PlainExpr Expr | Return | Fn String [String] | PrimitiveFn String [(String,Type)] Type AsmDef Bool
    | SyscallFn String [(String,Type)] [(String,Type)] Int | Loop [Statement] | BreakIf Expr deriving Show

-------------------------
letter_underscore :: Parser Char
letter_underscore = letter <|> char '_'

kw :: String -> Parser ()
kw s = do
    string s
    notFollowedBy letter_underscore
    spaces

trykw :: String -> a -> Parser a
trykw s val = do
    try (kw s)
    return val

spaces :: Parser ()
spaces = optional $ skipMany1 $ oneOf [' ','\t']

just_newline :: Parser ()
just_newline = oneOf ['\r','\n'] >> return ()

one_newline :: Parser ()
one_newline = do
    try just_newline <|> (char '#' >> manyTill anyChar just_newline >> return ())
    spaces

newline :: Parser ()
newline = skipMany1 one_newline

word :: Parser String
word = do
    result <- many1 letter_underscore
    spaces
    return result

number :: Parser Integer
number = do
    ds <- many1 digit
    spaces
    return (read ds)

number_any :: Parser Expr
number_any = do
    ds <- many1 digit
    (do
        try $ string "u8"
        spaces
        return (Literalu8 (read ds))) <|> (do
        try $ string "u64"
        spaces
        return (Literalu64 (read ds))) <|> (do
        try $ string "i8"
        spaces
        return (Literali8 (read ds))) <|> (do
        spaces
        return (Literalu8 (read ds)))

equals :: Parser ()
equals = do
    char '='
    spaces

open_square_bracket :: Parser ()
open_square_bracket = do
    char '['
    spaces

close_square_bracket_u8 :: Parser ()
close_square_bracket_u8 = do
    string "]u8"
    spaces

comma :: Parser ()
comma = do
    char ','
    spaces

dot :: Parser ()
dot = do
    try (char '.' >> notFollowedBy (char '.'))
    spaces

open_paren :: Parser ()
open_paren = do
    char '('
    spaces

close_paren :: Parser ()
close_paren = do
    char ')'
    spaces

arrow :: Parser ()
arrow = do
    string "->"
    spaces

colon :: Parser ()
colon = do
    char ':'
    spaces

kw_call :: Parser ()
kw_call = kw "call"

kw_exit :: Parser ()
kw_exit = kw "exit"

kw_fn :: Parser ()
kw_fn = kw "fn"

kw_primitive :: Parser ()
kw_primitive = kw "primitive"

kw_print :: Parser ()
kw_print = kw "print"

kw_return :: Parser ()
kw_return = kw "return"

kw_syscall :: Parser ()
kw_syscall = kw "syscall"

kw_write :: Parser ()
kw_write = kw "write"

-------------------------
array_type :: Parser PlainType
array_type = do
    char '['
    spaces
    t <- plain_type
    char ';'
    spaces
    e <- expr
    char ']'
    spaces
    return (Array t e)

plain_type :: Parser PlainType
plain_type = (
    trykw "u8" U8 <|>
    trykw "u8q" U8Q <|>
    trykw "u8x" U8X <|>
    trykw "u8y" U8Y <|>
    trykw "u8z" U8Z <|>
    trykw "u8v" U8V <|>
    trykw "u16" U8 <|>
    trykw "u16q" U16Q <|>
    trykw "u16x" U16X <|>
    trykw "u16y" U16Y <|>
    trykw "u16z" U16Z <|>
    trykw "u16v" U16V <|>
    trykw "u64" U64 <|>
    trykw "i8" I8 <|>
    trykw "i32" I32 <|>
    array_type)

rm_type :: Parser Type
rm_type = do
    try $ string "(&)"
    spaces
    t <- plain_type
    return (ByRM t)

{-mut_mem_type :: Parser Type
mut_mem_type = do
    try (char '&' >> spaces >> kw "mut")
    t <- plain_type
    return (MutMem t)-}

switch_type :: Parser Type
switch_type = do
    try (char '&' >> spaces >> char '(')
    spaces
    t0 <- typ
    arrow
    t1 <- typ
    char ')'
    spaces
    return (Switch t0 t1)

mem_type :: Parser Type
mem_type = do
    try $ char '&'
    spaces
    t <- plain_type
    return (ByMem t)

known_type :: Parser Type
known_type = do
    try $ char '#'
    spaces
    t <- plain_type
    return (Known t)

uninit_type :: Parser Type
uninit_type = do
    try (char '&' >> spaces >> kw "uninitialized")
    t <- plain_type
    return (Uninitialized t)

dnr_type :: Parser Type
dnr_type = trykw "doesnotreturn" DoesNotReturn

void_type :: Parser Type
void_type = trykw "void" Void

reg_type :: Parser Type
reg_type = do
    t <- plain_type
    return (ByReg t)

typ :: Parser Type
typ = rm_type <|> switch_type <|> uninit_type <|> dnr_type <|> void_type <|> mem_type <|> known_type <|> reg_type

uninit :: Parser Expr
uninit = do
    try (char '&' >> spaces >> kw "uninitialized")
    t <- plain_type
    return (Uninit t)
-------------------------

parse_vex :: Parser AsmVex
parse_vex = (
    trykw "VEX.128" Vex128 <|>
    trykw "VEX.256" Vex256 <|>
    trykw "VEX" Vex <|>
    trykw "EVEX.128" Evex128 <|>
    trykw "EVEX.256" Evex256 <|>
    trykw "EVEX.512" Evex512 <|>
    trykw "EVEX" Evex <|>
    return Unspecified)

parse_prefix :: Parser AsmPrefix
parse_prefix = (
    trykw "(66)" Optional66 <|>
    trykw "66" Prefix66 <|>
    trykw "F3" PrefixF3 <|>
    trykw "F2" PrefixF2 <|>
    return NoPrefix)

parse_mmmmm :: Parser AsmM
parse_mmmmm =
    (try (kw "0F") >>
        (trykw "38" M0F38) <|> (trykw "3A" M0F3A) <|> return M0F) <|> return NoM

parse_w :: Parser AsmW
parse_w = (
    trykw "W0" W0 <|>
    trykw "W1" W1 <|>
    trykw "WIG" WIG)

parse_op :: Parser Word8
parse_op = do
    upper_nibble <- oneOf "0123456789ABCDEF"
    lower_nibble <- oneOf "0123456789ABCDEF"
    spaces
    return $ read ['0','x',upper_nibble,lower_nibble]

parse_plusr :: Parser Bool
parse_plusr = do
    option False (trykw "+r" True)

parse_slash :: Parser (Maybe Word8)
parse_slash = optionMaybe (do
    try (char '/')
    d <- oneOf "01234567"
    spaces
    return $ read [d])

parse_mr :: Parser Bool
parse_mr = option False (trykw "MR" True)

asm_def :: Parser AsmDef
asm_def = do
    mr <- parse_mr
    vex <- parse_vex
    prefix <- parse_prefix
    mmmmm <- parse_mmmmm
    w <- parse_w
    op <- parse_op
    plusr <- parse_plusr
    slash <- parse_slash
    return $ AsmDef {
        asm_mr = mr,
        asm_vex = vex,
        asm_prefix = prefix,
        asm_mmmmm = mmmmm,
        asm_w = w,
        asm_op = op,
        asm_plusr = plusr,
        asm_slash = slash
        }

-------------------------
typed_arg :: Parser (String,Type)
typed_arg = do
    x <- word
    colon
    t <- typ
    return (x,t)

mut_expr :: Parser Expr
mut_expr = do
    try (kw "mut")
    e <- expr
    return (MutParam e)

actual_param :: Parser Expr
actual_param = mut_expr <|> expr

literal_list :: Parser Expr
literal_list = do
    open_square_bracket
    ns <- number `sepBy` comma
    close_square_bracket_u8
    return $ LiteralListu8 $ map fromIntegral ns

word_expr :: Parser Expr
word_expr = do
    x <- word
    return $ Var x

expr1 :: Parser Expr
expr1 = literal_list <|> word_expr <|> number_any <|> uninit

dot_method :: Parser (Expr->Expr)
dot_method = do
    dot
    m <- word
    open_paren
    args <- actual_param `sepBy` comma
    close_paren
    return (\e -> MethodCall e m args)

array_lookup :: Parser (Expr->Expr)
array_lookup = do
    char '['
    spaces
    index <- expr
    string "..+"
    spaces
    count <- expr
    char ']'
    spaces
    return (\e -> Slice e index count)

suffixes :: a -> (Parser (a->a)) -> Parser a
suffixes init sfx = do
    o <- optionMaybe sfx
    case o of
        Nothing -> return init
        Just f -> suffixes (f init) sfx

term :: Parser Expr
term = do
    e <- expr1
    suffixes e (dot_method <|> array_lookup)

comparison :: Parser (Expr->Expr)
comparison = do
    string ">="
    spaces
    e <- expr
    return (\l -> Le e l)

expr :: Parser Expr
expr = do
    e <- term
    o <- optionMaybe comparison
    case o of
        Nothing -> return e
        Just f -> return (f e)

lhs :: Parser Expr
lhs = do
    e <- expr1
    suffixes e array_lookup

return_thing :: Parser (String,Type)
return_thing = do
    t <- typ
    x <- option "" (do
        char '@'
        spaces
        word)
    return (x,t)

assignment :: Parser Statement
assignment = do
    xs <- try(do
        xs <- lhs `sepBy` comma
        equals
        return xs)
    e <- expr
    newline
    return $ Assign xs e

expr_statement :: Parser Statement
expr_statement = do
    e <- try expr
    newline
    return $ PlainExpr e

exit_statement :: Parser Statement
exit_statement = do
    try kw_exit
    e <- expr
    newline
    return (Exit e)

print_statement :: Parser Statement
print_statement = do
    try kw_print
    e <- expr
    newline
    return (Print e)

write_statement :: Parser Statement
write_statement = do
    try kw_write
    e <- expr
    newline
    return (Write e)

return_statement :: Parser Statement
return_statement = do
    try kw_return
    newline
    return Return

fn_statement :: Parser Statement
fn_statement = do
    try kw_fn
    f <- word
    open_paren
    args <- word `sepBy` comma
    close_paren
    newline
    return $ Fn f args

primitive_fn_statement :: Parser Statement
primitive_fn_statement = do
    try kw_primitive
    kw_fn
    f <- word
    open_paren
    args <- typed_arg `sepBy` comma
    close_paren
    arrow
    rt <- typ
    equals
    asm <- asm_def
    incidental <- option False (trykw "incidental" True)
    newline
    return (PrimitiveFn f args rt asm incidental)

syscall_fn_statement :: Parser Statement
syscall_fn_statement = do
    try kw_syscall
    kw_fn
    f <- word
    open_paren
    args <- typed_arg `sepBy` comma
    close_paren
    arrow
    rts <- return_thing `sepBy` comma
    equals
    n <- number
    newline
    return (SyscallFn f args rts (fromIntegral n))

loop_statement :: Parser Statement
loop_statement = do
    try (kw "loop")
    newline
    contents <- manyTill statement (kw "endloop" >> newline)
    return (Loop contents)

break_if_statement :: Parser Statement
break_if_statement = do
    try (kw "break")
    kw "if"
    e <- expr
    newline
    return (BreakIf e)

statement :: Parser Statement
statement = assignment <|> exit_statement <|> print_statement <|> write_statement <|> return_statement
    <|> fn_statement <|> primitive_fn_statement <|> syscall_fn_statement <|> loop_statement <|> break_if_statement <|> expr_statement

file :: Parser [Statement]
file = do
    optional newline
    result <- many1 statement
    eof
    return result

-------------------------

test :: IO ()
test = do
    a <- parseFromFile file "somecode.txt"
    print a

