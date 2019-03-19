module Parse where

import Control.Applicative ((<|>))
import Text.Parsec (try,eof)
import Text.Parsec.String (Parser,parseFromFile)
import Text.Parsec.Char (letter,oneOf,char,string,digit,anyChar)
import Text.Parsec.Combinator (many1,skipMany1,optional,optionMaybe,sepBy,notFollowedBy,optional,manyTill)
import Data.Word (Word8)

data Expr = LiteralListu8 [Word8] | Literalu8 Word8 | Var String | MethodCall Expr String [Expr] deriving Show
data PlainType = U8 | U8Q | U8X | U8Y | U8Z | U8V | U16 | U16Q | U16X | U16Y | U16Z | U16V deriving (Eq,Show)
data Type = ByReg PlainType | ByMem PlainType | ByRM PlainType | Known PlainType deriving (Eq,Show)
data AsmVex = Vex | Vex128 | Vex256 | Evex | Evex128 | Evex256 | Evex512 | Unspecified deriving (Eq,Show)
data AsmPrefix = Optional66 | Prefix66 | PrefixF3 | PrefixF2 deriving (Eq,Show)
data AsmM = M0F | M0F38 | M0F3A deriving (Eq,Show)
data AsmW = W0 | W1 | WIG deriving (Eq,Show)
data AsmDef = AsmDef {
    asm_vex :: AsmVex,
    asm_prefix :: AsmPrefix,
    asm_mmmmm :: AsmM,
    asm_w :: AsmW,
    asm_op :: Word8,
    asm_slash :: Maybe Word8
    } deriving Show
data Statement = Noop | Assign String Expr | Exit Expr | Print Expr | Write Expr
    | Call String [Expr] | Return | Fn String [String] | PrimitiveFn String [(String,Type)] Type AsmDef deriving Show

-------------------------
kw :: String -> Parser ()
kw s = do
    string s
    notFollowedBy letter
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
    result <- many1 letter
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
    let n = read ds
    (do
        try $ string "u8"
        spaces
        return (Literalu8 n)) <|> (do
        spaces
        return (Literalu8 n))

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
    char '.'
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

kw_write :: Parser ()
kw_write = kw "write"

-------------------------
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
    trykw "u16v" U16V)

rm_type :: Parser Type
rm_type = do
    try $ string "(&)"
    spaces
    t <- plain_type
    return (ByRM t)

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

reg_type :: Parser Type
reg_type = do
    t <- plain_type
    return (ByReg t)

typ :: Parser Type
typ = rm_type <|> mem_type <|> known_type <|> reg_type
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
    trykw "F2" PrefixF2)

parse_mmmmm :: Parser AsmM
parse_mmmmm = do
    kw "0F"
    (trykw "38" M0F38) <|> (trykw "3A" M0F3A) <|> return M0F

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

parse_slash :: Parser (Maybe Word8)
parse_slash = optionMaybe (do
    try (char '/')
    d <- oneOf "01234567"
    return $ read [d])

asm_def :: Parser AsmDef
asm_def = do
    vex <- parse_vex
    prefix <- parse_prefix
    mmmmm <- parse_mmmmm
    w <- parse_w
    op <- parse_op
    slash <- parse_slash
    return $ AsmDef {
        asm_vex = vex,
        asm_prefix = prefix,
        asm_mmmmm = mmmmm,
        asm_w = w,
        asm_op = op,
        asm_slash = slash
        }

-------------------------
typed_arg :: Parser (String,Type)
typed_arg = do
    x <- word
    colon
    t <- typ
    return (x,t)

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
expr1 = literal_list <|> word_expr <|> number_any

dot_method :: Expr -> Parser Expr
dot_method e = do
    dot
    m <- word
    open_paren
    args <- expr `sepBy` comma
    close_paren
    return $ MethodCall e m args

suffixes :: a -> (a -> Parser a) -> Parser a
suffixes init sfx = do
    o <- optionMaybe (sfx init)
    case o of
        Nothing -> return init
        Just result -> suffixes result sfx

expr :: Parser Expr
expr = do
    e <- expr1
    suffixes e dot_method

assignment :: Parser Statement
assignment = do
    x <- try(do
        x <- word
        equals
        return x)
    e <- expr
    newline
    return $ Assign x e

call_statement :: Parser Statement
call_statement = do
    try kw_call
    f <- word
    open_paren
    args <- expr `sepBy` comma
    close_paren
    newline
    return $ Call f args

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
    newline
    return (PrimitiveFn f args rt asm)

statement :: Parser Statement
statement = assignment <|> exit_statement <|> print_statement <|> call_statement <|> write_statement <|> return_statement
    <|> fn_statement <|> primitive_fn_statement

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

