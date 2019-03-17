module Parse where

import Control.Applicative ((<|>))
import Text.Parsec (try,eof)
import Text.Parsec.String (Parser,parseFromFile)
import Text.Parsec.Char (letter,oneOf,char,string,digit)
import Text.Parsec.Combinator (many1,skipMany1,optional,optionMaybe,sepBy)
import Data.Word (Word8)

data Expr = LiteralListu8 [Word8] | Literalu8 Word8 | Var String | MethodCall Expr String [Expr] deriving Show
data Statement = Noop | Assign String Expr | Exit Expr | Print Expr | Write Expr
    | Call String [Expr] | Return | Fn String [String] deriving Show

-------------------------

spaces :: Parser ()
spaces = optional $ skipMany1 $ oneOf [' ','\t']

newline :: Parser ()
newline = skipMany1 (oneOf ['\r','\n'] >> spaces)

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

kw_call :: Parser ()
kw_call = do
    string "call"
    spaces

kw_exit :: Parser ()
kw_exit = do
    string "exit"
    spaces

kw_fn :: Parser ()
kw_fn = do
    string "fn"
    spaces

kw_print :: Parser ()
kw_print = do
    string "print"
    spaces

kw_return :: Parser ()
kw_return = do
    string "return"
    spaces

kw_write :: Parser ()
kw_write = do
    string "write"
    spaces

-------------------------

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

statement :: Parser Statement
statement = assignment <|> exit_statement <|> print_statement <|> call_statement <|> write_statement <|> return_statement
    <|> fn_statement

file :: Parser [Statement]
file = do
    result <- many1 statement
    eof
    return result

-------------------------

test :: IO ()
test = do
    a <- parseFromFile file "somecode.txt"
    print a

