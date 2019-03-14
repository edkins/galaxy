module Parse where

import Control.Applicative ((<|>))
import Text.Parsec.String (Parser,parseFromFile)
import Text.Parsec.Char (letter,oneOf,char,string,digit)
import Text.Parsec.Combinator (many1,skipMany1,optional,optionMaybe,sepBy)
import Data.Word (Word8)

data Expr = LiteralListu8 [Word8] | Literalu8 Word8 | Var String | MethodCall Expr String [Expr] deriving Show
data Statement = Noop | Assign String Expr deriving Show

-------------------------

spaces :: Parser ()
spaces = optional $ skipMany1 $ oneOf [' ','\t']

newline :: Parser ()
newline = skipMany1 $ oneOf ['\r','\n']

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

number_u8 :: Parser Int
number_u8 = do
    ds <- many1 digit
    string "u8"
    spaces
    return (read ds) 

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

u8_expr :: Parser Expr
u8_expr = do
    n <- number_u8
    return $ Literalu8 (fromIntegral n)

expr1 :: Parser Expr
expr1 = literal_list <|> word_expr <|> u8_expr

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
    x <- word
    equals
    e <- expr
    newline
    return $ Assign x e

statement = assignment

file = many1 statement

-------------------------

test :: IO ()
test = do
    a <- parseFromFile file "somecode.txt"
    print a

