module Tasks where

import Main
import Control.Applicative

instance Functor Parser where
    --fmap :: (a -> b) -> Parser a -> Parser b
    fmap f (Parser p) = Parser $ \s -> case p s of 
      Nothing -> Nothing
      Just (a, s') -> Just (f a, s')

instance Applicative Parser where
    --pure :: a -> Parser a
    pure a = Parser $ \s -> Just (a, s)
    --(<*>) :: Parser (a -> b) -> Parser a -> Parser b
    Parser pf <*> Parser pa = Parser $ \s -> case pf s of
      Nothing     -> Nothing
      Just (f, t) -> case pa t of
        Nothing     -> Nothing
        Just (a, r) -> Just (f a, r)

instance Alternative Parser where
    --empty :: Parser a  
    empty = Parser (\_ -> Nothing)
    --(<|>) :: Parser a -> Parser a -> Parser a  
    Parser fir <|> Parser sec = Parser $ \s -> case fir s of 
      Nothing -> sec s 
      x -> x

instance Monad Parser where 
  --return :: a -> Parser a 
  return = pure
  -- (>>=) :: Parser a -> (a -> Parser b) -> Parser b
  Parser p >>= f = Parser $ \s -> case p s of 
    Nothing -> Nothing 
    Just (a, s') -> runP (f a) $ s

toInt :: Parser (String->Int)
toInt = pure (\s -> case s of 
  [] -> 0
  _  -> read s)
  
merge::Maybe(String,String)->Maybe(String,String)->Maybe(String,String)
merge a b = case b of
    Nothing -> a
    Just(num,s) -> case a of
      Nothing -> Nothing
      Just(num2, s2) -> Just (num2++num, s)

string2Parser::String-> Parser String
string2Parser x = Parser $ (\s -> 
  let fn c = case runP digit c of
              Nothing -> Nothing
              Just (num, xs) -> merge (Just ([num], xs)) $ fn xs 
  in fn x)

parseString :: Parser String
parseString = Parser $ (\s -> case s of
  a -> Just (a,a))

nothing2Zero:: Maybe (Int,String) -> Parser Int
nothing2Zero x = Parser $ \s -> case x of
  Nothing -> Just (0, s)
  a -> a      

emptyTail:: Maybe (Int,String) -> Parser Int
emptyTail x = Parser $ \s -> case x of
  Just (a, "") -> Just (a,"")
  _ -> Nothing

--Task 1 
-- (runP parseInt1) "123abc" = Just (123, "abc")
-- (runP parseInt1) "abc" = Just (0, "abc")
parseInt1 :: Parser Int
parseInt1 = (return (runP parseInt2) <*> parseString ) >>= nothing2Zero

--Task 2
-- (runP parseInt2) "123abc" = Just (123, "abc")
-- (runP parseInt2) "abc" = Nothing
parseInt2 :: Parser Int
parseInt2 = toInt <*> (parseString >>= string2Parser)

--Task 3
-- (runP parseInt3) "123abc" = Nothing
-- (runP parseInt3) "123" = Just (123, "")
parseInt3 :: Parser Int 
parseInt3 = (return (runP parseInt2) <*> parseString ) >>= emptyTail

main :: IO ()
main = print $ 1