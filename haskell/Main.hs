module Main where
import Data.Char 

data Parser a = Parser { runP :: String -> Maybe (a, String) }

-- always succeeds without consuming any input
ok :: Parser ()
ok = Parser $ \s -> Just ((), s)

-- fails w/o consuming any input if given parser succeeds,
-- and succeeds if given parser fails
isnot :: Parser a -> Parser ()
isnot parser = Parser $ \s -> case runP parser s of
    Just _  -> Nothing
    Nothing -> Just ((), s)

-- succeeds only at the end of input stream
eof :: Parser ()
eof = Parser $ \s -> case s of
    [] -> Just ((), "")
    _  -> Nothing

-- consumes only single character and returns it if predicate is true
satisfy :: (Char -> Bool) -> Parser Char
satisfy p = Parser $ \s -> case s of
    []     -> Nothing
    (x:xs) -> if p x then Just (x, xs) else Nothing

-- always fails without consuming any input
notok :: Parser ()
notok = isnot ok

-- consumes given character and returns it
char :: Char -> Parser Char
char c = satisfy (== c)

-- consumes any character or any digit only
anyChar, digit :: Parser Char
anyChar = satisfy (const True)
digit   = satisfy isDigit