module Text.Latex where

type Tex = String

class Latex a where
  latex :: a -> Tex

parens :: Latex a => a -> Tex
parens x = "(" ++ latex x ++ ")"

curlys :: Latex a => a -> Tex
curlys x = "{" ++ latex x ++ "}"

codeTex :: Latex a => a -> Tex
codeTex x = "\\texttt{" ++ latex x ++ "}"

latexParen :: Latex a => (a -> Bool) -> a -> Tex
latexParen isSimple x | not $ isSimple x = latex x
                      | otherwise  = parens x
