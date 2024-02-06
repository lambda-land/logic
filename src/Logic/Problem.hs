module Logic.Problem where
  
import Data.Maybe (fromJust)

import Logic.Proof
import Text.Latex

data Problem j = Fine j | Issue j | Missing | Axiom deriving Eq

instance Functor Problem where
  fmap f (Fine j) = Fine (f j)
  fmap f (Issue j) = Issue (f j)
  fmap _ Missing = Missing
  fmap _ Axiom = Axiom



problems :: Explain j => Proof j -> Proof (Problem j)
problems = fmap (\j -> if not $ null (premises j) then Fine j else Issue j)

nicerProblems :: Explain j => Proof j -> Proof (Problem j)
nicerProblems = go . problems 
  where go (Node (Issue j) _) = Node (Issue j) [Node Missing []]
        go (Node (Fine j) []) = Node (Fine j) [Node Axiom []]
        go (Node j ps)        = Node j (map go ps)



instance Show j => Show (Problem j) where
  show (Fine j) = show j
  show (Issue j) = "{>> " ++ show j ++ " <<}"-- "\x1b[1;31m {>> \x1b[0m " ++ show j ++ " \x1b[1;31m <<} \x1b[0m"
  show Missing = "(no proof)" -- "\x1b[0;31m(no proof)\x1b[0m"
  show Axiom = ""


instance Latex j => Latex (Problem j) where
  latex (Fine j) = latex j
  latex (Issue j) = "\\langle " ++ latex j ++ "\\rangle"
  latex Missing = "\\langle \\textbf{(no proof)} \\rangle"
  latex Axiom = ""