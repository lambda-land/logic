module Logic.Rule where


type Name = String

data Rule j
  = Rule { name :: Name
         , premises :: [j]
         , conclusion :: j
         }