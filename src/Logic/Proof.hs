{-# LANGUAGE PatternSynonyms #-}
module Logic.Proof (
  -- * Proof Trees
  Proof(..), pattern Proof, pattern Leaf,
  -- * Proof Generation
  Explain(..), proofs, prove, prove', suppose,
  -- * Proof Tree Manipulation
  conclusion, children,
  hidePast, hide,
  countNodes, getRow, toList, toList',
) where


import Data.List (intercalate)
import Data.Maybe (fromJust)


-- * Proof Trees


-- ---------------------------------------------------------------------------
-- | The type of proof trees parameterized by the type of judgments @j@.
data Proof j = Node j [Proof j]

-- | A constructor synonym for @Node@.
pattern Proof :: j -> [Proof j] -> Proof j
pattern Proof j ps = Node j ps

-- | A constructor synonym for @Node@ with no premises.
pattern Leaf :: j -> Proof j
pattern Leaf j = Node j []

-- | Extract the conclusion/root from a proof tree.
conclusion :: Proof j -> j
conclusion (Node j _) = j

-- | Extract the premises/children from a proof tree.
children :: Proof j -> [Proof j]
children (Node _ ps) = ps


-- | Get the proof tree with the premises hidden after the \(n\)th level.
hidePast :: Int -> Proof j -> Proof j
hidePast 0 (Node j _) = Node j []
hidePast n (Node j ps) = Node j (map (hidePast (n-1)) ps)

-- | Hide the subtrees of a proof tree that have the given judgment as their conclusion.
hide :: Eq j => j -> Proof j -> Maybe (Proof j)
hide j (Node j' ps)
    | j == j' = Nothing
    | otherwise = Just $ Node j' (map fromJust $ filter (not . null) $ map (hide j) ps)


-- | Count the number of judgemnets in a proof tree.
countNodes :: Proof j -> Int
countNodes (Node _ []) = 1
countNodes (Node _ ps) = 1 + sum (map countNodes ps)

-- | Get the \(n\)th row of a proof tree.
getRow :: Int -> Proof j -> [j]
getRow 0 (Node j _) = [j]
getRow n (Node _ ps) = concatMap (getRow (n-1)) ps

-- | Convert the proof tree to a list of judgements.
toList :: Eq j => Proof j -> [j]
toList p = concat $ takeWhile (/=[]) [getRow n p | n <- [0..countNodes p - 1]]

-- | Convert the proof tree to a list of judgements.
toList' :: Proof a -> [a]
toList' (Node j []) = [j]
toList' (Node j ps) = j : concatMap toList' ps


instance Functor Proof where
  fmap f (Node j ps) = Node (f j) $ map (fmap f) ps

instance Applicative Proof where
  pure j = Node j []
  (<*>) (Node f fs) (Node a as) = Node (f a) (zipWith (<*>) fs as)

instance Monad Proof where
  (Node j ps) >>= f = Node j' (map (>>= f) ps) where Node j' _ = f j

instance Foldable Proof where
  -- foldMap :: Monoid m => (a -> m) -> t a -> m
  foldMap f (Node j []) = f j <> mempty
  foldMap f (Node j ps) = f j <> mconcat (map (foldMap f) ps)

instance Traversable Proof where
  -- traverse :: Applicative f => (a -> f b) -> t a -> f (t b)
  -- traverse f (Node j ps) = 
  -- sequenceA :: Applicative f => Proof (f a) -> f (Proof a)
  sequenceA (Node fj []) = flip Node [] <$> fj
  sequenceA (Node fj ps) = Node <$> fj <*> sequenceA (map sequenceA ps)


-- instance Latex j => Latex (Proof j) where
--   latex (Node j []) = latex j
--   latex (Node j ps) = "\\infer[]{" ++ latex j ++ "}{" ++ intercalate " && " (map latex ps) ++ "}"


-- * Proof Generation

class Explain j where
  -- | Returns a list of all possible premises of a given judgment.
  -- 
  --   * @premises j = []@ if @j@ is decidably false.A
  --
  --   * @premises j = [[]]@ if @j@ is an axiom.
  --
  --   * @premises j = [p1,p2,...,pn] : tail (premises j) @ if @j@ is provable from the conclusions of @p1, p2, ..., pn@.
  premises :: j -> [[j]]


-- | Returns a list of all possible proofs of a given judgment.
proofs :: Explain j => j -> [Proof j]
proofs j | [[]] <- premises j = [Node j []]
proofs j = do 
    ps <- premises j
    let pfs = map proofs ps
    if or $ map null pfs 
        then []
        else map (Node j) $ sequence pfs

-- | Returns the first proof of a given judgment.
-- 
-- > prove j = listToMaybe (proofs j)
prove :: Explain j => j -> Maybe (Proof j)
prove j | (p:_) <- proofs j = Just p
prove _                     = Nothing

-- | Returns a proof of a given judgment or fails if the judgment is not provable.
--
-- > prove' j = fromJust (prove j)
prove' :: Explain j => j -> Proof j
prove' = fromJust . prove



-- proofs :: Explain judge => judge -> [Proof judge]
-- proofs j = concatMap (map (Node j) . lss . map proofs) (premises j)
--   where lss :: [[a]] -> [[a]] -- sequence -- isomers
--         lss [] = [[]]
--         lss (a:as) = [concatMap (a':) (lss as) | a' <- a]


-- | Gives the first proof of a given judgment and doesn't fail if the judgement is not provable.
suppose :: Explain j => j -> Proof j
suppose j = Node j (map suppose ps)
  where ps = case premises j of { [] -> []; (p:_) -> p }























instance Show j => Show (Proof j) where
  show pf = unlines (reverse ls) where (_, ls) = ppProof pf

-- return a list of lines and the width of the longest line
ppProof :: Show judge => Proof judge -> (Int, [String])
ppProof (Node j []) = (length line, [line]) where line = show j
ppProof (Node j ps) = (width, allLines) where

  pad :: a -> Int -> [a] -> [a]
  pad a n xs = xs ++ replicate (n - length xs) a

  appendLayout :: (Int, [String]) -> (Int, [String]) -> (Int, [String])
  appendLayout (w1, lines1) (w2, lines2) = (w1 + 2 + w2, combined) where
    common = max (length lines1) (length lines2)
    (lines1', lines2') = (pad "" common lines1, pad "" common lines2)
    lines1'' = map (pad ' ' w1) lines1'
    combined = zipWith (\l r -> l ++ "  " ++ r) lines1'' lines2'

  conclusion = show j
  (premisesWidth, premisesLines) = foldr1 appendLayout (map ppProof ps)
  width = max (length conclusion) premisesWidth
  divider = replicate width '-'
  concIndent = replicate ((width - length conclusion) `div` 2) ' '
  premIndent = replicate ((width - premisesWidth) `div` 2) ' '
  allLines = (concIndent ++ conclusion) : divider : map (premIndent ++) premisesLines

hideAfterLevel :: Int -> Proof judge -> Maybe (Proof judge) 
hideAfterLevel n (Node j ps) 
  | n == 0    = Nothing
  | otherwise = Just $ Node j (map unjust $ filter (not . null) $ map (hideAfterLevel (n-1)) ps) 
  where unjust (Just x) = x




