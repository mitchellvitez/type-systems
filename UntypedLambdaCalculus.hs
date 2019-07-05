module UntypedLambdaCalculus where

type Info = String

-- dummy info
mkInfo :: Info
mkInfo = ""

type Context = [(Int, Binding)]

data Binding = NameBind
  deriving Show

data Term
  = TmVar Info Int Int
  | TmAbs Info String Term
  | TmApp Info Term Term

termToString :: Context -> Term -> String
termToString ctx (TmAbs _ x t1) =
  "(lambda " ++ x' ++ ". " ++ termToString ctx' t1 ++ ")"
  where (ctx', x') = pickFreshName ctx x
termToString ctx (TmApp _ t1 t2) =
  "(" ++ termToString ctx t1 ++ " " ++ termToString ctx t2 ++ ")"
termToString ctx (TmVar i x n) =
  if length ctx == n then
    indexToName i ctx x
  else
    "[bad index]"

pickFreshName :: Context -> String -> (Context, String)
pickFreshName ctx x = (ctx, x ++ "'")

indexToName :: Info -> Context -> Int -> String
indexToName _ [] _ = error "not found"
indexToName i ((n,b):rest) x =
  if n == x then show b else indexToName i rest x

termShift :: Int -> Term -> Term
termShift d t = walk 0 t where
  walk c (TmVar i x n) =
    if x >= c
    then TmVar i (x+d) (n+d)
    else TmVar i x (n+d)
  walk c (TmAbs i x t1) =
    TmAbs i x (walk (c+1) t1)
  walk c (TmApp i t1 t2) =
    TmApp i (walk c t1) (walk c t2)

termSubst :: Int -> Term -> Term -> Term
termSubst j s t = walk 0 t where
  walk c (TmVar i x n) =
    if x == j + c
    then termShift c s
    else TmVar i x n
  walk c (TmAbs i x t1) =
    TmAbs i x (walk (c+1) t1)
  walk c (TmApp i t1 t2) =
    TmApp i (walk c t1) (walk c t2)

termSubstTop :: Term -> Term -> Term
termSubstTop s t =
  termShift (-1) $ termSubst 0 (termShift 1 s) t

isVal :: Context -> Term -> Bool
isVal _ (TmAbs _ _ _) = True
isVal _ _ = False

evalOne :: Context -> Term -> Maybe Term
evalOne ctx (TmApp i (TmAbs _ x t12) v2)
  | isVal ctx v2 = Just $ termSubstTop v2 t12
evalOne ctx (TmApp i v1 t2)
  | isVal ctx v1 = TmApp i v1 <$> evalOne ctx t2
evalOne ctx (TmApp i t1 t2) =
  evalOne ctx t1 >>= \t1' -> Just $ TmApp i t1' t2
evalOne _ _ =
  Nothing

eval :: Context -> Term -> Maybe Term
eval ctx t = do
  t' <- evalOne ctx t
  if isVal ctx t' then pure t' else eval ctx t'
