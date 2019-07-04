module UntypedArithmeticWithBools where

type Info = String

-- dummy info
mkInfo :: Info
mkInfo = ""

data Term
  = TmTrue Info
  | TmFalse Info
  | TmIf Info Term Term Term
  | TmZero Info
  | TmSucc Info Term
  | TmPred Info Term
  | TmIsZero Info Term

isNumericVal :: Term -> Bool
isNumericVal (TmZero _) = True
isNumericVal (TmSucc _ t) = isNumericVal t
isNumericVal _ = False

isVal :: Term -> Bool
isVal (TmTrue _) = True
isVal (TmFalse _) = True
isVal t
  | isNumericVal t = True
  | otherwise = False

evalOne :: Term -> Maybe Term
evalOne (TmIf _ (TmTrue _) t f) =
  Just t
evalOne (TmIf _ (TmFalse _) t f) =
  Just f
evalOne (TmIf i t1 t2 t3) =
  evalOne t1 >>= \t -> Just $ TmIf i t t2 t3
evalOne (TmSucc i t1) =
  TmSucc i <$> evalOne t1
evalOne (TmPred _ (TmZero _)) =
  Just $ TmZero mkInfo
evalOne (TmPred _ (TmSucc _ v))
  | isNumericVal v = Just v
evalOne (TmPred i t) =
  TmPred i <$> evalOne t
evalOne (TmIsZero _ (TmZero _)) =
  Just $ TmTrue mkInfo
evalOne (TmIsZero _ (TmSucc _ v))
  | isNumericVal v = Just $ TmFalse mkInfo
evalOne (TmIsZero i t) =
  TmIsZero i <$> evalOne t
evalOne _ =
  Nothing

eval :: Term -> Maybe Term
eval t = do
  t' <- evalOne t 
  if isVal t' then pure t' else eval t'
