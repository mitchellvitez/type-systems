module SimplyTypedLambdaCalculusWithBools where

type Info = String

type Context = [(String, Binding)]

data Ty
  = TyArr Ty Ty
  | TyBool
  deriving (Show, Eq)

data Term
  = TmVar Info Int Int
  | TmAbs Info String Ty Term
  | TmApp Info Term Term
  | TmTrue Info
  | TmFalse Info
  | TmIf Info Term Term Term

data Binding
  = NameBind
  | VarBind Ty
  deriving Show

mkInfo :: Info
mkInfo = ""

addBinding :: Context -> String -> Binding -> Context
addBinding ctx x bind = (x, bind) : ctx

getTypeFromContext :: Info -> Context -> Int -> Ty
getTypeFromContext i ctx x =
  case getBinding i ctx x of
    VarBind tyT -> tyT
    _ -> error $ "getTypeFromContext: Wrong kind of binding for variable " ++
      (show . indexToName i ctx $ show x)

indexToName :: Info -> Context -> String -> Binding
indexToName _ [] _ = error "not found"
indexToName i ((n,b):rest) x =
  if n == x then b else indexToName i rest x

getBinding :: Info -> Context -> Int -> Binding
getBinding _ ctx n = snd $ ctx !! n

typeOf :: Context -> Term -> Ty
typeOf ctx (TmVar i x _) =
  getTypeFromContext i ctx x
typeOf ctx (TmAbs _ x tyT1 t2) =
  TyArr tyT1 $ typeOf (addBinding ctx x (VarBind tyT1)) t2
typeOf ctx (TmApp i t1 t2) =
  let tyT1 = typeOf ctx t1
      tyT2 = typeOf ctx t2
  in case tyT1 of
    TyArr tyT11 tyT12 ->
      if tyT2 == tyT11
      then tyT12
      else error i "parameter type mismatch"
    _ -> error i "arrow type expected"
typeOf _ (TmTrue _) =
  TyBool
typeOf _ (TmFalse _) =
  TyBool
typeOf ctx (TmIf i t1 t2 t3) =
  if typeOf ctx t1 == TyBool
  then 
    if tyT2 == typeOf ctx t3
    then tyT2
    else error i "arms of conditional have different types"
  else error i "guard of conditional not a boolean"
  where tyT2 = typeOf ctx t2
