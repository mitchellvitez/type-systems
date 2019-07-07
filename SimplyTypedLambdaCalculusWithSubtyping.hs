module SimplyTypedLambdaCalculusWithSubtyping where

data Ty
  = TyRecord [(String, Ty)]
  | TyTop
  | TyArr Ty Ty
  deriving (Eq, Show)

type Info = String

mkInfo :: Info
mkInfo = ""

type Context = [(String, Binding)]

data Binding
  = NameBind
  | VarBind Ty
  deriving Show

addBinding :: Context -> String -> Binding -> Context
addBinding ctx x bind = (x, bind) : ctx

data Term
  = TmVar Info Int Int
  | TmAbs Info String Ty Term
  | TmApp Info Term Term
  | TmRecord Info [(String, Term)]
  | TmProj Info Term String

subtype :: Ty -> Ty -> Bool
subtype s t | s == t = True
subtype _ TyTop = True 
subtype (TyArr s1 s2) (TyArr t1 t2) =
  subtype t1 s1 && subtype s2 t2
subtype (TyRecord s) (TyRecord t) =
  all (==True) [subtype (lookupLabel li s) ti | (li, ti) <- t]
subtype _ _ = False

typeOf :: Context -> Term -> Ty
typeOf ctx (TmRecord _ fields) =
  let fieldTys = map (\(li, ti) -> (li, typeOf ctx ti)) fields in TyRecord fieldTys
typeOf ctx (TmProj i t1 l) =
  case typeOf ctx t1 of
    TyRecord fieldTys -> lookupLabel l fieldTys
    _ -> error $ i ++ "\nExpected record type"
typeOf ctx (TmVar i x _) =
  getTypeFromContext i ctx x
typeOf ctx (TmAbs _ x t1 t2) =
  TyArr t1 $ typeOf (addBinding ctx x (VarBind t1)) t2
typeOf ctx (TmApp i t1 t2) =
  let tyT1 = typeOf ctx t1
      tyT2 = typeOf ctx t2
  in case tyT1 of
    TyArr tyT11 tyT12 ->
      if subtype tyT2 tyT11 then tyT12
      else error $ i ++ "\n parameter type mismatch"
    _ -> error $ i ++ "\n arrow type expected"

lookupLabel :: String -> [(String, Ty)] -> Ty
lookupLabel l xs =
  case lookup l xs of
    Just x -> x
    Nothing -> error "label \"l\" not found"

getTypeFromContext :: Info -> Context -> Int -> Ty
getTypeFromContext = undefined -- TODO
