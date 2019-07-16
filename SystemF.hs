module SystemF where

-- TODO: reuse code where possible
-- import SimplyTypedLambdaCalculusWithBools (getTypeFromContext)
-- import SimplyTypedLambdaCalculusWithSubtyping (addBinding)

data Ty
  = TyVar Int Int
  | TyArr Ty Ty
  | TyAll String Ty
  | TySome String Ty
  deriving Eq

data Binding
  = NameBind
  | VarBind Ty
  | TyVarBind

type Info = String

data Term
  = TmVar Info Int Int
  | TmAbs Info String Ty Term
  | TmApp Info Term Term
  | TmTAbs Info String Term
  | TmTApp Info Term Ty
  | TmPack Info Ty Term Ty
  | TmUnpack Info String String Term Term

typeShiftAbove :: Int -> Int -> Ty -> Ty
typeShiftAbove d c (TyVar x n) =
  if x >= c
  then TyVar (x+d) (n+d)
  else TyVar x (n+d)
typeShiftAbove d c (TyArr tyT1 tyT2) =
  TyArr (typeShiftAbove d c tyT1) (typeShiftAbove d c tyT2)
typeShiftAbove d c (TyAll tyX tyT2) =
  TyAll tyX $ typeShiftAbove d (c+1) tyT2
typeShiftAbove d c (TySome tyX tyT2) =
  TySome tyX $ typeShiftAbove d (c+1) tyT2

typeShift :: Int -> Ty -> Ty
typeShift d tyT = typeShiftAbove d 0 tyT

typeMap :: (Int -> Int -> Int -> Ty) -> Int -> Ty -> Ty
typeMap onvar c (TyArr tyT1 tyT2) =
  TyArr (typeMap onvar c tyT1) (typeMap onvar c tyT2)
typeMap onvar c (TyVar x n) =
  onvar c x n
typeMap onvar c (TyAll tyX tyT2) =
  TyAll tyX $ typeMap onvar (c+1) tyT2
typeMap onvar c (TySome tyX tyT2) =
  TySome tyX $ typeMap onvar (c+1) tyT2

typeShiftAbove' :: Int -> Int -> Ty -> Ty
typeShiftAbove' d =
  typeMap (\c x n -> 
    if x >= c
    then TyVar (x+d) (n+d)
    else TyVar x (n+d)
  )

typeSubst :: Ty -> Int -> Ty -> Ty
typeSubst tyS =
  typeMap (\j x n ->
    if x == j
    then typeShift j tyS
    else TyVar x n
  )

typeSubstTop :: Ty -> Ty -> Ty
typeSubstTop tyS tyT =
  typeShift (-1) $ typeSubst (typeShift 1 tyS) 0 tyT

tmmap :: (Info -> Int -> Int -> Int -> Term) -> (Int -> Ty -> Ty) -> Int -> Term -> Term
tmmap onvar _ c (TmVar i x n) = 
  onvar i c x n
tmmap onvar ontype c (TmAbs i x tyT1 t2) = 
  TmAbs i x (ontype c tyT1) $ tmmap onvar ontype (c+1) t2
tmmap onvar ontype c (TmApp i t1 t2) = 
  TmApp i (tmmap onvar ontype c t1) (tmmap onvar ontype c t2)
tmmap onvar ontype c (TmTAbs i tyX t2) = 
  TmTAbs i tyX $ tmmap onvar ontype (c+1) t2
tmmap onvar ontype c (TmTApp i t1 tyT2) = 
  TmTApp i (tmmap onvar ontype c t1) (ontype c tyT2)
tmmap onvar ontype c (TmPack i tyT1 t2 tyT3) = 
  TmPack i (ontype c tyT1) (tmmap onvar ontype c t2) (ontype c tyT3)
tmmap onvar ontype c (TmUnpack i tyX x t1 t2) = 
  TmUnpack i tyX x (tmmap onvar ontype c t1) (tmmap onvar ontype (c+2) t2)

termShiftAbove :: Int -> Int -> Term -> Term
termShiftAbove d =
  tmmap (\i c x n ->
    if x >= c
    then TmVar i (x+d) (n+d)
    else TmVar i x (n+d)
  )
  (typeShiftAbove d)

termShift :: Int -> Term -> Term
termShift d t = termShiftAbove d 0 t

termSubst :: Int -> Term -> Term -> Term
termSubst j s =
  tmmap (\i k x n ->
    if x == k
    then termShift k s
    else TmVar i x n
  )
  (flip const)
  j

tyTermSubst :: Ty -> Int -> Term -> Term
tyTermSubst tyS =
  tmmap
    (\i _ x n -> TmVar i x n)
    (\j tyT -> typeSubst tyS j tyT)

termSubstTop :: Term -> Term -> Term
termSubstTop s t =
  termShift (-1) $ termSubst 0 (termShift 1 s) t

tyTermSubstTop :: Ty -> Term -> Term
tyTermSubstTop tyS t =
  termShift (-1) $ tyTermSubst (typeShift 1 tyS) 0 t

isVal _ _ = False

evalOne ctx (TmTApp i (TmTAbs _ x t11) tyT2) =
  tyTermSubstTop tyT2 t11
evalOne ctx (TmTApp i t1 tyT2) =
  TmTApp i (evalOne ctx t1) tyT2
evalOne ctx (TmUnpack i _ _ (TmPack _ tyT11 v12 _) t2)
  | isVal ctx v12 = 
    tyTermSubstTop tyT11 $ termSubstTop (termShift 1 v12) t2
evalOne ctx (TmUnpack i tyX x t1 t2) =
  TmUnpack i tyX x (evalOne ctx t1) t2
evalOne ctx (TmPack i tyT1 t2 tyT3) =
  TmPack i tyT1 (evalOne ctx t2) tyT3

addBinding = undefined
getTypeFromContext = undefined

typeOf ctx (TmVar i n _) =
  getTypeFromContext i ctx n
typeOf ctx (TmAbs i x tyT1 t2) =
  let ctx' = addBinding ctx x (VarBind tyT1)
      tyT2 = typeOf ctx' t2
  in TyArr tyT1 $ typeShift (-1) tyT2
typeOf ctx (TmApp i t1 t2) =
  let tyT1 = typeOf ctx t1
      tyT2 = typeOf ctx t2
  in case tyT1 of
    TyArr tyT11 tyT12 ->
      if tyT2 == tyT11
      then tyT12
      else error $ i ++ "parameter type mismatch"
    _ -> error $ i ++ "arrow type expected"
typeOf ctx (TmTAbs i tyX t2) =
  let ctx = addBinding ctx tyX TyVarBind
  in TyAll tyX (typeOf ctx t2)
typeOf ctx (TmTApp i t1 tyT2) =
  case typeOf ctx t1 of
    TyAll _ tyT12 -> typeSubstTop tyT2 tyT12
    _ -> error $ i ++ "universal type expected"
typeOf ctx (TmPack i tyT1 t2 tyT@(TySome tyY tyT2)) =
  let tyU = typeOf ctx t2
      tyU' = typeSubstTop tyT1 tyT2
  in 
    if tyU == tyU'
    then tyT
    else error $ i ++ "doesn't match declared type"
typeOf ctx (TmPack i tyT1 t2 _) =
  error $ i ++ "existential type expected"
typeOf ctx (TmUnpack i tyX x t1 t2) =
  let tyT1 = typeOf ctx t1
  in case tyT1 of
    TySome tyY tyT11 ->
      let ctx' = addBinding ctx tyX TyVarBind
          ctx'' = addBinding ctx' x (VarBind tyT11)
          tyT2 = typeOf ctx'' t2
      in typeShift (-2) tyT2
    _ -> error $ i ++ "existential type expected"

typeShiftAbove'' :: Int -> Int -> Ty -> Ty
typeShiftAbove'' d =
  typeMap (\c x n -> 
    if x >= c
    then 
      if x + d < 0
      then error "Scoping error!"
      else TyVar (x+d) (n+d)
    else TyVar x (n+d)
  )
