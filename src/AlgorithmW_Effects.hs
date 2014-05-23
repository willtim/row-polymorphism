-------------------------------------------------------------------------
-- Row-polymorphic effect types using constrained rows

-- See "Koka: Programming with Row-polymorphic Effect Types" by D. Leijen
-- for a similar implementation using scoped-labels.
-------------------------------------------------------------------------

{-# LANGUAGE OverloadedStrings, ViewPatterns #-}

module AlgorithmW_Effects where

import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S

import Control.Applicative ((<$>))
import Control.Arrow (first)
import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State
import Data.String
import Text.PrettyPrint.Leijen hiding ((<$>))

type Name  = String
type Label = String

data Exp
  = EVar  Name
  | EPrim Prim
  | EApp  Exp Exp
  | EAbs  Name Exp
  | ELet  Name Exp Exp

data Prim
  = Unit
  | Int Integer
  | Bool Bool
  | Str String
  | Add
  | Sub
  | Mul
  | Div    -- ^ a partial function for integers
  | Catch  -- ^ catch and handle divide-by-zero exception
  | Total  -- ^ mark an expression as being free from partiality
  | Print  -- ^ does IO
  | Pure   -- ^ marks an expression as being free from IO
    deriving (Eq, Ord)

type Effect = Type

data Type
  = TVar TyVar
  | TUnit
  | TInt
  | TBool
  | TStr
  | TFun Type Effect Type
  | TRowEmpty
  | TRowExtend Label Type Type
    deriving (Eq, Ord)

data TyVar = TyVar
  { tyvarName       :: Name
  , tyvarKind       :: Kind
  , tyvarConstraint :: Constraint
  } deriving (Eq, Ord)

-- | row type variables may have constraints
data Kind = Star | Row deriving (Eq, Ord)

-- | labels the associated tyvar must lack, for types of kind row
type Constraint = S.Set Label

data Scheme = Scheme [TyVar] Type

class Types a where
  ftv :: a -> S.Set TyVar -- ^ free type variables
  apply :: Subst -> a -> a

instance Types Type where
  ftv (TVar v) = S.singleton v
  ftv TUnit = S.empty
  ftv TInt = S.empty
  ftv TBool = S.empty
  ftv (TFun t1 eff t2) = S.unions [ftv t1, ftv eff, ftv t2]
  ftv TRowEmpty = S.empty
  ftv (TRowExtend l t r) = ftv r `S.union` ftv t
  apply s (TVar v) = case M.lookup v s of
                       Nothing -> TVar v
                       Just t -> t
  apply s (TFun t1 eff t2) = TFun (apply s t1) (apply s eff) (apply s t2)
  apply s (TRowExtend l t r) = TRowExtend l (apply s t) (apply s r)
  apply s t = t

instance Types Scheme where
  ftv (Scheme vars t) = (ftv t) S.\\ (S.fromList vars)
  apply s (Scheme vars t) = Scheme vars (apply (foldr M.delete s vars) t)

instance Types a => Types [a] where
  apply s = map (apply s)
  ftv l = foldr S.union S.empty (map ftv l)

type Subst = M.Map TyVar Type

nullSubst :: Subst
nullSubst = M.empty

emptyEff :: Effect
emptyEff = TRowEmpty

-- | apply s1 and then s2
-- NB: order is very important, there were bugs in the original
-- "Algorithm W Step-by-Step" paper related to substitution composition
composeSubst :: Subst -> Subst -> Subst
composeSubst s1 s2 = (M.map (apply s1) s2) `M.union` s1

newtype TypeEnv = TypeEnv (M.Map Name Scheme)

remove :: TypeEnv -> Name -> TypeEnv
remove (TypeEnv env) var = TypeEnv (M.delete var env)

instance Types TypeEnv where
  ftv (TypeEnv env) = ftv (M.elems env)
  apply s (TypeEnv env) = TypeEnv (M.map (apply s) env)

-- | generalise abstracts a type over all type variables which are free
-- in the type but not free in the given type environment.
generalise :: TypeEnv -> Type -> Scheme
generalise env t = Scheme vars t
  where
    vars = S.toList ((ftv t) S.\\ (ftv env))

data TIEnv = TIEnv {}
data TIState = TIState {tiSupply :: Int, tiSubst :: Subst }

type TI a = ErrorT String (ReaderT TIEnv (StateT TIState IO)) a

runTI :: TI a -> IO (Either String a, TIState)
runTI t = do
  (res, st) <- runStateT (runReaderT (runErrorT t) initTIEnv) initTIState
  return (res, st)
  where
    initTIEnv = TIEnv {}

initTIState = TIState {tiSupply = 0, tiSubst = M.empty }

newTyVar :: Char -> TI Type
newTyVar = newTyVarWith Star none

newTyVarWith :: Kind -> Constraint -> Char -> TI Type
newTyVarWith k c prefix = do
  s <- get
  put s {tiSupply = tiSupply s + 1 }
  let name = prefix : show (tiSupply s)
  return (TVar $ TyVar name k c)

newEffect :: TI Effect
newEffect = newEffectWith none

newEffectWith :: Constraint -> TI Effect
newEffectWith c = newTyVarWith Row c 'e'


-- | The instantiation function replaces all bound type variables in a
-- type scheme with fresh type variables.
instantiate :: Scheme -> TI Type
instantiate (Scheme vars t) = do
  nvars <- mapM (\(TyVar (p:_) k c) -> newTyVarWith k c p) vars
  let s = M.fromList (zip vars nvars)
  return $ apply s t

unify :: Type -> Type -> TI Subst
unify (TFun l eff r) (TFun l' eff' r') = do
  s1 <- unify l l'
  s2 <- unify (apply s1 eff) (apply s1 eff')
  let s = s2 `composeSubst` s1
  s3 <- unify (apply s r) (apply s r')
  return $ s3 `composeSubst` s
unify (TVar u) (TVar v) = unionConstraints u v
unify (TVar v) t  = varBind v t
unify t (TVar v)  = varBind v t
unify TUnit TUnit = return nullSubst
unify TInt TInt   = return nullSubst
unify TBool TBool = return nullSubst
unify TStr  TStr  = return nullSubst
unify TRowEmpty TRowEmpty = return nullSubst
unify (TRowExtend label1 fieldTy1 rowTail1) row2@TRowExtend{} = do
  (fieldTy2, rowTail2, theta1) <- rewriteRow row2 label1
  -- ^ apply side-condition to ensure termination
  case snd $ toList rowTail2 of
    Just tv | M.member tv theta1 -> throwError "recursive row type"
    _ -> do
      theta2 <- unify (apply theta1 fieldTy1) (apply theta1 fieldTy2)
      let s = theta2 `composeSubst` theta1
      theta3 <- unify (apply s rowTail1) (apply s rowTail2)
      return $ theta3 `composeSubst` s
unify t1 t2 = throwError $ "types do not unify: " ++ show t1 ++ " vs. " ++ show t2

-- | in order to unify two type variables, we must union any lacks constraints
unionConstraints :: TyVar -> TyVar -> TI Subst
unionConstraints u v
  | u == v    = return nullSubst
  | otherwise =
      case (tyvarKind u, tyvarKind v) of
       (Star, Star) -> return $ M.singleton u (TVar v)
       (Row,  Row)  -> do
         let c = (tyvarConstraint u) `S.union` (tyvarConstraint v)
         r <- newTyVarWith Row c 'e'
         return $ M.fromList [ (u, r), (v, r) ]
       _            -> throwError "kind mismatch!"

varBind :: TyVar -> Type -> TI Subst
varBind u t
  | u `S.member` ftv t = throwError $ "occur check fails: " ++ " vs. " ++ show t
  | otherwise          = case tyvarKind u of
                           Star -> return $ M.singleton u t
                           Row  -> varBindRow u t

-- | bind the row tyvar to the row type, as long as the row type does not
-- contain the labels in the tyvar lacks constraint; and propagate these
-- label constraints to the row variable in the row tail, if there is one.
varBindRow :: TyVar -> Type -> TI Subst
varBindRow u t
  = case S.toList (ls `S.intersection` ls') of
      [] | Nothing <- mv -> return s1
         | Just r1 <- mv -> do
             let c = ls `S.union` (tyvarConstraint r1)
             r2 <- newTyVarWith Row c 'e'
             let s2 = M.singleton r1 r2
             return $ s1 `composeSubst` s2
      labels             -> throwError $ "illegal label(s): " ++ show labels
  where
    ls        = tyvarConstraint u
    (ls', mv) = first (S.fromList . map fst) $ toList t
    s1        = M.singleton u t

rewriteRow :: Type -> Label -> TI (Type, Type, Subst)
rewriteRow TRowEmpty newLabel = throwError $ "label " ++ newLabel ++ " cannot be inserted"
rewriteRow (TRowExtend label fieldTy rowTail) newLabel
  | newLabel == label     = return (fieldTy, rowTail, nullSubst) -- ^ nothing to do
  | TVar alpha <- rowTail = do
      beta  <- newTyVarWith Row (lacks newLabel) 'e'
      gamma <- newTyVar 'a'
      s     <- varBindRow alpha $ TRowExtend newLabel gamma beta
      return (gamma, apply s $ TRowExtend label fieldTy beta, s)
  | otherwise   = do
      (fieldTy', rowTail', s) <- rewriteRow rowTail newLabel
      return (fieldTy', TRowExtend label fieldTy rowTail', s)
rewriteRow ty _ = error $ "Unexpected type: " ++ show ty

-- | type-inference
ti :: TypeEnv -> Exp -> TI (Subst, Type, Effect)
ti (TypeEnv env) (EVar n) =
  case M.lookup n env of
    Nothing -> throwError $ "unbound variable: "++n
    Just sigma -> do
      t   <- instantiate sigma
      eff <- newEffect
      return (nullSubst, t, eff)
ti env (EPrim prim) = do
  t   <- tiPrim prim
  eff <- newEffect
  return (nullSubst, t, eff)
ti env (EAbs n e) = do
  tv <- newTyVar 'a'
  let TypeEnv env' = remove env n
      env'' = TypeEnv (env' `M.union` (M.singleton n (Scheme [] tv)))
  (s1, t1, eff2) <- ti env'' e
  eff <- newEffect
  return (s1, TFun (apply s1 tv) eff2 t1, eff)
ti env (EApp e1 e2) = do
  (s1, t1, eff1) <- ti env e1
  (s2, t2, eff2) <- ti (apply s1 env) e2
  tv <- newTyVar 'a'
  s3 <- unify (apply s2 t1) (TFun t2 eff2 tv)
  s4 <- unify (apply (s3 `composeSubst` s2)  eff1) (apply s3 eff2)
  return ( foldr1 composeSubst [s4, s3, s2 ,s1]
         , apply (s4 `composeSubst` s3) tv
         , apply (s4 `composeSubst` s3) eff2
         )
ti env (ELet x e1 e2) = do
  (s1, t1, eff1) <- ti env e1
  s2 <- unify eff1 emptyEff
  let TypeEnv env' = remove env x
      scheme = generalise (apply (s2 `composeSubst` s1) env) t1
      env''  = TypeEnv (M.insert x scheme env')
  (s3, t2, eff2) <- ti (apply (s2 `composeSubst` s1) env'') e2
  return (s3 `composeSubst` s2 `composeSubst` s1, t2, eff2)

tiPrim :: Prim -> TI Type
tiPrim p = case p of
  Unit                   -> return TUnit
  (Int _)                -> return TInt
  (Bool _)               -> return TBool
  (Str _)                -> return TStr
  Add                    -> do
    eff1 <- newEffect
    eff2 <- newEffect
    return $ TFun TInt eff1 (TFun TInt eff2 TInt)
  Div                    -> do
    eff1 <- newEffect
    eff2 <- TRowExtend "par" TUnit <$> newEffectWith (lacks "par")
    return $ TFun TInt eff1 (TFun TInt eff2 TInt)
  Catch                  -> do
    t1   <- newTyVar 'a'
    eff1 <- newEffect
    eff2 <- newEffectWith (lacks "par")
    let action  = TFun TUnit (TRowExtend "par" TUnit eff2) t1
        handler = TFun TUnit eff2 t1
    return $ TFun action eff1 (TFun handler eff2 t1)
  Total                  -> do
    t1   <- newTyVar 'a'
    eff1 <- newEffectWith (lacks "par")
    return $ TFun t1 eff1 t1
  Print                  -> do
    t1   <- newTyVar 'a'
    eff1 <- newEffect
    eff2 <- TRowExtend "io" TUnit <$> newEffectWith (lacks "io")
    return $ TFun TStr eff1 (TFun t1 eff2 t1)
  Pure                   -> do
    t1   <- newTyVar 'a'
    eff1 <- newEffectWith (lacks "io")
    return $ TFun t1 eff1 t1


typeInference :: M.Map String Scheme -> Exp -> TI (Type, Effect)
typeInference env e = do
  (s, t, eff) <- ti (TypeEnv env) e
  return (apply s t, apply s eff)

--  | decompose a row-type into its constituent parts
toList :: Type -> ([(Label, Type)], Maybe TyVar)
toList (TVar v)           = ([], Just v)
toList TRowEmpty          = ([], Nothing)
toList (TRowExtend l t r) = let (ls, mv) = toList r
                            in ((l, t):ls, mv)
lacks :: Label -> Constraint
lacks = S.singleton

none :: Constraint
none = S.empty


----------------------------------------------------------------------
-- Examples

e1 = ELet "id" (EAbs "x" (EVar "x")) (EVar "id")
e2 = EAbs "x" (EApp (EApp (EPrim Div) (EPrim $ Int 1)) (EVar "x"))
e3 = ELet "f" e2 $
       EApp (EApp (EPrim Catch) (EAbs "_" (EApp (EVar "f") (EPrim $ Int 0))))
            (EAbs "_" (EPrim $ Int 0))
e4 = EAbs "x" (EApp (EApp (EPrim Print) (EPrim $ Str "x is ")) (EVar "x"))
e5 = ELet "f" e2 (EApp (EPrim Pure) (EApp (EVar "f") (EPrim $ Int 0)))
e6 = ELet "f" e2 (EApp (EPrim Total) (EApp (EVar "f") (EPrim $ Int 42)))
e7 = ELet "f" e4 (EApp (EPrim Pure) (EApp (EVar "f") (EPrim $ Int 42)))
e8 = ELet "f" e2 (EApp (EVar "f") (EApp (EVar "f") (EPrim $ Int 0)))

test :: Exp -> IO ()
test e = do
  (res,_) <- runTI $ typeInference M.empty e
  case res of
    Left err -> putStrLn $ show e ++ " :: error: " ++ err
    Right (t,_eff) -> putStrLn $ show e ++ " :: " ++ show (generalise (TypeEnv M.empty) t)

main :: IO ()
main = do
  mapM test [ e1, e2, e3, e4, e5, e6, e7, e8 ]
  return ()


------------------------------------------------------------
-- Pretty-printing

instance IsString Doc where
  fromString = text

instance Show Type where
  showsPrec _ x = shows $ ppType x

ppType :: Type -> Doc
ppType (TVar v)       = text $ tyvarName v
ppType TUnit          = parens empty
ppType TInt           = "Int"
ppType TBool          = "Bool"
ppType TStr           = "String"
ppType (TFun t eff s) = ppParenType t <+> "->" <+> ppEffect eff <+> ppType s
ppType _ = error "Unexpected type"

ppParenType :: Type -> Doc
ppParenType t =
  case t of
    TFun {} -> parens $ ppType t
    _       -> ppType t

ppEffect :: Effect -> Doc
ppEffect r = braces $ (hsep $ punctuate comma $ map ppEntry ls)
               <> maybe empty (ppRowTail ls) mv
  where
    (ls, mv)       = toList r
    ppRowVar r     = text (tyvarName r)
    ppRowTail [] r = ppRowVar r
    ppRowTail _  r = space <> "|" <+> ppRowVar r
    ppEntry (l, t) = case t of
      TUnit -> text l
      _     -> text l <+> "=" <+> ppType t

instance Show Exp where
  showsPrec _ x = shows $ ppExp x

ppExp :: Exp -> Doc
ppExp (EVar name)     = text name
ppExp (EPrim prim)    = ppPrim prim
ppExp (ELet x b body) = "let" <+> text x <+> "=" <+>
                         ppExp b <+> "in" <//>
                         indent 2 (ppExp body)
ppExp (EApp e1 e2)    = ppExp e1 <+> ppParenExp e2
ppExp (EAbs n e)      = char '\\' <> text n <+> "->" <+> ppExp e

ppParenExp :: Exp -> Doc
ppParenExp t =
  case t of
    ELet {} -> parens $ ppExp t
    EApp {} -> parens $ ppExp t
    EAbs {} -> parens $ ppExp t
    _       -> ppExp t

instance Show Prim where
    showsPrec _ x = shows $ ppPrim x

ppPrim :: Prim -> Doc
ppPrim Unit               = "()"
ppPrim (Int i)            = integer i
ppPrim (Bool b)           = if b then "True" else "False"
ppPrim (Str s)            = "\"" <> text s <> "\""
ppPrim Add                = "(+)"
ppPrim Sub                = "(-)"
ppPrim Mul                = "(*)"
ppPrim Div                = "(/)"
ppPrim Catch              = "catch"
ppPrim Total              = "total"
ppPrim Print              = "print"
ppPrim Pure               = "pure"

instance Show Scheme where
  showsPrec _ x = shows $ ppScheme x

ppScheme :: Scheme -> Doc
ppScheme (Scheme vars t) =
  "forall" <+> hcat (punctuate space $ map (text . tyvarName) vars) <> "."
           <+> parens (hcat $ punctuate comma $ concatMap ppConstraint vars) <+> "=>"
           <+> ppType t
  where
    ppConstraint :: TyVar -> [Doc]
    ppConstraint (TyVar n k c) =
      case k of
        Star            -> []
        Row | null ls   -> []
            | otherwise -> [hcat (punctuate "\\" $ text n : map text ls)]
      where
        ls = S.toList c
