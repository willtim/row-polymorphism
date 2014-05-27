----------------------------------------------------------------------
-- Polymorphic Extensible Records with Scoped labels
--
-- See "Extensible Records with Scoped labels" by Daan Leijen
-- Based on code from "Algorithm W Step-by-Step" by Martin Grabmuller
----------------------------------------------------------------------

{-# LANGUAGE TupleSections, OverloadedStrings #-}

module AlgorithmW_Records where

import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S

import Control.Applicative ((<$>))
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
  = Int Integer
  | Bool Bool
  | Cond
  | RecordSelect Label
  | RecordExtend Label
  | RecordRestrict Label
  | RecordEmpty
    deriving (Eq, Ord)

data Type
  = TVar Name
  | TInt
  | TBool
  | TFun Type Type
  | TRecord Type
  | TRowEmpty
  | TRowExtend Label Type Type
    deriving (Eq, Ord)

data Scheme = Scheme [Name] Type

class Types a where
  ftv :: a -> S.Set Name -- ^ free type variables
  apply :: Subst -> a -> a

instance Types Type where
  ftv (TVar n) = S.singleton n
  ftv TInt = S.empty
  ftv TBool = S.empty
  ftv (TFun t1 t2) = ftv t1 `S.union` ftv t2
  ftv (TRecord t) = ftv t
  ftv TRowEmpty = S.empty
  ftv (TRowExtend l t r) = ftv r `S.union` ftv t
  apply s (TVar n) = case M.lookup n s of
                       Nothing -> TVar n
                       Just t -> t
  apply s (TFun t1 t2) = TFun (apply s t1) (apply s t2)
  apply s (TRecord t) = TRecord (apply s t)
  apply s (TRowExtend l t r) = TRowExtend l (apply s t) (apply s r)
  apply s t = t

instance Types Scheme where
  ftv (Scheme vars t) = (ftv t) S.\\ (S.fromList vars)
  apply s (Scheme vars t) = Scheme vars (apply (foldr M.delete s vars) t)

instance Types a => Types [a] where
  apply s = map (apply s)
  ftv l = foldr S.union S.empty (map ftv l)

type Subst = M.Map Name Type

nullSubst :: Subst
nullSubst = M.empty

composeSubst :: Subst -> Subst -> Subst
composeSubst s1 s2 = (M.map (apply s1) s2) `M.union` s1

newtype TypeEnv = TypeEnv (M.Map Name Scheme)

remove :: TypeEnv -> Name -> TypeEnv
remove (TypeEnv env) var = TypeEnv (M.delete var env)

instance Types TypeEnv where
  ftv (TypeEnv env) = ftv (M.elems env)
  apply s (TypeEnv env) = TypeEnv (M.map (apply s) env)

-- | generalize abstracts a type over all type variables which are free
-- in the type but not free in the given type environment.
generalize :: TypeEnv -> Type -> Scheme
generalize env t = Scheme vars t
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
newTyVar prefix = do
  s <- get
  put s {tiSupply = tiSupply s + 1 }
  return (TVar $ prefix : show (tiSupply s))

-- | The instantiation function replaces all bound type variables in a
-- type scheme with fresh type variables.
instantiate :: Scheme -> TI Type
instantiate (Scheme vars t) = do
  nvars <- mapM (\(p:_) -> newTyVar p) vars
  let s = M.fromList (zip vars nvars)
  return $ apply s t

unify :: Type -> Type -> TI Subst
unify (TFun l r) (TFun l' r') = do
  s1 <- unify l l'
  s2 <- unify (apply s1 r) (apply s1 r')
  return $ s2 `composeSubst` s1
unify (TVar u) t = varBind u t
unify t (TVar u) = varBind u t
unify TInt TInt = return nullSubst
unify TBool TBool = return nullSubst
unify (TRecord row1) (TRecord row2) = unify row1 row2
unify TRowEmpty TRowEmpty = return nullSubst
unify (TRowExtend label1 fieldTy1 rowTail1) row2@TRowExtend{} = do
  (fieldTy2, rowTail2, theta1) <- rewriteRow row2 label1
  -- ^ apply side-condition to ensure termination
  case snd $ toList rowTail1 of
    Just tv | M.member tv theta1 -> throwError "recursive row type"
    _ -> do
      theta2 <- unify (apply theta1 fieldTy1) (apply theta1 fieldTy2)
      let s = theta2 `composeSubst` theta1
      theta3 <- unify (apply s rowTail1) (apply s rowTail2)
      return $ theta3 `composeSubst` s
unify t1 t2 = throwError $ "types do not unify: " ++ show t1 ++ " vs. " ++ show t2

varBind :: String -> Type -> TI Subst
varBind u t
  | t == TVar u        = return nullSubst
  | u `S.member` ftv t = throwError $ "occur check fails: " ++ " vs. " ++ show t
  | otherwise          = return $ M.singleton u t

rewriteRow :: Type -> Label -> TI (Type, Type, Subst)
rewriteRow TRowEmpty newLabel = throwError $ "label " ++ newLabel ++ " cannot be inserted"
rewriteRow (TRowExtend label fieldTy rowTail) newLabel
  | newLabel == label     = return (fieldTy, rowTail, nullSubst) -- ^ nothing to do
  | TVar alpha <- rowTail = do
      beta  <- newTyVar 'r'
      gamma <- newTyVar 'a'
      return ( gamma
             , TRowExtend label fieldTy beta
             , M.singleton alpha $ TRowExtend newLabel gamma beta
             )
  | otherwise   = do
      (fieldTy', rowTail', s) <- rewriteRow rowTail newLabel
      return ( fieldTy'
             , TRowExtend label fieldTy rowTail'
             , s
             )
rewriteRow ty _ = error $ "Unexpected type: " ++ show ty

-- | type-inference
ti :: TypeEnv -> Exp -> TI (Subst, Type)
ti (TypeEnv env) (EVar n) =
  case M.lookup n env of
    Nothing -> throwError $ "unbound variable: "++n
    Just sigma -> do
      t <- instantiate sigma
      return (nullSubst, t)
ti env (EPrim prim) = (nullSubst,) <$> tiPrim prim
ti env (EAbs n e) = do
  tv <- newTyVar 'a'
  let TypeEnv env' = remove env n
      env'' = TypeEnv (env' `M.union` (M.singleton n (Scheme [] tv)))
  (s1, t1) <- ti env'' e
  return (s1, TFun (apply s1 tv) t1)
ti env (EApp e1 e2) = do
  (s1, t1) <- ti env e1
  (s2, t2) <- ti (apply s1 env) e2
  tv <- newTyVar 'a'
  s3 <- unify (apply s2 t1) (TFun t2 tv)
  return (s3 `composeSubst` s2 `composeSubst` s1, apply s3 tv)
ti env (ELet x e1 e2) = do
  (s1, t1) <- ti env e1
  let TypeEnv env' = remove env x
      scheme = generalize (apply s1 env) t1
      env''  = TypeEnv (M.insert x scheme env')
  (s2, t2) <- ti (apply s1 env'') e2
  return (s2 `composeSubst` s1, t2)

tiPrim :: Prim -> TI Type
tiPrim p = case p of
  (Int _)                -> return TInt
  (Bool _)               -> return TBool
  Cond                   -> do
    a <- newTyVar 'a'
    return $ TFun TBool (TFun a (TFun a a))
  RecordEmpty            -> return $ TRecord TRowEmpty
  (RecordSelect label)   -> do
    a <- newTyVar 'a'
    r <- newTyVar 'r'
    return $ TFun (TRecord $ TRowExtend label a r) a
  (RecordExtend label)   -> do
    a <- newTyVar 'a'
    r <- newTyVar 'r'
    return $ TFun a (TFun (TRecord r) (TRecord $ TRowExtend label a r))
  (RecordRestrict label) -> do
    a <- newTyVar 'a'
    r <- newTyVar 'r'
    return $ TFun (TRecord $ TRowExtend label a r) (TRecord r)

typeInference :: M.Map String Scheme -> Exp -> TI Type
typeInference env e = do
  (s, t) <- ti (TypeEnv env) e
  return $ apply s t

toList :: Type -> ([(Label, Type)], Maybe Name)
toList (TVar r)           = ([], Just r)
toList TRowEmpty          = ([], Nothing)
toList (TRowExtend l t r) = let (ls, mv) = toList r
                            in ((l, t):ls, mv)


----------------------------------------------------------------------
-- Examples

e1 = EApp (EApp (EPrim $ RecordExtend "y") (EPrim $ Int 2)) (EPrim RecordEmpty)
e2 = EApp (EApp (EPrim $ RecordExtend "x") (EPrim $ Int 1)) e1
e3 = EApp (EPrim $ RecordSelect "y") e2
e4 = ELet "f" (EAbs "r" (EApp (EPrim $ RecordSelect "x") (EVar "r"))) (EVar "f")
e5 = EAbs "r" (EApp (EPrim $ RecordSelect "x") (EVar "r"))

-- Row tail unification soundness
-- \r -> if True then { x = 1 | r } else { y = 2 | r }
e6 = EAbs "r" $ app (EPrim Cond)
       [ EPrim $ Bool True
       , app (EPrim $ RecordExtend "x") [EPrim $ Int 1, EVar "r"]
       , app (EPrim $ RecordExtend "y") [EPrim $ Int 2, EVar "r"]
       ]

app :: Exp -> [Exp] -> Exp
app f = foldl EApp f

test :: Exp -> IO ()
test e = do
  (res,_) <- runTI $ typeInference M.empty e
  case res of
    Left err -> putStrLn $ show e ++ " :: error: " ++ err
    Right t  -> putStrLn $ show e ++ " :: " ++ show t

main :: IO ()
main = do
  mapM test [ e1, e2, e3, e4, e5, e6 ]
  return ()


------------------------------------------------------------
-- Pretty-printing

instance IsString Doc where
  fromString = text

instance Show Type where
  showsPrec _ x = shows $ ppType x

ppType :: Type -> Doc
ppType (TVar n)    = text n
ppType TInt        = "Int"
ppType TBool       = "Bool"
ppType (TFun t s)  = ppParenType t <+> "->" <+> ppType s
ppType (TRecord r) = braces $ (hsep $ punctuate comma $ map ppEntry ls)
                              <> maybe empty (ppRowTail ls) mv
  where
    (ls, mv)       = toList r
    ppRowTail [] r = text r
    ppRowTail _  r = space <> "|" <+> text r
    ppEntry (l, t) = text l <+> "=" <+> ppType t
ppType _ = error "Unexpected type"

ppParenType :: Type -> Doc
ppParenType t =
  case t of
    TFun {} -> parens $ ppType t
    _       -> ppType t

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
ppPrim (Int i)            = integer i
ppPrim (Bool b)           = if b then "True" else "False"
ppPrim Cond               = "(_?_:_)"
ppPrim (RecordSelect l)   = "(_." <> text l <> ")"
ppPrim (RecordExtend l)   = "{"   <> text l <>  "=_|_}"
ppPrim (RecordRestrict l) = "(_-" <> text l <> ")"
ppPrim RecordEmpty        = "{}"

instance Show Scheme where
  showsPrec _ x = shows $ ppScheme x

ppScheme :: Scheme -> Doc
ppScheme (Scheme vars t) =
  "forall" <+> hcat (punctuate comma $ map text vars) <> "." <+> ppType t
