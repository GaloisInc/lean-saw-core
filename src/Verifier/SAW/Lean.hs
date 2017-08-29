{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}

{- |
Module      : Verifier.SAW.Lean
Copyright   : Galois, Inc. 2017
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.Lean
  ( lean_extract
  ) where

import qualified Data.Char as Char
import Data.Map (Map)
import qualified Data.Map as Map
--import Data.Word (Word32)
--import Control.Monad (foldM)
import Control.Monad.State

import Verifier.SAW.SharedTerm
--import Verifier.SAW.Constant (scConstant)
import Verifier.SAW.TypedAST (preludeName, mkSort)

import qualified Language.Lean as Lean

-- | All-in-one function for loading a Lean module and extracting a declaration.
lean_extract :: SharedContext -> String -> String -> IO Term
lean_extract sc modname name =
  do env0 <- Lean.standardEnv Lean.trustHigh
     st <- Lean.mkStandardIOState
     opts <- Lean.getStateOptions st
     putStrLn $ "Options: " ++ show opts
     env <- Lean.envImport st env0 (Lean.fromList [parseName modname])
     --putStrLn "Env:"
     --Lean.forEnvDecl_ env (\decl -> print (Lean.declName decl))
     decl <-
       case Lean.envLookupDecl (parseName name) env of
         Nothing -> fail "lean_extract: name not found"
         Just decl -> return decl
     t <- evalStateT (importDecl sc env [] decl) Map.empty
     putStrLn "Result term:"
     putStrLn (scPrettyTerm defaultPPOpts t)
     return t

parseName :: String -> Lean.Name
parseName = go Lean.anonymousName []
  where
    addPart n p
      | all Char.isDigit p = Lean.nameAppendIndex n (read p)
      | otherwise          = Lean.nameAppend n p
    go n p [] = addPart n (reverse p)
    go n p ('.' : cs) = go (addPart n (reverse p)) [] cs
    go n p (c : cs) = go n (c : p) cs

declBody :: Lean.Decl -> Maybe Lean.Expr
declBody decl =
  case Lean.declView decl of
    Lean.Constant         -> Nothing
    Lean.Axiom            -> Nothing
    Lean.Definition e _ _ -> Just e
    Lean.Theorem e _      -> Just e

importDecl ::
    SharedContext ->
    Lean.Env ->
    [Term] ->
    Lean.Decl ->
    StateT (Map Lean.Name Term) IO Term
importDecl sc env tys decl =
  case declBody decl of
    Nothing ->
      do t <- importExpr sc env tys (Lean.declType decl)
         t' <- lift $ scFreshGlobal sc (Lean.nameToString name) t
         modify (Map.insert name t')
         return t'
    Just e ->
      do t <- importExpr sc env tys e
         let tc = Lean.typechecker env
         ty <- importExpr sc env tys (Lean.inferType tc e)
         --t' <- lift $ scConstant sc (Lean.nameToString name) t
         lift $ putStrLn $ "Constant " ++ show (Lean.nameToString name)
         lift $ putStrLn $ " : " ++ (scPrettyTerm defaultPPOpts ty)
         lift $ putStrLn $ " = " ++ (scPrettyTerm defaultPPOpts t)
         t' <- lift $ scTermF sc (Constant (Lean.nameToString name) t ty)
         modify (Map.insert name t')
         return t'
  where
    name = Lean.declName decl
importExpr ::
    SharedContext ->
    Lean.Env ->
    [Term] ->
    Lean.Expr ->
    StateT (Map Lean.Name Term) IO Term
importExpr sc env tys expr = do
  --lift $ putStrLn $ "importExpr:\n  " ++ show expr
  case Lean.exprView expr of
    Lean.ExprVar i ->
      do lift $ scLocalVar sc (fromIntegral i)
    Lean.ExprSort _ {-Univ-} ->
      do lift $ scSort sc (mkSort 0) -- currently we assume everything is in Type0
    Lean.ExprConst name _univs ->
      do cache <- get
         case Map.lookup name cache of
           Just t -> return t
           Nothing ->
             case Lean.envLookupDecl name env of
               Nothing -> fail $ "importExpr: invalid constant name " ++
                          show (Lean.nameToString name)
               Just decl -> importDecl sc env tys decl
    Lean.ExprLocal _ {-LocalConst-} ->
      do unimplemented "ExprLocal"
    Lean.ExprMeta {} {-Name Expr-} ->
      do unimplemented "ExprMeta"
    Lean.ExprApp e1 e2 ->
      do t1 <- importExpr sc env tys e1
         t2 <- importExpr sc env tys e2
         lift $ scApply sc t1 t2
    Lean.ExprLambda _bk name e1 e2 ->
      do t1 <- importExpr sc env tys e1
         t2 <- importExpr sc env (t1 : tys) e2
         lift $ scLambda sc (Lean.nameToString name) t1 t2
    Lean.ExprPi _bk name e1 e2 ->
      do t1 <- importExpr sc env tys e1
         t2 <- importExpr sc env (t1 : tys) e2
         lift $ scPi sc (Lean.nameToString name) t1 t2
    Lean.ExprMacro mdef exprs ->
      do lift $ putStrLn "importExpr ExprMacro"
         lift $ putStrLn (show mdef)
         lift $ putStrLn (show exprs)
         --let tc = Lean.typechecker env
         --let importType = importExpr sc env tys . Lean.inferType tc
         ts <- mapM (importExpr sc env tys) (Lean.toList exprs)
         --argTys <- lift $ mapM (scTypeOf' sc tys) ts
         --resTy <- importType expr
         --funTy <- lift $ scFunAll sc argTys resTy
         --f <- lift $ scFreshGlobal sc (Lean.macroDefToString mdef) funTy
         --lift $ scApplyAll sc f ts
         let ident = mkIdent preludeName (Lean.macroDefToString mdef)
         lift $ scCtorApp sc ident ts
  where
    unimplemented msg =
      fail $ unwords ["importExpr: Unimplemented", msg, Lean.exprToString expr]
