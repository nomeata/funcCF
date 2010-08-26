{-|
 - This module calculates the exact control graph by evaluating a "CPSScheme"
 - program, following the definitions in Olin Shivers\' \"Control-Flow
 - Analysis of Higher-Order Languages\".
 -}
{-# LANGUAGE TypeOperators #-}
module ExCF where

import Data.Map (empty, (!))

import CPSScheme
import Common

-- * Types

-- | A closure is a lambda expression bound to a binding environment
type Closure = (Lambda, BEnv)

-- | A contour is an identifier for the contours (or dynamic frames) generated
-- at each call of a lambda expression 
type Contour = Integer

-- | A binding environment maps the labels of 'Lambda' and 'Let' bindings to the
-- innermost contour generated for these expressions
type BEnv = Label :⇀  Contour

-- | A variable environment maps variable names together with a contour to a
-- value. The second parameter is required to allow for different, shadowed
-- bindings of the same variable to coexist.
type VEnv = Var :× Contour :⇀ D

-- | A semantical value can either be
data D = DI Const   -- ^ A constant
       | DC Closure -- ^ A closed lambda expression
       | DP Prim    -- ^ A primitive value
       | Stop       -- ^ The special continuation passed to the outermost
                    --   lambda of a program
    deriving (Show)

-- | The origin of an edge in the control graph is a call position bundled with
-- the binding environment at that point.
type CCtxt = Label :× BEnv

-- | The resulting control flow graph has edges from call sites (annotated by
-- the current binding environment) to functions (e.g. lambdas with closure,
-- primitive operations, or 'Stop')
type CCache = CCtxt :⇀ D

-- | The result of evaluating a program is the control flow graph.
type Ans = CCache

-- * Evaluation functions

-- | evalCPS evaluates a whole program, by initializing the envirnoments and
--   passing the Stop continuation to the outermost lambda
evalCPS :: Prog -> Ans
evalCPS lam = evalF f [Stop] ve 0
 where  ve = empty
        β = empty
        f = evalV (L lam) β ve

-- | evalC (called A by Shivers) evaluates a syntactical value to a semantical
--   piece of data.
evalV :: Val -> BEnv -> VEnv -> D
evalV (C _ int) β ve = DI int
evalV (P prim) β ve = DP prim
evalV (R _ binder var) β ve = ve ! (var, β ! binder)
evalV (L lam) β ve = DC (lam, β)

-- | evalF evaluates a function call, distinguishing between lambda
--   expressions, primitive operations and the special Stop continuation. It
--   calles 'evalC' for the function bodies.
evalF :: D -> [D] -> VEnv -> Contour -> Ans
evalF (DC (Lambda lab vs c, β)) as ve b
        | length as /= length vs = error $ "Wrong number of arguments to lambda expression " ++ show lab
        | otherwise = evalC c β' ve' b
            where β' = β `upd` [lab ↦ b]
                  ve' = ve `upd` zipWith (\v a -> (v,b) ↦ a) vs as

evalF (DP (Plus c)) [DI a1, DI a2, cont] ve b = evalF cont [DI (a1 + a2)] ve b'
                                              `upd` [ (c, β) ↦ cont ]
    where b' = succ b
          β  = empty `upd` [ c ↦  b ]
evalF (DP (If ct cf)) [DI v, contt, contf] ve b
    | v /= 0 =  evalF contt [] ve b' `upd` [ (ct, βt) ↦ contt ]
    | v == 0 =  evalF contf [] ve b' `upd` [ (cf, βf) ↦ contf ]
    where b' = succ b
          βt  = empty `upd` [ ct ↦  b ]
          βf  = empty `upd` [ cf ↦  b ]

evalF Stop [DI int] _ _ = empty 

evalF Stop _ _ _ = error $ "Stop called with wrong number or types of arguments"
evalF (DP prim) _ _ _ = error $ "Primop " ++ show prim ++ " called with wrong arguments"
evalF (DI int) _ _ _ = error $ "Cannot treat a constant value as a function"

-- | evalC evaluates the body of a function, which can either be an application
--   (which is then evaluated using 'evalF') or a 'Let' statement.
evalC :: Call -> BEnv -> VEnv -> Contour -> Ans
evalC (App lab f vs) β ve b = evalF f' as ve b' `upd` [ (lab,β) ↦ f' ]
  where f' = evalV f β ve
        as = map (\v -> evalV v β ve) vs
        b' = succ b

evalC (Let lab ls c') β ve b = evalC c' β' ve' b'
  where b' = succ b
        β' = β `upd` [lab ↦ b']
        ve' = ve `upd` [(v,b') ↦ evalV (L l) β' ve | (v,l) <- ls]
