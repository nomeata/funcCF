{-|
 - Here, a standard semantic for the language defined in "CPSScheme" is
 - implemented, following the definitions in Olin Shivers\' \"Control-Flow
 - Analysis of Higher-Order Languages\".
 -}
{-# LANGUAGE TypeOperators #-}
module Eval where

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

-- | The result of evaluating a program can be either an error or a constant
--   value.
type Ans = Either String Const

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
evalV (P _ prim) β ve = DP prim
evalV (R _ binder var) β ve = ve ! (var, β ! binder)
evalV (L lam) β ve = DC (lam, β)

-- | evalF evaluates a function call, distinguishing between lambda
--   expressions, primitive operations and the special Stop continuation. It
--   calles 'evalC' for the function bodies.
evalF :: D -> [D] -> VEnv -> Contour -> Ans
evalF (DC (Lambda lab vs c, β)) as ve b
        | length as /= length vs = Left $ "Wrong number of arguments to lambda expression " ++ show lab
        | otherwise = evalC c β' ve' b
            where β' = β `upd` [lab ↦ b]
                  ve' = ve `upd` zipWith (\v a -> (v,b) ↦ a) vs as

evalF (DP Plus) [DI a1, DI a2, cont] ve b = evalF cont [DI (a1 + a2)] ve b'
    where b' = succ b
evalF (DP If) [DI v, cont1, cont2] ve b = evalF (if v /= 0 then cont1 else cont2) [] ve b'
    where b' = succ b

evalF Stop [DI int] _ _ = Right int 

evalF Stop _ _ _ = Left $ "Stop called with wrong number or types of arguments"
evalF (DP prim) _ _ _ = Left $ "Primop " ++ show prim ++ " called with wrong arguments"
evalF (DI int) _ _ _ = Left $ "Cannot treat a constant value as a function"

-- | evalC evaluates the body of a function, which can either be an application
--   (which is then evaluated using 'evalF') or a 'Let' statement.
evalC :: Call -> BEnv -> VEnv -> Contour -> Ans
evalC (App lab f vs) β ve b = evalF f' as ve b'
  where f' = evalV f β ve
        as = map (\v -> evalV v β ve) vs
        b' = succ b

evalC (Let lab ls c') β ve b = evalC c' β' ve' b'
  where b' = succ b
        β' = β `upd` [lab ↦ b']
        ve' = ve `upd` [(v,b') ↦ evalV (L l) β' ve | (v,l) <- ls]
