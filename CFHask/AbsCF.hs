{-|
 - This module calculates an abstract control graph by evaluating a "CPSScheme"
 - program, following the definitions in Olin Shivers\' \"Control-Flow
 - Analysis of Higher-Order Languages\".
 -}
{-# LANGUAGE TypeOperators #-}
module AbsCF where

import Data.Map (empty, unions, fromList, (!))
import Control.Monad.State
import Control.Applicative ((<$>))
import Data.Set (Set)
import qualified Data.Set as S

import CPSScheme
import Common

-- * Types

-- | A closure is a lambda expression bound to a binding environment
type Closure = (Lambda, BEnv)

-- | A contour is an identifier for the contours (or dynamic frames) generated
-- at each call of a lambda expression. For the abstract semantics, this is
-- chosen to be a finite set.
type Contour = ()

-- | A binding environment maps the labels of 'Lambda' and 'Let' bindings to the
-- innermost contour generated for these expressions
type BEnv = Label :⇀  Contour

-- | A variable environment maps variable names together with a contour to a
-- value. The second parameter is required to allow for different, shadowed
-- bindings of the same variable to coexist.
type VEnv = Var :× Contour :⇀ D

-- | Here, we do not care about values any more, only about procedures:
data Proc = PC Closure -- ^ A closed lambda expression
          | PP Prim    -- ^ A primitive operation
          | Stop
    deriving (Show, Eq, Ord)


-- | For variables, we only remember the set of possible program values. We use
-- a list here instead of a set for the more convenient sytanx (list
-- comprehension etc.).
type D = [Proc]

-- | The origin of an edge in the control graph is a call position bundled with
-- the binding environment at that point.
type CCtxt = Label :× BEnv

-- | The resulting control flow graph has edges from call sites (annotated by
-- the current binding environment) to functions (e.g. lambdas with closure,
-- primitive operations, or 'Stop')
type CCache = CCtxt :⇀ D

-- | The result of evaluating a program is an approximation to the control flow
-- graph.
type Ans = CCache

-- | The uncurried arguments of 'evalF'
type FState = (Proc, [D], VEnv, Contour)

-- | The uncurried arguments of 'evalC'
type CState = (Call, BEnv, VEnv, Contour)

-- | We need memoization. This Data structure is used to remember all visited
-- arguments
type Memo = Set (Either FState CState)


-- * Evaluation functions

nb () = ()

-- | evalCPS evaluates a whole program, by initializing the envirnoments and
--   passing the Stop continuation to the outermost lambda
evalCPS :: Prog -> Ans
evalCPS lam = evalState (evalF (f, [[Stop]], ve, ())) S.empty
 where  ve = empty
        β = empty
        [f] = evalV (L lam) β ve

-- | evalC (called A by Shivers) evaluates a syntactical value to a semantical
--   piece of data.
evalV :: Val -> BEnv -> VEnv -> D
evalV (C _ int) β ve = []
evalV (P prim) β ve = [PP prim]
evalV (R _ binder var) β ve = ve ! (var, β ! binder)
evalV (L lam) β ve = [PC (lam, β)]

-- | evalF evaluates a function call, distinguishing between lambda
--   expressions, primitive operations and the special Stop continuation. It
--   calles 'evalC' for the function bodies.
--
--   Because we want to memoize the results of the recursive calls, and do not
--   want to separate that code, the that to be 
evalF :: FState -> State Memo Ans
evalF args = do
    seen <- gets (S.member (Left args))
    if seen then return empty else do
    modify (S.insert (Left args))
    case args of
        (PC (Lambda lab vs c, β), as, ve, b)
            -> if (length as /= length vs)
               then error $ "Wrong number of arguments to lambda expression " ++ show lab
               else evalC (c,β',ve',b)
            where β' = β `upd` [lab ↦ b]
                  ve' = ve `upd` zipWith (\v a -> (v,b) ↦ a) vs as
        (PP (Plus c), [_, _, conts], ve, b)
            -> unionsM [ evalF (cont,[[]],ve,b') | cont <- conts ] `upd'` [ (c, β) ↦ conts ]
            where b' = nb b
                  β  = empty `upd` [ c ↦  b ]
        (PP (If ct cf), [_, contt, contf], ve, b)
            -> unionsM [ evalF (cont,[],ve,b') | cont <- contt ++ contf ]
            `upd'` [ (ct, βt) ↦ contt, (cf, βf) ↦ contf ]
            where b' = nb b
                  βt  = empty `upd` [ ct ↦  b ]
                  βf  = empty `upd` [ cf ↦  b ]
        (Stop,[_],_,_) -> return empty 
        (Stop,_,_,_) -> error $ "Stop called with wrong number or types of arguments"
        (PP prim,_,_,_) -> error $ "Primop " ++ show prim ++ " called with wrong arguments"

-- | evalC evaluates the body of a function, which can either be an application
--   (which is then evaluated using 'evalF') or a 'Let' statement.
evalC :: CState -> State Memo Ans
evalC args = do
    seen <- gets (S.member (Right args))
    if seen then return empty else do
    modify (S.insert (Right args))
    case args of
        (App lab f vs, β, ve, b)
            -> unionsM [evalF (f',as,ve,b') | f' <- fs ] `upd'` [ (lab,β) ↦ fs ]
            where fs = evalV f β ve
                  as = map (\v -> evalV v β ve) vs
                  b' = nb b
        (Let lab ls c', β, ve, b)
            -> evalC (c',β',ve',b')
            where b' = nb b
                  β' = β `upd` [lab ↦ b']
                  ve' = ve `upd` [(v,b') ↦ evalV (L l) β' ve | (v,l) <- ls]
