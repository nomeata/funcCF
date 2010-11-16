{-|
This module calculates an abstract control graph by evaluating a "CPSScheme"
program, following the definitions in Olin Shivers\' \"Control-Flow
Analysis of Higher-Order Languages\".
 -}
{-# LANGUAGE TypeOperators #-}
module AbsCF where

import Data.Map (empty, unions, fromList, toList, (!))
import Control.Monad.State
import Control.Applicative ((<$>))
import Data.Set (Set)
import qualified Data.Set as S

import CPSScheme
import Common

-- * Types

-- | A closure is a lambda expression bound to a binding environment
type Closure c = (Lambda, BEnv c)

-- | The abstract semantics are parametrized by a (finite) set of contours.
-- Here, this is modeled via a type class.
class (Show c, Eq c, Ord c) => Contour c where
    initial :: c -- ^ The initial contour, used by evalCPS, but not used
    nb :: c -> Label -> c -- ^ Generating a new contour. This method has access
                          -- to the label of the current call site, in case it
                          -- wants to record this information. 

-- | A possible contour set, the singleton set. Shivers calls this 0CFA, but in
-- Haskell, types and constructor names have to start with an upper case
-- letter.
newtype CFA0 = CFA0 ()
    deriving (Show, Eq, Ord)

instance Contour CFA0 where
    initial = CFA0 ()
    nb _ _ = CFA0 ()

-- | A more detailed contour set, remembering the call site. 
newtype CFA1 = CFA1 Label
    deriving (Show, Eq, Ord)

instance Contour CFA1 where
    initial = CFA1 (-1)
    nb _ l = CFA1 l

-- | A binding environment maps the labels of 'Lambda' and 'Let' bindings to the
-- innermost contour generated for these expressions
type BEnv c = Label :⇀ c

-- | A variable environment maps variable names together with a contour to a
-- value. The second parameter is required to allow for different, shadowed
-- bindings of the same variable to coexist.
type VEnv c = Var :× c :⇀ D c

-- | Here, we do not care about values any more, only about procedures:
data Proc c = PC (Closure c) -- ^ A closed lambda expression
            | PP Prim        -- ^ A primitive operation
            | Stop
    deriving (Show, Eq, Ord)


-- | For variables, we only remember the set of possible program values. We use
-- a list here instead of a set for the more convenient sytanx (list
-- comprehension etc.).
type D c = [Proc c]

-- | The origin of an edge in the control graph is a call position bundled with
-- the binding environment at that point.
type CCtxt c = Label :× BEnv c

-- | The resulting control flow graph has edges from call sites (annotated by
-- the current binding environment) to functions (e.g. lambdas with closure,
-- primitive operations, or 'Stop')
type CCache c = CCtxt c :⇀ D c

-- | The result of evaluating a program is an approximation to the control flow
-- graph.
type Ans c = CCache c

-- | The uncurried arguments of 'evalF'
type FState c = (Proc c, [D c], VEnv c, c)

-- | The uncurried arguments of 'evalC'
type CState c = (Call, BEnv c, VEnv c, c)

-- | We need memoization. This Data structure is used to remember all visited
-- arguments
type Memo c = Set (Either (FState c) (CState c))


-- * Evaluation functions

-- | evalCPS evaluates a whole program, by initializing the envirnoments and
--   passing the Stop continuation to the outermost lambda
evalCPS :: Contour c => Prog -> Ans c
evalCPS lam = evalState (evalF (f, [[Stop]], ve, initial)) S.empty
 where  ve = empty
        β = empty
        [f] = evalV (L lam) β ve

-- | Variants fixing the coutour
evalCPS_CFA0 :: Prog -> Ans CFA0
evalCPS_CFA0 = evalCPS

evalCPS_CFA1 :: Prog -> Ans CFA1
evalCPS_CFA1 = evalCPS

-- | evalC (called A by Shivers) evaluates a syntactical value to a semantical
--   piece of data.
evalV :: Contour c => Val -> BEnv c -> VEnv c -> D c
evalV (C _ int) β ve = []
evalV (P prim) β ve = [PP prim]
evalV (R _ var) β ve = ve ! (var, β ! binder var)
evalV (L lam) β ve = [PC (lam, β)]

-- | evalF evaluates a function call, distinguishing between lambda
--   expressions, primitive operations and the special Stop continuation. It
--   calles 'evalC' for the function bodies.
--
--   Because we want to memoize the results of the recursive calls, and do not
--   want to separate that code, the that to be 
evalF :: Contour c => FState c -> State (Memo c) (Ans c)
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
            where b' = nb b c
                  β  = empty `upd` [ c ↦  b ]
        (PP (If ct cf), [_, contt, contf], ve, b)
            -> unionsM (
                [ evalF (cont,[],ve,bt') | cont <- contt ] ++
                [ evalF (cont,[],ve,bf') | cont <- contf ] )
            `upd'` [ (ct, βt) ↦ contt, (cf, βf) ↦ contf ]
            where bt' = nb b ct
                  bf' = nb b cf
                  βt  = empty `upd` [ ct ↦  b ]
                  βf  = empty `upd` [ cf ↦  b ]
        (Stop,[_],_,_) -> return empty 
        (Stop,_,_,_) -> error $ "Stop called with wrong number or types of arguments"
        (PP prim,_,_,_) -> error $ "Primop " ++ show prim ++ " called with wrong arguments"

-- | evalC evaluates the body of a function, which can either be an application
--   (which is then evaluated using 'evalF') or a 'Let' statement.
evalC :: Contour c => CState c -> State (Memo c) (Ans c)
evalC args = do
    seen <- gets (S.member (Right args))
    if seen then return empty else do
    modify (S.insert (Right args))
    case args of
        (App lab f vs, β, ve, b)
            -> unionsM [evalF (f',as,ve,b') | f' <- fs ] `upd'` [ (lab,β) ↦ fs ]
            where fs = evalV f β ve
                  as = map (\v -> evalV v β ve) vs
                  b' = nb b lab
        (Let lab ls c', β, ve, b)
            -> evalC (c',β',ve',b')
            where b' = nb b lab
                  β' = β `upd` [lab ↦ b']
                  ve' = ve `upd` [(v,b') ↦ evalV (L l) β' ve | (v,l) <- ls]

-- | For the visualization, we need a list of edges from Label to Label. TODO: Handle STOP
graphToEdgelist :: Show c => Ans c -> [Label :× Label]
graphToEdgelist = concat . map go . toList
  where go ((l,_),ds) = concat $ map go' ds
          where go' Stop = []
                go' (PP (Plus l')) = [(l,l')]
                go' (PP (If l' _)) = [(l,l')]
                go' (PC (Lambda l' _ _ , _)) = [(l,l')]

