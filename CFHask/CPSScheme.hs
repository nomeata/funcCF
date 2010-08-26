{-|
  This module defines the syntax of the simple, continuation-passing-style
  functional language used here, as well as some examples.
-}
{-# LANGUAGE GeneralizedNewtypeDeriving, OverloadedStrings #-}
module CPSScheme where

import GHC.Exts( IsString(..) )

-- * The CPS styntax

-- | A program is defined as a lambda abstraction. The calling convention is
-- that the program has one paramater, the final continuation.
type Prog = Lambda

-- | Labels are used throughout the code to refer to various positions in the code.
--
-- Integers are used here, but they are wrapped in a newtype to hide them from
-- the implementation.
newtype Label = Label Integer
    deriving (Show, Num, Eq, Ord)

-- | Variable names are just strings. Again, they are wrapped so they can be
-- treated abstractly.
newtype Var = Var String
    deriving (IsString, Show, Eq, Ord)

-- | A lambda expression has a label, a list of abstract argument names and a body.
data Lambda = Lambda Label [Var] Call
    deriving (Show, Eq, Ord)

-- | The body of a lambda expression is either 
data Call = App Label Val [Val]
          -- ^ an application of a value to a list of arguments, or
          | Let Label [(Var, Lambda)] Call
          -- ^ it is the definition of a list of (potentially mutable
          -- recursive) lambda expression, defined for a nother call
          -- expression.
    deriving (Show, Eq, Ord)

-- | A value can either be
data Val = L Lambda          -- ^ a lambda abstraction,
         | R Label Label Var -- ^ a reference to a variable (which contains the
                             -- label of the binding position of the variable
                             -- for convenience),
         | C Label Const     -- ^ a constant value or
         | P Prim            -- ^ a primitive operation.
    deriving (Show, Eq, Ord)

instance IsString Val where
    fromString s = R noProg noProg (Var s)
instance Num Val where
    fromInteger i = C noProg i
    (+) = error "Do not use the Num Val instance"
    (*) = error "Do not use the Num Val instance"
    abs = error "Do not use the Num Val instance"
    signum = error "Do not use the Num Val instance"
    negate (C _ i) = (C noProg (-i))
    negate _ = error "Do not use the Num Val instance"


-- | As constants we only have integers.
type Const = Integer

-- | Primitive operations. The primitive operations are annotated by labels. These mark the (invisible) call sites that call the continuations, and are one per continuation.
data Prim = Plus Label -- ^ Integer addition. Expected parameters: two integers, one continuation.
          | If Label Label -- ^ Conditional branching. Expected paramters: one integer, one continuation to be called if the argument is nonzero, one continuation to be called if the argument is zero (“false”)
    deriving (Show, Eq, Ord)

-- * Smart constructors

-- | This converts code generated by the smart constructors to a fully
-- annotated 'CPSScheme' syntax tree
prog :: Lambda -> Prog
prog p = p

lambda :: [Var] -> Call -> Lambda
lambda = Lambda noProg

app :: Val -> [Val] -> Call
app = App noProg

let_ :: [(Var, Lambda)] -> Call -> Call
let_ = Let noProg

l :: Lambda -> Val
l = L

c :: Const -> Val
c = C noProg

plus :: Val
plus = P (Plus noProg)

if_ :: Val
if_ = P (If noProg noProg)

-- | Internal error value
noProg :: a
noProg = error "Smart constructors used without calling prog"

-- * Some example Programs

-- | Returns 0
ex1 :: Prog
ex1 = prog $ lambda ["cont"] $
        app "cont" [0]

-- | Returns 1 + 1
ex2 :: Prog
ex2 = prog $ lambda ["cont"] $ 
        app plus [1, 1, "cont"]

-- | Returns the sum of the first 10 integers            
ex3 :: Prog
ex3 = prog $ lambda ["cont"] $
        let_ [("rec", lambda ["p", "i", "c'"] $
                        app if_
                            [ "i"
                            , l $ lambda [] $
                                app plus ["p", "i",
                                    l $ lambda ["p'"] $
                                        app plus ["i", -1,
                                            l $ lambda ["i'"] $
                                                app "rec" [ "p'", "i'",  "c'" ]
                                            ]
                                    ]
                            , l $ lambda [] $
                                app "c'" ["p"]
                            ]
        )] $ app "rec" [0, 10, "cont"]

-- | Does not Terminate
ex4 :: Prog
ex4 = prog $ lambda ["cont"] $
        let_ [("rec", lambda ["c"] $ app "rec" ["c"])] $
           app "rec" ["cont"]

