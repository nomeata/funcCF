{-|
  This module defines the syntax of the simple, continuation-passing-style
  functional language used here, as well as some examples.
-}
{-# LANGUAGE GeneralizedNewtypeDeriving, OverloadedStrings#-}
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

-- | As constants we only have integers.
type Const = Integer

-- | Primitive operations. The primitive operations are annotated by labels. These mark the (invisible) call sites that call the continuations, and are one per continuation.
data Prim = Plus Label -- ^ Integer addition. Expected parameters: two integers, one continuation.
          | If Label Label -- ^ Conditional branching. Expected paramters: one integer, one continuation to be called if the argument is nonzero, one continuation to be called if the argument is zero (“false”)
    deriving (Show, Eq, Ord)

-- * Some example Programs

-- | Returns 0
ex1 :: Prog
ex1 = Lambda 0 ["cont"] $
        App 1 (R 2 0 "cont") [C 3 0]

-- | Returns 1 + 1
ex2 :: Prog
ex2 = Lambda 0 ["cont"] $ 
        App 1 (P (Plus 1))
            [ C 2 1
            , C 3 1
            , R 4 0 "cont"]

-- | Returns the sum of the first 10 integers            
ex3 :: Prog
ex3 = Lambda 0 ["cont"] $
        Let 1 [("rec", Lambda 2 ["p", "i", "c'"] $
                        App 3 (P (If 4 31))
                            [ R 5 2 "i"
                            , L $ Lambda 6 [] $
                                App 7 (P  (Plus 8)) [R 9 2 "p", R 10 2 "i",
                                    L $ Lambda 11 ["p'"] $
                                        App 12 (P (Plus 30)) [R 13 2 "i", C 26 (-1),
                                            L $ Lambda 14 ["i'"] $
                                                App 29 (R 15 1 "rec")
                                                    [ R 16 11 "p'"
                                                    , R 17 14 "i'"
                                                    , R 18 2 "c'" ]
                                            ]
                                    ]
                            , L $ Lambda 19 [] $
                                App 20 (R 21 2 "c'") [R 22 2 "p"]
                            ]
        )] $ App 23 (R 24 1 "rec") [C 27 0, C 28 10, R 25 0 "cont"]

-- | Does not Terminate
ex4 :: Prog
ex4 = Lambda 0 ["cont"] $
        Let 1 [("rec",Lambda 2 ["c"] $
            App 3 (R 4 1 "rec") [R 5 2 "c"]
        )] $ App 6 (R 7 1 "rec") [R 8 0 "cont"]

