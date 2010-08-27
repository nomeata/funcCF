{-|
 A Pretty printer for 'CPSScheme'-files and control flow graphs.
 -}
{-# LANGUAGE TypeOperators #-}
module CPSPrint  where

import Text.PrettyPrint
import Data.Char

import CPSScheme
import Common

-- * Pretty printer for 'CPSScheme' programs, omitting any labels

-- Pretty-Prints a whole document. The first flag, if set to true, embedds the
-- label information by abusing high range unicode characters.
ppProg :: Bool -> Prog -> Doc
ppProg el = ppLambda el

ppLambda :: Bool -> Lambda -> Doc
ppLambda el (Lambda l vs c) = parens $ 
    embeddLabel el l <> text "λ" <+> sep
       [ hsep (map (\(Var n) -> text n) vs) <> text "." 
       , ppCall el c
       ]

ppCall :: Bool -> Call -> Doc
ppCall el (App l (P (If lt lf)) [b,c1,c2]) = sep
    [ embeddLabel el l  <> text "if" <+> ppVal el b
    , embeddLabel el lt <> text "then" <+> ppVal el c1
    , embeddLabel el lf <> text "else" <+> ppVal el c2
    ]
ppCall el (App l f as) =
    embeddLabel el l <> ppVal el f <+> sep (map (ppVal el) as)
ppCall el (Let l binds c) =
    embeddLabel el l <> text "let" <+> vcat (map ppBind binds) $$
    text "in" <+> ppCall el c
    where ppBind (Var n,l) = text n <+> text "=" $$ nest 6 (ppLambda el l)

ppVal :: Bool -> Val -> Doc
ppVal el (L l)             = ppLambda el l
ppVal el (R _ _ (Var v))   = text v
ppVal el (C _ c)           = integer c
ppVal el (P (Plus _))      = text "(+)"
ppVal el (P (If _ _))      = text "if"

-- * Label embedding trick

-- | First unicode point to embed labels with (Private Use Area)
startAt :: Integer
startAt = 0x100000

labelToChar :: Label -> Char
labelToChar (Label i) = chr (fromIntegral (startAt + i))

charToLabel :: Char -> Maybe Label
charToLabel c = if i >= startAt then Just $ Label (i - startAt)
                                else Nothing
  where i = fromIntegral (ord c)                            

embeddLabel :: Bool -> Label -> Doc
embeddLabel False _  = empty
embeddLabel True  l  = char (labelToChar l)
