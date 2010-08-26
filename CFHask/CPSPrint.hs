{-|
 A Pretty printer for 'CPSScheme'-files and control flow graphs.
 -}
{-# LANGUAGE TypeOperators #-}
module CPSPrint  where

import Text.PrettyPrint

import CPSScheme
import Common

-- * Pretty printer for 'CPSScheme' programs, omitting any labels

ppProg :: Prog -> Doc
ppProg = ppLambda

ppLambda :: Lambda -> Doc
ppLambda (Lambda _ vs c) = parens $ text "λ" <+> sep
   [ hsep (map (\(Var n) -> text n) vs) <> text "." 
   , ppCall c
   ]

ppCall :: Call -> Doc
ppCall (App _ (P (If _ _)) [b,c1,c2]) = sep
    [ text "if" <+> ppVal b
    , text "then" <+> ppVal c1
    , text "else" <+> ppVal c2
    ]
ppCall (App _ f as) =
    ppVal f <+> sep (map ppVal as)
ppCall (Let _ binds c) =
    text "let" <+> vcat (map ppBind binds) $$
    text "in" <+> ppCall c
    where ppBind (Var n,l) = text n <+> text "=" $$ nest 6 (ppLambda l)

ppVal :: Val -> Doc
ppVal (L l)             = ppLambda l
ppVal (R _ _ (Var v))   = text v
ppVal (C _ c)           = integer c
ppVal (P (Plus _))      = text "(+)"
ppVal (P (If _ _))      = text "if"
