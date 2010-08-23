{-|
  Some convenience definitions.
 -}
{-# LANGUAGE TypeOperators #-}
module Common where

import qualified Data.Map as M

-- * Type aliases

-- | Convenient alias for a partial map
type a :⇀ b = M.Map a b
infixl 8 :⇀

-- | Convenient alias for a product type
type a :× b = (a,b)
infixl 9 :×

-- * Partial map functions

-- | A function used to write map updates resembling the mathematical syntax m [ k &#8614; v]  as m `upd` [k &#8614; v]
upd :: (Ord k) => k :⇀a -> [k :× a] -> k :⇀ a
upd map list = M.union (M.fromList list) map

-- | For use in the argument list of 'upd'
(↦) :: k -> v -> k :× v
k ↦ v = (k,v)
