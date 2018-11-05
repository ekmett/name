module Nominal.Restriction where

import Nominal.Atom
import Nominal.Tie

infixr 6 #\

class Restricted x where
  -- |
  -- @
  -- restrict . nreturn = id
  -- restrict . fmap restrict = restrict . fmap restrict . delta
  -- restrict (Tie a x) = a #\ x
  -- @
  restrict :: Tie x -> x
  restrict (Tie a x) = a #\ x

  -- |
  -- @
  -- a # a #\ x
  -- a # x ⇒  a #\ x = x
  -- a #\ b #\ x = b #\ a #\ x
  -- @
  -- |
  (#\) :: Atom -> x -> x
  a #\ x = restrict (Tie a x)

  {-# minimal restrict | (#\) #-}

