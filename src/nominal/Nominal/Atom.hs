---------------------------------------------------------------------------------
-- |
-- Copyright :  (c) Edward Kmett 2018
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
---------------------------------------------------------------------------------

module Nominal.Atom
( Atom
, AsAtom(..)
, HasAtom(..)
) where

import Control.Lens
import Nominal.Internal.Trie

class AsAtom t where
  _Atom :: Prism' t Atom

instance AsAtom Atom where
  _Atom = id

instance AsAtom a => AsAtom (Maybe a) where
  _Atom = _Just._Atom

class HasAtom t where
  atom :: Lens' t Atom

instance HasAtom Atom where
  atom = id
