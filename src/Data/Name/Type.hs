---------------------------------------------------------------------------------
-- |
-- Copyright :  (c) Edward Kmett 2018
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
---------------------------------------------------------------------------------

module Data.Name.Type
( Name
, AsName(..)
, HasName(..)
) where

import Control.Lens
import Data.Name.Internal.Trie

class AsName t where
  _Name :: Prism' t Name

instance AsName Name where
  _Name = id

instance AsName a => AsName (Maybe a) where
  _Name = _Just._Name

class HasName t where
  atom :: Lens' t Name

instance HasName Name where
  atom = id
