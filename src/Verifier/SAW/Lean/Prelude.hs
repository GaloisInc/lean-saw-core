{-# LANGUAGE TemplateHaskell #-}

{- |
Module      : Verifier.SAW.Lean.Prelude
Copyright   : Galois, Inc. 2017
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.Lean.Prelude
  ( Module
  , module Verifier.SAW.Lean.Prelude
  ) where

import Verifier.SAW.Prelude
import Verifier.SAW.ParserUtils

$(runDecWriter $ do
    prelude <- defineImport [|preludeModule|] preludeModule
    lean <- defineModuleFromFile [prelude] "leanModule" "saw/Lean.sawcore"
    declareSharedModuleFns "Lean" (decVal lean)
 )
