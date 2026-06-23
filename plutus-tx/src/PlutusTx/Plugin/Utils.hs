{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-unused-foralls #-}
{-# OPTIONS_GHC -fomit-interface-pragmas #-}

module PlutusTx.Plugin.Utils where

import Data.ByteString qualified as BS
import Data.Foldable (fold)
import GHC.TypeLits
import PlutusCore.Flat (unflat)
import PlutusTx.Code
import PlutusTx.Utils
import Prelude (Maybe (Just), ($), (.))

{- Note [plc and Proxy]
It would be nice to use TypeApplications instead of passing a Proxy to plc.
However, this means we need to create a type application in the TH-generated code which calls it.
As of recent versions of GHC, this causes an error in the module where the splice appears if it
doesn't have TypeApplications enabled.

Generally we want to avoid forcing users to enable language extensions, so we use
a Proxy to avoid this.
-}

-- This needs to be defined here so we can reference it in the TH functions.
-- If we inline this then we won't be able to find it later!

plinthc :: forall a. a -> CompiledCode a
plinthc _ = SerializedCode (mustBeReplaced "plc") (mustBeReplaced "pir") (mustBeReplaced "covidx")
{-# OPAQUE plinthc #-}

{-| This function is used in `typeCheckResultAction` to mark the given expression
with its source location. -}
anchor :: forall (loc :: Symbol) a. a -> a
anchor a = a
{-# OPAQUE anchor #-}

{-| This function is used in `typeCheckResultAction` to mark the given expression
as unsupported by Plinth. -}
unsupported :: forall (err :: Symbol) (loc :: Symbol) a. a -> a
unsupported x = x
{-# OPAQUE unsupported #-}

-- Note [mkCompiledCode lives in plutus-tx]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- The plugin (in plutus-tx-plugin, built into uplc-ghc) replaces a 'plinthc'
-- marker with a call to 'mkCompiledCode', resolved by TH name. With the
-- compiler baked into uplc-ghc, consumer projects depend on plutus-tx but not
-- on plutus-tx-plugin. So 'mkCompiledCode' must live in plutus-tx for the
-- unit-agnostic name resolution to find a module that exposes it in the
-- consumer's package set. See Note [Unit-id-agnostic name resolution] in
-- plutus-tx-plugin:PlutusTx.Plugin.Common.
mkCompiledCode :: forall a. BS.ByteString -> BS.ByteString -> BS.ByteString -> CompiledCode a
mkCompiledCode plcBS pirBS ci = SerializedCode plcBS (Just pirBS) (fold . unflat $ ci)
{-# OPAQUE mkCompiledCode #-}
