{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskellQuotes #-}

module PlutusTx.Plugin.Unsupported where

import PlutusTx.Compiler.Compat qualified as Compat
import PlutusTx.Compiler.Expr
import PlutusTx.Compiler.Type (splitGhcName)
import PlutusTx.Plugin.Utils qualified

import GHC.Builtin.Names qualified as GHC
import GHC.Core.TyCo.Rep qualified as GHC
import GHC.Hs qualified as GHC
import GHC.Hs.Syn.Type qualified as GHC
import GHC.Iface.Env qualified as GHC
import GHC.Plugins qualified as GHC
import GHC.Tc.Types qualified as GHC
import GHC.Tc.Types.Evidence qualified as GHC
import GHC.Tc.Utils.Env qualified as GHC
import GHC.Tc.Utils.Monad qualified as GHC
import GHC.Unit.Finder qualified as GHC

import Control.Monad.IO.Class
import Data.Foldable
import GHC.Data.Maybe (MaybeErr (..))
import Data.Generics.Uniplate.Data
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe
import Language.Haskell.TH qualified as TH

type Module = String
type Class = String
type Method = String
type Function = String
type UseThisInstead = Maybe String

data Unsupported
  = BaseMethod Class Method UseThisInstead
  | BaseFunction Function UseThisInstead
  | -- | The Bool tells if the range is bounded ([a .. b]) or not ([a ..]).
    RangeSyntax Bool
  | IO

renderUnsupported :: Unsupported -> String
renderUnsupported = \case
  BaseMethod cls method malt ->
    (cls <> "." <> method)
      <> case malt of Just alt -> ", use " <> alt; Nothing -> ""
  BaseFunction fn malt ->
    fn <> case malt of Just alt -> ", use " <> alt; Nothing -> ""
  RangeSyntax True ->
    "Range syntax, use PlutusTx.Enum.enumFromTo or PlutusTx.Enum.enumFromThenTo"
  RangeSyntax False ->
    "Unbounded range syntax: unbounded ranges are not supported"
  IO -> "IO actions are not supported in Plinth"

isUnsupported :: GHC.HsExpr GHC.GhcTc -> Maybe Unsupported
isUnsupported expr =
  asum
    [ checkUnsupportedMethod expr
    , checkUnsupportedFunction expr
    , checkRangeSyntax expr
    , checkIO ty
    ]
  where
    ty = GHC.hsExprType expr

-- | Check if an expr uses range syntax ([a..b] and friends). It shows
-- as an 'ArithSeq' node, not as an 'enumFromTo' method occurrence, so
-- 'checkUnsupportedMethod' cannot catch it.
checkRangeSyntax :: GHC.HsExpr GHC.GhcTc -> Maybe Unsupported
checkRangeSyntax = \case
  GHC.ArithSeq _ _ info -> Just . RangeSyntax $ case info of
    GHC.From {} -> False
    GHC.FromThen {} -> False
    GHC.FromTo {} -> True
    GHC.FromThenTo {} -> True
  _ -> Nothing

-- | Check if the type involves IO.
checkIO :: GHC.Type -> Maybe Unsupported
checkIO ty = case GHC.splitTyConApp_maybe ty of
  Just (tc, _) | GHC.getName tc == GHC.ioTyConName -> Just IO
  _ -> do
    (_, _, arg, res) <- GHC.splitFunTy_maybe ty
    asum [checkIO arg, checkIO res]

-- | Check if an expr is a method of an unsupported @base@ class.
checkUnsupportedMethod :: GHC.HsExpr GHC.GhcTc -> Maybe Unsupported
checkUnsupportedMethod = \case
  GHC.HsVar _ (GHC.L _ v)
    | Just cls <- GHC.getName <$> GHC.isClassOpId_maybe v
    , (Just modu, occ) <- splitGhcName cls
    , Just alt <- Map.lookup (modu, occ) unsupportedBaseClasses ->
        Just $ BaseMethod (modu <> "." <> occ) (renderGhcName $ GHC.getName v) alt
    | otherwise -> Nothing
  GHC.XExpr (Compat.WrapExpr e) -> checkUnsupportedMethod e
  _ -> Nothing

-- | Check if an expr is an unsupported @base@ function.
checkUnsupportedFunction :: GHC.HsExpr GHC.GhcTc -> Maybe Unsupported
checkUnsupportedFunction = \case
  GHC.HsVar _ (GHC.L _ v)
    | (Just modu, occ) <- splitGhcName (GHC.getName v)
    , Just alt <- Map.lookup (modu, occ) unsupportedBaseFunctions ->
        Just $ BaseFunction (modu <> "." <> occ) alt
  GHC.XExpr (Compat.WrapExpr e) -> checkUnsupportedFunction e
  _ -> Nothing

renderGhcName :: GHC.Name -> String
renderGhcName = GHC.showSDocUnsafe . GHC.pprName
{-# INLINE renderGhcName #-}

-- The suggestions are written out instead of derived with TH.pprint:
-- the latter prints the class's defining module (PlutusTx.Eq.Class,
-- PlutusTx.Show.TH, ...), not the module users import from.
unsupportedBaseClasses :: Map (Module, Class) UseThisInstead
unsupportedBaseClasses =
  Map.fromList
    . mapMaybe
      ( \(name, alt) -> do
          modu <- TH.nameModule name
          pure ((modu, TH.nameBase name), alt)
      )
    $ [ (''Prelude.Eq, Just "PlutusTx.Eq.Eq")
      , (''Prelude.Ord, Just "PlutusTx.Ord.Ord")
      , (''Prelude.Show, Just "PlutusTx.Show.Show")
      , (''Prelude.Enum, Just "PlutusTx.Enum.Enum")
      ]

{-| @base@ functions that can never work in Plinth, detected at the
type-check stage so the error points at the use site. Only add
functions that always fail to compile: the 'unsupported' wrap turns
every compiled use into an error. -}
unsupportedBaseFunctions :: Map (Module, Function) UseThisInstead
unsupportedBaseFunctions =
  Map.fromList
    . mapMaybe
      ( \(name, alt) -> do
          modu <- TH.nameModule name
          pure ((modu, TH.nameBase name), alt)
      )
    $ [ ('Prelude.error, plutusError)
      , ('Prelude.errorWithoutStackTrace, plutusError)
      , ('Prelude.undefined, plutusError)
      ]
  where
    plutusError = Just "PlutusTx.Prelude.error or PlutusTx.Prelude.traceError"

unsupportedMarkerModule, unsupportedMarkerName :: String
unsupportedMarkerModule = fromJust $ TH.nameModule 'PlutusTx.Plugin.Utils.unsupported
unsupportedMarkerName = TH.nameBase 'PlutusTx.Plugin.Utils.unsupported

{- Note [Do not wrap the compiler markers]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The types of the compiler markers mention the user's code type. For
example, in

  code :: CompiledCode (IO ())
  code = $$(PlutusTx.compile [|| ... ||])

the splice applies 'plinthc' at type 'IO () -> CompiledCode (IO ())',
so the IO check matches the 'plinthc' occurrence itself. Wrapping it
in 'unsupported' hides the marker from the plugin pass, which then
fails with "Found invalid marker" instead of the real error. The same
holds for 'anchor' applications injected before this pass. So an
expression whose head is one of the markers is never wrapped; the
offending sub-expression still gets its own wrap. -}

-- | The markers that must never be wrapped in 'unsupported'.
protectedMarkerNames :: [String]
protectedMarkerNames =
  TH.nameBase
    <$> [ 'PlutusTx.Plugin.Utils.plinthc
        , 'PlutusTx.Plugin.Utils.anchor
        , 'PlutusTx.Plugin.Utils.unsupported
        , 'PlutusTx.Plugin.Utils.mkCompiledCode
        ]

-- | The head variable of an application chain, if any.
exprHeadName :: GHC.HsExpr GHC.GhcTc -> Maybe GHC.Name
exprHeadName = \case
  GHC.HsVar _ (GHC.L _ v) -> Just (GHC.getName v)
  GHC.HsApp _ (GHC.L _ f) _ -> exprHeadName f
  Compat.HsAppType _ (GHC.L _ f) _ -> exprHeadName f
  GHC.XExpr (Compat.WrapExpr e) -> exprHeadName e
  Compat.HsPar (GHC.L _ e) -> exprHeadName e
  _ -> Nothing

injectUnsupportedMarkers :: GHC.TcGblEnv -> GHC.TcM GHC.TcGblEnv
injectUnsupportedMarkers env = do
  hscEnv <- GHC.getTopEnv
  findResult <-
    liftIO $
      GHC.findImportedModule
        hscEnv
        (GHC.mkModuleName unsupportedMarkerModule)
        GHC.NoPkgQual
  case findResult of
    GHC.Found _ m -> do
      -- See Note [Tolerate non-Plinth modules under uplc-ghc]
      name <- GHC.lookupOrig m (GHC.mkVarOcc unsupportedMarkerName)
      mbThing <- liftIO $ GHC.lookupGlobal_maybe hscEnv name
      case mbThing of
        Succeeded (GHC.AnId unsupportedId) -> do
          markers <- traverse (GHC.lookupOrig m . GHC.mkVarOcc) protectedMarkerNames
          let binds = GHC.tcg_binds env
              binds' = Compat.modifyBinds (transformBi (wrapUnsupported markers unsupportedId)) binds
          pure env {GHC.tcg_binds = binds'}
        _ -> pure env
    _ -> pure env

{- Note [Tolerate non-Plinth modules under uplc-ghc]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
uplc-ghc loads this plugin as a *static* plugin, so its typeCheckResultAction
runs on every module it compiles, not only Plinth programs. The marker
(unsupported, anchor, plinthc) lives in PlutusTx.Plugin.Utils, and we may only
inject a reference to it when that module is reachable from the module under
compilation -- i.e. its interface can be loaded. Otherwise the injected
reference would be ill-scoped and GHC aborts with "Can't find interface-file
declaration for ...".

Two cases must be tolerated:

  (1) PlutusTx.Plugin.Utils is not on the search path at all (a package that
      does not depend on plutus-tx): 'findImportedModule' returns NotFound.

  (2) It is in the home package (e.g. while compiling plutus-tx's own modules,
      which do not depend on PlutusTx.Plugin.Utils): 'findImportedModule'
      returns Found, but the interface is not reachable from this module's
      imports.

We probe reachability with 'lookupGlobal_maybe', which loads the marker's Id
from the home/external package tables and returns 'Failed' (rather than
throwing) when the interface is not reachable. Only when it succeeds is there
something to mark, so otherwise we leave the module unchanged. A dynamically
loaded plugin would only ever run on modules that requested it via -fplugin,
where the marker is always reachable.
-}

wrapUnsupported :: [GHC.Name] -> GHC.Id -> GHC.LHsExpr GHC.GhcTc -> GHC.LHsExpr GHC.GhcTc
wrapUnsupported markers unsupportedId le@(GHC.L ann e)
  -- See Note [Do not wrap the compiler markers]
  | Just h <- exprHeadName e
  , h `elem` markers =
      le
  | Just unsupported <- isUnsupported e
  , Just sp <- GHC.srcSpanToRealSrcSpan (GHC.locA ann) =
      let msgTy = GHC.LitTy . GHC.StrTyLit . GHC.mkFastString $ renderUnsupported unsupported
          locTy = GHC.LitTy . GHC.StrTyLit . GHC.mkFastString $ encodeSrcSpan sp
          ty = GHC.hsExprType e
          wrapper =
            GHC.WpTyApp ty
              `GHC.WpCompose` GHC.WpTyApp locTy
              `GHC.WpCompose` GHC.WpTyApp msgTy
          wrapped = GHC.mkHsWrap wrapper (GHC.HsVar GHC.noExtField (GHC.noLocA unsupportedId))
       in GHC.noLocA $ Compat.hsAppTc (GHC.noLocA wrapped) le
  | otherwise = le
