{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneKindSignatures #-}

module PlutusTx.Compiler.Utils where

import PlutusTx.Compiler.Error
import PlutusTx.Compiler.Types

import PlutusCore qualified as PLC
import PlutusCore.Annotation (Ann, SrcSpan (..), addSrcSpan, annMayInline)

import GHC.Core qualified as GHC
import GHC.Plugins qualified as GHC
import GHC.Types.TyThing qualified as GHC

import Control.Lens (Iso', iso, (^.))
import Control.Monad ((<=<))
import Control.Monad.Except
import Control.Monad.Reader (MonadReader, ask)

import Language.Haskell.TH.Syntax qualified as TH

import Data.Kind qualified as Kind
import Data.Map qualified as Map
import Data.Text qualified as T

{-| Identical to `SomeTypeIn` but without existential kind. Having kind fixed to
`Type` makes it easier to pattern match and construct a different type within
universe. See how it's used in 'compileMkNil'. -}
type SomeStarIn :: (Kind.Type -> Kind.Type) -> Kind.Type
data SomeStarIn uni = forall a. SomeStarIn !(uni (PLC.Esc a))

{-| Get the 'GHC.TyCon' for a given 'TH.Name' stored in the builtin name info,
failing if it is missing. -}
lookupGhcTyCon :: Compiling uni fun m ann => TH.Name -> m GHC.TyCon
lookupGhcTyCon thName = do
  CompileContext {ccNameInfo} <- ask
  case Map.lookup thName ccNameInfo of
    Just (GHC.ATyCon tc) -> pure tc
    _ -> throwPlain $ CompilationError $ "TyCon not found: " <> T.pack (show thName)

{-| Get the 'GHC.Name' for a given 'TH.Name' stored in the builtin name info,
failing if it is missing. -}
lookupGhcName :: Compiling uni fun m ann => TH.Name -> m GHC.Name
lookupGhcName thName = do
  CompileContext {ccNameInfo} <- ask
  case Map.lookup thName ccNameInfo of
    Just thing -> pure (GHC.getName thing)
    Nothing -> throwPlain $ CompilationError $ "Name not found: " <> T.pack (show thName)

{-| Get the 'GHC.Id' for a given 'TH.Name' stored in the builtin name info,
failing if it is missing. -}
lookupGhcId :: Compiling uni fun m ann => TH.Name -> m GHC.Id
lookupGhcId thName = do
  CompileContext {ccNameInfo} <- ask
  case Map.lookup thName ccNameInfo of
    Just (GHC.AnId ghcId) -> pure ghcId
    _ -> throwPlain $ CompilationError $ "Id not found: " <> T.pack (show thName)

-- Note [Suppressed Core annotations in error output]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- Error messages and their "Context:" frames show GHC Core. Raw Core
-- carries much noise a Plinth user cannot act on: occurrence info
-- ("[Occ=Once1!]"), casts with their coercions, uniques ("x_a5yk";
-- also platform-dependent), ticks. Rendering with the corresponding
-- suppression flags keeps the output close to the user's code:
--
--   case x_a5yk [Occ=Once1] of ...   -->   case x of ...
--
-- Module prefixes stay: they tell a supported name from an
-- unsupported one (e.g. GHC.Classes.== vs PlutusTx.Eq.==).

getVarSourceSpan :: GHC.Var -> Maybe GHC.RealSrcSpan
getVarSourceSpan = GHC.srcSpanToRealSrcSpan . GHC.nameSrcSpan . GHC.varName

-- | The name of the file a 'GHC.RealSrcSpan' points to, with path separators
-- normalized to '/'.
--
-- GHC reports backslashes on Windows. Normalizing here makes source locations
-- (and any golden output derived from them) platform-independent.
srcSpanNormFile :: GHC.RealSrcSpan -> String
srcSpanNormFile = map (\c -> if c == '\\' then '/' else c) . GHC.unpackFS . GHC.srcSpanFile

srcSpanIso :: Iso' GHC.RealSrcSpan SrcSpan
srcSpanIso = iso fromGHC toGHC
  where
    fromGHC sp =
      SrcSpan
        { srcSpanFile = srcSpanNormFile sp
        , srcSpanSLine = GHC.srcSpanStartLine sp
        , srcSpanSCol = GHC.srcSpanStartCol sp
        , srcSpanELine = GHC.srcSpanEndLine sp
        , srcSpanECol = GHC.srcSpanEndCol sp
        }
    toGHC sp =
      GHC.mkRealSrcSpan
        (GHC.mkRealSrcLoc (fileNameFs sp) (srcSpanSLine sp) (srcSpanSCol sp))
        (GHC.mkRealSrcLoc (fileNameFs sp) (srcSpanELine sp) (srcSpanECol sp))
    fileNameFs = GHC.fsLit . srcSpanFile

-- | An 'Ann' that carries the source span of the given name, when the
-- name has one. Used to give PIR-level errors a source location.
annForName :: GHC.Name -> Ann
annForName n = case GHC.srcSpanToRealSrcSpan (GHC.nameSrcSpan n) of
  Nothing -> annMayInline
  Just sp -> addSrcSpan (sp ^. srcSpanIso) annMayInline

sdToStr :: MonadReader (CompileContext uni fun) m => GHC.SDoc -> m String
sdToStr sd = do
  CompileContext {ccFlags = flags} <- ask
  -- See Note [Suppressed Core annotations in error output]
  let flags' =
        foldl
          GHC.gopt_set
          flags
          [ GHC.Opt_SuppressIdInfo
          , GHC.Opt_SuppressCoercions
          , GHC.Opt_SuppressUniques
          , GHC.Opt_SuppressTicks
          ]
  pure $ GHC.showSDocForUser flags' GHC.emptyUnitState GHC.alwaysQualify sd

sdToTxt :: MonadReader (CompileContext uni fun) m => GHC.SDoc -> m T.Text
sdToTxt = fmap T.pack . sdToStr

throwSd
  :: (MonadError (CompileError uni fun ann) m, MonadReader (CompileContext uni fun) m)
  => (T.Text -> Error uni fun ann)
  -> GHC.SDoc
  -> m a
throwSd constr = (throwPlain . constr) <=< sdToTxt

tyConsOfExpr :: GHC.CoreExpr -> GHC.UniqSet GHC.TyCon
tyConsOfExpr = \case
  GHC.Type ty -> GHC.tyConsOfType ty
  GHC.Coercion co -> GHC.tyConsOfType $ GHC.mkCoercionTy co
  GHC.Var v -> GHC.tyConsOfType (GHC.varType v)
  GHC.Lit _ -> mempty
  -- ignore anything in the ann
  GHC.Tick _ e -> tyConsOfExpr e
  GHC.App e1 e2 -> tyConsOfExpr e1 <> tyConsOfExpr e2
  GHC.Lam bndr e -> tyConsOfBndr bndr <> tyConsOfExpr e
  GHC.Cast e co -> tyConsOfExpr e <> GHC.tyConsOfType (GHC.mkCoercionTy co)
  GHC.Case scrut bndr ty alts ->
    tyConsOfExpr scrut
      <> tyConsOfBndr bndr
      <> GHC.tyConsOfType ty
      <> foldMap tyConsOfAlt alts
  GHC.Let bind body -> tyConsOfBind bind <> tyConsOfExpr body

tyConsOfBndr :: GHC.CoreBndr -> GHC.UniqSet GHC.TyCon
tyConsOfBndr = GHC.tyConsOfType . GHC.varType

tyConsOfBind :: GHC.Bind GHC.CoreBndr -> GHC.UniqSet GHC.TyCon
tyConsOfBind = \case
  GHC.NonRec bndr rhs -> binderTyCons bndr rhs
  GHC.Rec bndrs -> foldMap (uncurry binderTyCons) bndrs
  where
    binderTyCons bndr rhs = tyConsOfBndr bndr <> tyConsOfExpr rhs

tyConsOfAlt :: GHC.CoreAlt -> GHC.UniqSet GHC.TyCon
tyConsOfAlt (GHC.Alt _ vars e) = foldMap tyConsOfBndr vars <> tyConsOfExpr e

{-| Get the package name for the module being compiled.
Tries 'lookupUnit' first (works for installed packages), then
'thisPackageName' from DynFlags (works for home library units),
and finally falls back to stripping the version from the unit ID string. -}
getPackageName :: GHC.HscEnv -> GHC.Module -> String
getPackageName hscEnv thisModule =
  let unitState = GHC.hsc_units hscEnv
      unit = GHC.moduleUnit thisModule
   in case GHC.lookupUnit unitState unit of
        Just unitInfo -> GHC.unitPackageNameString unitInfo
        Nothing -> case GHC.thisPackageName (GHC.hsc_dflags hscEnv) of
          Just n -> n
          Nothing -> stripVersion (GHC.unitString unit)
  where
    -- Extract "foo-bar" from "foo-bar-1.2.3-inplace-component"
    stripVersion s = go [] s
    go acc [] = reverse acc
    go acc ('-' : rest@(c : _))
      | c >= '0', c <= '9' = reverse acc
      | otherwise = go ('-' : acc) rest
    go acc (c : rest) = go (c : acc) rest
