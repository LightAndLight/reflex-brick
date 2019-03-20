{-# language DeriveFunctor, StandaloneDeriving #-}
{-# language DerivingVia #-}
{-# language GADTs #-}
{-# language OverloadedStrings #-}
{-# language RecursiveDo #-}
{-# language ScopedTypeVariables #-}
{-# language TemplateHaskell #-}
{-# language TypeApplications #-}
module Main where

{-

This will likely be factored out into a library, but I'm leaving it here for now

-}

import Reflex
import Reflex.Brick

import Brick.AttrMap (attrMap)
import Brick.Focus
  (FocusRing, focusRing, focusRingCursor, focusNext, focusPrev, focusGetCurrent)
import Brick.Widgets.Border (border)
import Brick.Widgets.Core ((<=>), (<+>), emptyWidget, txt, vLimit)
import Brick.Widgets.Edit
  (Editor, editorText, editContentsL, renderEditor, getEditContents)
import Brick.Types (Widget)
import Control.Monad (guard)
import Control.Monad.Fix (MonadFix)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Reader (ReaderT, runReaderT, ask)
import Data.Function ((&))
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import Lens.Micro ((%~), mapped)
import Lens.Micro.TH (makeLenses)
import qualified Data.Text.Zipper as Zipper

import qualified Data.Text as Text
import qualified Graphics.Vty.Input.Events as Vty

-- | From 'Brick.Widgets.Edit.handleEditorEvent'
handleEditorEvent ::
  Reflex t =>
  EventSelector t RBVtyEvent -> -- ^ terminal events
  Event t (Editor Text n -> Editor Text n)
handleEditorEvent e = (editContentsL %~) <$> eModify
  where
    evkey c ms op =
      fmapMaybe
        (\ms' -> if ms' == ms then Just op else Nothing)
        (select e $ RBKey c)

    eModify =
      mergeWith (.)
      [ evkey (Vty.KChar 'a') [Vty.MCtrl] Zipper.gotoBOL
      , evkey (Vty.KChar 'e') [Vty.MCtrl] Zipper.gotoEOL
      , evkey (Vty.KChar 'd') [Vty.MCtrl] Zipper.deleteChar
      , evkey (Vty.KChar 'k') [Vty.MCtrl] Zipper.killToEOL
      , evkey (Vty.KChar 'u') [Vty.MCtrl] Zipper.killToBOL
      , evkey Vty.KEnter [] Zipper.breakLine
      , evkey Vty.KDel [] Zipper.deleteChar
      , fmapMaybe
          (\(k, ms) ->
             case k of
               Vty.KChar c ->
                 if null ms && c /= '\t'
                 then Just (Zipper.insertChar c)
                 else Nothing
               _ -> Nothing)
          (select e RBAnyKey)
      , evkey Vty.KUp [] Zipper.moveUp
      , evkey Vty.KDown [] Zipper.moveDown
      , evkey Vty.KLeft [] Zipper.moveLeft
      , evkey Vty.KRight [] Zipper.moveRight
      , evkey Vty.KBS [] Zipper.deletePrevChar
      ]

data FormField t n a
  = FormField
  { _fieldData :: Dynamic t a
  , _fieldWidget :: Dynamic t (Widget n)
  , _fieldNames :: [n]
  }
makeLenses ''FormField
deriving instance Reflex t => Functor (FormField t n)

emptyField :: Reflex t => a -> FormField t n a
emptyField a =
  FormField
  { _fieldData = pure a
  , _fieldWidget = pure emptyWidget
  , _fieldNames = []
  }

combineFieldsWith ::
  Reflex t =>
  (Widget n -> Widget n -> Widget n) ->
  FormField t n (a -> b) ->
  FormField t n a ->
  FormField t n b
combineFieldsWith f a b =
  FormField
  { _fieldData = _fieldData a <*> _fieldData b
  , _fieldWidget = f <$> _fieldWidget a <*> _fieldWidget b
  , _fieldNames = _fieldNames a <> _fieldNames b
  }

newtype VFormField t n a = VFormField { unVFormField :: FormField t n a }
  deriving Functor
newtype HFormField t n a = HFormField { unHFormField :: FormField t n a }
  deriving Functor

fieldFocusRing ::
  (Reflex t, MonadHold t m, MonadFix m) =>
  Event t () -> -- ^ previous
  Event t () -> -- ^ next
  [n] -> -- ^ the set of fields
  m (Dynamic t (FocusRing n))
fieldFocusRing ePrev eNext fs = do
  let initial = focusRing fs
  foldDyn
    ($)
    initial
    (mergeWith (\_ _ -> id) [focusPrev <$ ePrev, focusNext <$ eNext])

data Form t n m a where
  FormPure :: a -> Form t n m a
  FormMap :: (a -> b) -> Form t n m a -> Form t n m b
  FormLift :: (Dynamic t (Maybe n) -> m (FormField t n a)) -> Form t n m a
  FormStyle :: (Widget n -> Widget n) -> Form t n m a -> Form t n m a
  FormVert :: Form t n m (a -> b) -> Form t n m a -> Form t n m b
  FormHoriz :: Form t n m (a -> b) -> Form t n m a -> Form t n m b

instance Functor (Form t n m) where; fmap = FormMap

(<*>+) :: Form t n m (a -> b) -> Form t n m a -> Form t n m b
(<*>+) = FormHoriz
infixl 4 <*>+

(<*>=) :: Form t n m (a -> b) -> Form t n m a -> Form t n m b
(<*>=) = FormVert
infixl 4 <*>=

field :: (Dynamic t (Maybe n) -> m (FormField t n a)) -> Form t n m a
field = FormLift

styled :: (Widget n -> Widget n) -> Form t n m a -> Form t n m a
styled = FormStyle

besides :: [Form t n m a] -> Form t n m [a]
besides [] = FormPure []
besides (f : fs) = FormHoriz (FormMap (:) f) (besides fs)

aboves :: [Form t n m a] -> Form t n m [a]
aboves [] = FormPure []
aboves (f : fs) = FormVert (FormMap (:) f) (aboves fs)

makeForm ::
  forall t n m a.
  ( Reflex t, MonadHold t m, MonadFix m
  , Eq n
  ) =>
  Event t () ->
  Event t () ->
  Form t n m a ->
  m (Dynamic t a, Dynamic t (Maybe n), Dynamic t (ReflexBrickAppState n))
makeForm ePrev eNext form = do
  rec
    let dFocus = focusGetCurrent <$> dFocusRing
    ff <- runReaderT (go form) dFocus
    dFocusRing <- fieldFocusRing ePrev eNext $ _fieldNames ff
  pure $
    ( _fieldData ff
    , dFocus
    , (\w fr ->
       ReflexBrickAppState
       { _rbWidgets = [w]
       , _rbCursorFn = focusRingCursor id fr
       , _rbAttrMap = attrMap mempty []
       }) <$>
      _fieldWidget ff <*>
      dFocusRing
    )
  where
    go ::
      forall x.
      Form t n m x ->
      ReaderT (Dynamic t (Maybe n)) m (FormField t n x)
    go (FormPure a) = pure $ emptyField a
    go (FormMap f ma) = fmap f <$> go ma
    go (FormLift ma) = do
      ask >>= lift . ma
    go (FormStyle f ma) = do
      a <- go ma
      pure $ a & fieldWidget.mapped %~ f
    go (FormVert mf ma) = combineFieldsWith (<=>) <$> go mf <*> go ma
    go (FormHoriz mf ma) = combineFieldsWith (<+>) <$> go mf <*> go ma

textFieldBase ::
  forall t m n.
  ( Reflex t, MonadHold t m, MonadFix m
  , Ord n, Show n
  ) =>
  EventSelector t RBVtyEvent -> -- ^ terminal events
  ([Text] -> Widget n) -> -- ^ how to render contents
  n -> -- ^ widget name (must be unique)
  Maybe Text -> -- ^ initial contents
  Maybe Int -> -- ^ line limit
  Dynamic t (Maybe n) -> -- ^ current focus
  m (FormField t n [Text])
textFieldBase eVtyEvent renderLines name def limit dFocus = do
  let initial = editorText name limit (fromMaybe mempty def)
  dInFocus <- holdUniqDyn $ (== Just name) <$> dFocus
  dEditor <-
    foldDyn ($) initial $
    gate (current dInFocus) (handleEditorEvent eVtyEvent)
  pure $
    FormField
    { _fieldData = getEditContents <$> dEditor
    , _fieldWidget = renderEditor renderLines <$> dInFocus <*> dEditor
    , _fieldNames = [name]
    }

textField ::
  forall t m n.
  ( Reflex t, MonadHold t m, MonadFix m
  , Ord n, Show n
  ) =>
  EventSelector t RBVtyEvent -> -- ^ terminal events
  n -> -- ^ widget name (must be unique)
  Maybe Text -> -- ^ initial contents
  Maybe Int -> -- ^ line limit
  Dynamic t (Maybe n) -> -- ^ current focus
  m (FormField t n [Text])
textField eVtyEvent name def limit =
  textFieldBase
    eVtyEvent
    (txt . Text.intercalate "\n")
    name
    def
    limit

passwordField ::
  forall t m n.
  ( Reflex t, MonadHold t m, MonadFix m
  , Ord n, Show n
  ) =>
  EventSelector t RBVtyEvent -> -- ^ terminal events
  n -> -- ^ widget name (must be unique)
  Maybe Text -> -- ^ initial contents
  Dynamic t (Maybe n) -> -- ^ current focus
  m (FormField t n Text)
passwordField eVtyEvent name def =
  (fmap Text.concat <$>) .
  textFieldBase
    eVtyEvent
    (txt . stars)
    name
    def
    (Just 1)
  where
    stars s = Text.replicate (Text.length $ Text.concat s) (Text.singleton '*')

data FormId = FormName | FormPassword
  deriving (Eq, Show, Ord)

network ::
  (Reflex t, MonadHold t m, MonadFix m) =>
  EventSelector t (RBEvent FormId e) ->
  m (ReflexBrickApp t FormId)
network eEvent = do
  let
    eVtyEvent = fan $ select eEvent RBAnyVtyEvent
    eTab = select eEvent (RBVtyEvent . RBKey $ Vty.KChar '\t')
    ePrev = fmapMaybe (\ms -> guard (ms == [Vty.MShift])) eTab
    eNext = fmapMaybe (\ms -> guard (ms == [])) eTab
    eQuit = () <$ select eEvent (RBVtyEvent $ RBKey Vty.KEnter)

  rec
    (_, dFocus, dAppState) <-
      makeForm ePrev eNext $
      (,) <$>
      styled border (field $ textField eVtyEvent FormName Nothing (Just 1)) <*>=
      styled border (field $ passwordField eVtyEvent FormPassword Nothing)

  pure $
    ReflexBrickApp
    { rbaAppState = dAppState
    , rbaSuspendAndResume = never
    , rbaHalt = eQuit
    }

main :: IO ()
main = runReflexBrickApp @FormId (pure ()) Nothing network
