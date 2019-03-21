{-# language DeriveFunctor, StandaloneDeriving #-}
{-# language DerivingVia #-}
{-# language GADTs #-}
{-# language OverloadedLists #-}
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

import Brick.AttrMap (AttrMap, attrMap)
import Brick.Focus
  (FocusRing, focusRing, focusRingCursor, focusNext, focusPrev, focusGetCurrent)
import Brick.Forms (focusedFormInputAttr)
import Brick.Widgets.Border (border)
import Brick.Widgets.Core
  ((<=>), (<+>), emptyWidget, txt, vLimit, vBox, withDefAttr, showCursor, padBottom)
import Brick.Widgets.Edit
  (Editor, editorText, editContentsL, renderEditor, getEditContents)
import Brick.Types (Widget, Location(..), Padding(..))
import Brick.Util (on)
import Control.Monad (guard)
import Control.Monad.Fix (MonadFix)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Reader (ReaderT, runReaderT, ask)
import Data.Function ((&))
import Data.List.NonEmpty (NonEmpty(..))
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import Lens.Micro ((%~), (^.), _1, _2, mapped, _last)
import Lens.Micro.TH (makeLenses)
import qualified Data.Text.Zipper as Zipper

import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Text as Text
import qualified Graphics.Vty.Attributes as Vty
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
  AttrMap ->
  Event t () ->
  Event t () ->
  Form t n m a ->
  m (Dynamic t a, Dynamic t (Maybe n), Dynamic t (ReflexBrickAppState n))
makeForm style ePrev eNext form = do
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
       , _rbAttrMap = style
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
    , _fieldWidget =
      (\focus -> addStyle focus . renderEditor renderLines focus) <$>
      dInFocus <*>
      dEditor
    , _fieldNames = [name]
    }
  where
    addStyle focus = if focus then withDefAttr focusedFormInputAttr else id

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

radioField ::
  ( Reflex t, MonadHold t m
  , Eq n
  ) =>
  EventSelector t RBVtyEvent -> -- ^ terminal events
  NonEmpty (n, a, Text) -> -- ^ selections
  Dynamic t (Maybe n) -> -- ^ current focus
  m (FormField t n a)
radioField eVtyEvent choices dFocus = do
  let
    names = foldr (\a b -> (^.) a _1 : b) [] choices
    initial = let x = NonEmpty.head choices in (x ^. _1, x ^. _2)
    eSpace = select eVtyEvent (RBKey $ Vty.KChar ' ')

  let dHighlighted = (>>= \n -> (,) n <$> lookupValue n choices) <$> dFocus
  dSelected <- holdDyn initial $ attachWithMaybe const (current dHighlighted) eSpace

  pure $
    FormField
    { _fieldData = (^. _2) <$> dSelected
    , _fieldWidget =
        (\mh (ns, _) ->
           vBox $
           foldr
             (\(n', _, a) -> (:) (addStyle mh n' . txt $ radio ns n' <> a))
             []
             choices) <$>
        dHighlighted <*>
        dSelected
    , _fieldNames = names
    }
  where
    lookupValue n ((n', a, _) :| []) =
      if n == n' then Just a else Nothing
    lookupValue n ((n', a, _) :| (x : xs)) =
      if n == n' then Just a else lookupValue n (x :| xs)

    addStyle mh n' =
      if maybe False (\(nh, _) -> nh == n') mh
      then showCursor n' (Location (1, 0)) . withDefAttr focusedFormInputAttr
      else id

    radio ns n' = if ns == n' then "[*] " else "[ ] "

checkboxField ::
  ( Reflex t, MonadHold t m, MonadFix m
  , Eq n
  ) =>
  EventSelector t RBVtyEvent -> -- ^ terminal events
  n -> -- ^ name
  Text -> -- ^ label
  Dynamic t (Maybe n) -> -- ^ current focus
  m (FormField t n Bool)
checkboxField eVtyEvent name label dFocus = do
  let eSpace = select eVtyEvent (RBKey $ Vty.KChar ' ')

  let dHighlighted = (==Just name) <$> dFocus
  rec
    dChecked <-
      holdDyn False $
      (not <$>
      current dChecked <@
      attachWithMaybe
        (\h _ -> guard h)
        (current dHighlighted)
        eSpace)

  pure $
    FormField
    { _fieldData = dChecked
    , _fieldWidget =
        (\h c -> addStyle h $ txt $ check c <> label) <$>
        dHighlighted <*>
        dChecked
    , _fieldNames = [name]
    }
  where
    addStyle h =
      if h
      then showCursor name (Location (1, 0)) . withDefAttr focusedFormInputAttr
      else id

    check c = if c then "[x] " else "[ ] "

data FormId
  = FormName
  | FormPassword
  | FormX
  | FormY
  | FormZ
  | FormQuestion
  deriving (Eq, Show, Ord)

data C = X | Y | Z
  deriving (Eq, Show, Ord)

styling :: AttrMap
styling =
  attrMap Vty.defAttr
  [ (focusedFormInputAttr, Vty.black `on` Vty.white)
  ]

network ::
  (Reflex t, MonadHold t m, MonadFix m) =>
  EventSelector t (RBEvent FormId e) ->
  m (ReflexBrickApp t FormId)
network eEvent = do
  let
    eVtyEvent = fan $ select eEvent RBAnyVtyEvent
    ePrev =
      fmapMaybe
        (guard . null)
        (select eEvent (RBVtyEvent . RBKey $ Vty.KBackTab))
    eNext =
      fmapMaybe
        (guard . null)
        (select eEvent (RBVtyEvent . RBKey $ Vty.KChar '\t'))
    eQuit = () <$ select eEvent (RBVtyEvent $ RBKey Vty.KEnter)

  rec
    (dData, dFocus, dAppState) <-
      makeForm styling ePrev eNext $
      (,,,) <$>
      styled border (field $ textField eVtyEvent FormName Nothing (Just 1)) <*>=
      styled border (field $ passwordField eVtyEvent FormPassword Nothing) <*>=
      styled
        (padBottom $ Pad 1)
        (field (radioField eVtyEvent [(FormX, X, "X"), (FormY, Y, "Y"), (FormZ, Z, "Z")])) <*>=
      field (checkboxField eVtyEvent FormQuestion "???")

  pure $
    ReflexBrickApp
    { rbaAppState =
      (\as output ->
        as
          { _rbWidgets =
            _rbWidgets as & _last %~ (<=> txt ("output: " <> Text.pack (show output)))
          }) <$>
      dAppState <*>
      dData
    , rbaSuspendAndResume = never
    , rbaHalt = eQuit
    }

main :: IO ()
main = runReflexBrickApp @FormId (pure ()) Nothing network
