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
  ((<=>), (<+>), emptyWidget, txt, vBox, withDefAttr, showCursor, padBottom)
import Brick.Widgets.Edit
  (Editor, editorText, editContentsL, renderEditor, getEditContents)
import Brick.Types (Widget, Location(..), Padding(..))
import Brick.Util (on)
import Control.Monad (guard)
import Control.Monad.Fix (MonadFix)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Reader (ReaderT, runReaderT, ask)
import Data.Foldable (foldl')
import Data.Function ((&))
import Data.List.NonEmpty (NonEmpty(..))
import Data.Maybe (isJust, fromMaybe)
import Data.Set (Set)
import Data.Text (Text)
import Lens.Micro ((%~), (^.), _1, _2, mapped, _last)
import Lens.Micro.TH (makeLenses)

import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified Data.Text.Zipper as Zipper
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

dynFocusRing ::
  (Reflex t, MonadHold t m, MonadFix m) =>
  Event t () -> -- ^ previous
  Event t () -> -- ^ next
  [n] -> -- ^ the set of fields
  m (Dynamic t (FocusRing n))
dynFocusRing ePrev eNext fs = do
  let initial = focusRing fs
  foldDyn
    ($)
    initial
    (mergeWith (\_ _ -> id) [focusPrev <$ ePrev, focusNext <$ eNext])

data Form t n m a where
  FormPure :: a -> Form t n m a
  FormMap :: (a -> b) -> Form t n m a -> Form t n m b
  FormLift ::
    (EventSelector t RBVtyEvent ->
     Dynamic t (Maybe n) ->
     m (FormField t n a)) ->
    Form t n m a
  FormStyle :: (Widget n -> Widget n) -> Form t n m a -> Form t n m a
  FormVert :: Form t n m (a -> b) -> Form t n m a -> Form t n m b
  FormHoriz :: Form t n m (a -> b) -> Form t n m a -> Form t n m b

instance Functor (Form t n m) where; fmap = FormMap

(<*>+) :: Form t n m (a -> b) -> Form t n m a -> Form t n m b
(<*>+) = FormHoriz
infixl 4 <*>+

(<*+) :: Form t n m a -> Form t n m b -> Form t n m a
(<*+) a b = const <$> a <*>+ b
infixl 4 <*+

(*>+) :: Form t n m a -> Form t n m b -> Form t n m b
(*>+) a b = const id <$> a <*>+ b
infixl 4 *>+

(<*>=) :: Form t n m (a -> b) -> Form t n m a -> Form t n m b
(<*>=) = FormVert
infixl 4 <*>=

(<*=) :: Form t n m a -> Form t n m b -> Form t n m a
(<*=) a b = const <$> a <*>= b
infixl 4 <*=

(*>=) :: Form t n m a -> Form t n m b -> Form t n m b
(*>=) a b = const id <$> a <*>= b
infixl 4 *>=

fieldM ::
  (EventSelector t RBVtyEvent -> Dynamic t (Maybe n) -> m (FormField t n a)) ->
  Form t n m a
fieldM = FormLift

field :: Applicative m => FormField t n a -> Form t n m a
field f = fieldM (\_ _ -> pure f)

styled :: (Widget n -> Widget n) -> Form t n m a -> Form t n m a
styled = FormStyle

(@@=) :: (Widget n -> Widget n) -> Form t n m a -> Form t n m a
(@@=) = styled

infixr 5 @@=

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
  EventSelector t RBVtyEvent -> -- ^ terminal input events
  AttrMap -> -- ^ styling
  Event t () -> -- ^ cycle forward through form
  Event t () -> -- ^ cycle forward through form
  Form t n m a -> -- ^ the form
  m (Dynamic t a, Dynamic t (Maybe n), Dynamic t (ReflexBrickAppState n))
makeForm eVtyEvent style ePrev eNext form = do
  rec
    let dFocus = focusGetCurrent <$> dFocusRing
    ff <- runReaderT (go form) (eVtyEvent, dFocus)
    dFocusRing <- dynFocusRing ePrev eNext $ _fieldNames ff
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
      ReaderT (EventSelector t RBVtyEvent, Dynamic t (Maybe n)) m (FormField t n x)
    go (FormPure a) = pure $ emptyField a
    go (FormMap f ma) = fmap f <$> go ma
    go (FormLift ma) = do
      ask >>= lift . uncurry ma
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
  ([Text] -> Widget n) -> -- ^ how to render contents
  n -> -- ^ widget name (must be unique)
  Maybe Text -> -- ^ initial contents
  Maybe Int -> -- ^ line limit
  EventSelector t RBVtyEvent -> -- ^ terminal events
  Dynamic t (Maybe n) -> -- ^ current focus
  m (FormField t n [Text])
textFieldBase renderLines name def limit eVtyEvent dFocus = do
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
  n -> -- ^ widget name (must be unique)
  Maybe Text -> -- ^ initial contents
  Maybe Int -> -- ^ line limit
  EventSelector t RBVtyEvent -> -- ^ terminal events
  Dynamic t (Maybe n) -> -- ^ current focus
  m (FormField t n [Text])
textField name def limit =
  textFieldBase
    (txt . Text.intercalate "\n")
    name
    def
    limit

passwordField ::
  forall t m n.
  ( Reflex t, MonadHold t m, MonadFix m
  , Ord n, Show n
  ) =>
  n -> -- ^ widget name (must be unique)
  Maybe Text -> -- ^ initial contents
  EventSelector t RBVtyEvent -> -- ^ terminal events
  Dynamic t (Maybe n) -> -- ^ current focus
  m (FormField t n Text)
passwordField name def eVtyEvent =
  (fmap Text.concat <$>) .
  textFieldBase
    (txt . stars)
    name
    def
    (Just 1)
    eVtyEvent
  where
    stars s = Text.replicate (Text.length $ Text.concat s) (Text.singleton '*')

radioField ::
  ( Reflex t, MonadHold t m
  , Eq n
  ) =>
  NonEmpty (n, a, Text) -> -- ^ selections
  EventSelector t RBVtyEvent -> -- ^ terminal events
  Dynamic t (Maybe n) -> -- ^ current focus
  m (FormField t n a)
radioField choices eVtyEvent dFocus = do
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
  n -> -- ^ name
  Text -> -- ^ label
  EventSelector t RBVtyEvent -> -- ^ terminal events
  Dynamic t (Maybe n) -> -- ^ current focus
  m (FormField t n Bool)
checkboxField name label eVtyEvent dFocus = do
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

listField ::
  forall t n m a.
  ( Reflex t, MonadHold t m, MonadFix m
  , Ord n
  ) =>
  [(n, Text, a)] -> -- ^ choices
  EventSelector t RBVtyEvent -> -- ^ terminal events
  Dynamic t (Maybe n) -> -- ^ current focus
  m (FormField t n [a])
listField choices eVtyEvent eFocus = do
  let
    names = fmap (^. _1) choices
    eSpace = select eVtyEvent . RBKey $ Vty.KChar ' '

    dSelected = (>>= \n -> if n `elem` names then Just n else Nothing) <$> eFocus
    dInFocus = isJust <$> dSelected

  rec
    dIxs :: Dynamic t (Set n) <-
      holdDyn mempty $
      (\mix ixs ->
         case mix of
           Nothing -> ixs
           Just ix ->
             if ix `Set.member` ixs
             then Set.delete ix ixs
             else Set.insert ix ixs) <$>
      current dSelected <*>
      current dIxs <@
      gate (current dInFocus) eSpace

  pure $
    FormField
    { _fieldData =
      (\ixs ->
         foldr
           (\(n, _, a) b -> if n `Set.member` ixs then a : b else b)
           []
           choices) <$>
      dIxs
    , _fieldWidget =
      (\msel f ixs ->
         foldl'
           (\b (n, l, _) ->
              b <=>
              addStyle n
                (f && Just n == msel)
                (txt $ (if n `Set.member` ixs then "+ " else "- ") <> l))
           emptyWidget
           choices) <$>
      dSelected <*>
      dInFocus <*>
      dIxs
    , _fieldNames = names
    }

  where
    addStyle n b =
      if b
      then showCursor n (Location (0, 0)) . withDefAttr focusedFormInputAttr
      else id

makeButton ::
  forall t n m.
  ( Reflex t, MonadHold t m, MonadFix m
  , Eq n
  ) =>
  n -> -- ^ name
  Text -> -- ^ value
  EventSelector t RBVtyEvent -> -- ^ terminal inputs
  Dynamic t (Maybe n) -> -- ^ current focus
  m (Event t (), FormField t n ())
makeButton name value eVtyEvent dFocus =
  pure
  ( gate ((==Just name) <$> current dFocus) eEnter
  , FormField
    { _fieldData = pure ()
    , _fieldWidget =
      (\f -> addStyle (f == Just name) (txt $ "[" <> value <> "]")) <$>
      dFocus
    , _fieldNames = [name]
    }
  )
  where
    addStyle b =
      if b
      then withDefAttr focusedFormInputAttr
      else id

    eEnter = () <$ select eVtyEvent (RBKey Vty.KEnter)

data FormId
  = FormName
  | FormPassword
  | FormX
  | FormY
  | FormZ
  | FormQuestion
  | FormListX
  | FormListY
  | FormListZ
  | FormSubmit
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

  rec
    (eSubmit, button) <- makeButton FormSubmit "submit" eVtyEvent dFocus
    (dData, dFocus, dAppState) <-
      makeForm eVtyEvent styling ePrev eNext $
      (,,,,) <$>
      border @@= fieldM (textField FormName Nothing (Just 1)) <*>=
      border @@= fieldM (passwordField FormPassword Nothing) <*>=
      padBottom (Pad 1) @@=
        fieldM (radioField [(FormX, X, "X"), (FormY, Y, "Y"), (FormZ, Z, "Z")]) <*>=
      fieldM (checkboxField FormQuestion "???") <*>=
      fieldM (listField [(FormListX, "X", X), (FormListY, "Y", Y), (FormListZ, "Z", Z)]) <*=
      field button

  let eQuit = eSubmit

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
