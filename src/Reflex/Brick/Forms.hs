{-# language DeriveFunctor, StandaloneDeriving #-}
{-# language GADTs #-}
{-# language OverloadedStrings #-}
{-# language RecursiveDo #-}
{-# language ScopedTypeVariables #-}
{-# language TemplateHaskell #-}
module Reflex.Brick.Forms
  ( -- * Forms
    Form
  , makeForm
  , fieldM
  , field
  , styled
  , (@@=)
    -- ** Combining functions
  , besides
  , aboves
  , (<*>+)
  , (<*+)
  , (*>+)
  , (<*>=)
  , (<*=)
  , (*>=)
    -- * Form elements
  , textField
  , passwordField
  , checkboxField
  , radioField
  , listField
  , makeButton
  , textFieldBase
    -- * @FormField@
  , FormField(..)
  , emptyField
  , combineFieldsWith
    -- ** Lenses
  , fieldData
  , fieldWidget
  , fieldNames
  , fieldValidation
    -- * Utilities
  , onSuccess
  , onFailure
  )
where

import Reflex
import Reflex.Brick

import Brick.AttrMap (AttrMap)
import Brick.Focus
  (FocusRing, focusRing, focusRingCursor, focusNext, focusPrev, focusGetCurrent)
import Brick.Forms (focusedFormInputAttr)
import Brick.Types (Widget, Location(..))
import Brick.Widgets.Core
  ((<=>), (<+>), emptyWidget, txt, vBox, withDefAttr, showCursor)
import Brick.Widgets.Edit
  (Editor, editorText, editContentsL, renderEditor, getEditContents)
import Control.Monad (guard)
import Control.Monad.Fix (MonadFix)
import Control.Monad.Reader (ReaderT, runReaderT, ask)
import Control.Monad.Trans (lift)
import Data.Bifunctor (first)
import Data.Dependent.Map (DMap)
import Data.Foldable (foldl')
import Data.Function ((&))
import Data.Functor.Identity (Identity)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Map (Map)
import Data.Map.Monoidal (MonoidalMap)
import Data.Maybe (fromMaybe, isJust)
import Data.Set (Set)
import Data.Text (Text)
import Data.Validation (Validation(..))
import Lens.Micro ((%~), (^.), _1, _2, mapped)
import Lens.Micro.TH (makeLenses)

import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Map.Monoidal as MonoidalMap
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified Data.Text.Zipper as Zipper
import qualified Graphics.Vty.Input.Events as Vty

-- | From 'Brick.Widgets.Edit.handleEditorEvent'
handleEditorEvent ::
  Reflex t =>
  Event t ([Vty.Modifier], DMap RBKey Identity) -> -- ^ Terminal key events
  Event t (Editor Text n -> Editor Text n)
handleEditorEvent e = (editContentsL %~) <$> eModify
  where
    keyEvents =
      fan $
      fmapMaybe
        (\(ms, d) -> if null ms then Just d else Nothing)
        e

    ctrlEvents =
      fan $
      fmapMaybe
        (\(ms, d) -> if ms == [Vty.MCtrl] then Just d else Nothing)
        e

    eModify =
      mergeWith (.)
      [ Zipper.gotoBOL <$ select ctrlEvents (RBChar 'a')
      , Zipper.gotoEOL <$ select ctrlEvents (RBChar 'e')
      , Zipper.deleteChar <$ select ctrlEvents (RBChar 'd')
      , Zipper.killToEOL <$ select ctrlEvents (RBChar 'k')
      , Zipper.killToBOL <$ select ctrlEvents (RBChar 'u')
      , Zipper.breakLine <$ select keyEvents RBEnter
      , Zipper.deleteChar <$ select keyEvents RBDel
      , fmapMaybe
          (\c ->
             if c /= '\t'
             then Just $ Zipper.insertChar c
             else Nothing)
          (select keyEvents RBAnyChar)
      , Zipper.moveUp <$ select keyEvents RBUp
      , Zipper.moveDown <$ select keyEvents RBDown
      , Zipper.moveLeft <$ select keyEvents RBLeft
      , Zipper.moveRight <$ select keyEvents RBRight
      , Zipper.deletePrevChar <$ select keyEvents RBBS
      ]

data FormField t n e a
  = FormField
  { _fieldData :: Dynamic t a
  , _fieldWidget :: Dynamic t (Widget n)
  , _fieldNames :: [n]
  , _fieldValidation :: Dynamic t (Validation (MonoidalMap n e) a)
  }
makeLenses ''FormField
deriving instance Reflex t => Functor (FormField t n e)

emptyField :: Reflex t => a -> FormField t n e a
emptyField a =
  FormField
  { _fieldData = pure a
  , _fieldWidget = pure emptyWidget
  , _fieldNames = []
  , _fieldValidation = pure $ Success a
  }

combineFieldsWith ::
  (Reflex t, Ord n, Semigroup e) =>
  (Widget n -> Widget n -> Widget n) ->
  FormField t n e (a -> b) ->
  FormField t n e a ->
  FormField t n e b
combineFieldsWith f a b =
  FormField
  { _fieldData = _fieldData a <*> _fieldData b
  , _fieldWidget = f <$> _fieldWidget a <*> _fieldWidget b
  , _fieldNames = _fieldNames a <> _fieldNames b
  , _fieldValidation = (<*>) <$> _fieldValidation a <*> _fieldValidation b
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

data  Form t n ev e m a where
  FormPure :: a ->  Form t n ev e m a
  FormMap :: (a -> b) ->  Form t n ev e m a ->  Form t n ev e m b
  FormLift ::
    (Dynamic t (Maybe n) ->
     m (FormField t n e a)) ->
     Form t n ev e m a
  FormStyle :: (Widget n -> Widget n) ->  Form t n ev e m a ->  Form t n ev e m a
  FormVert ::  Form t n ev e m (a -> b) ->  Form t n ev e m a ->  Form t n ev e m b
  FormHoriz ::  Form t n ev e m (a -> b) ->  Form t n ev e m a ->  Form t n ev e m b

instance Functor ( Form t n ev e m) where; fmap = FormMap

-- | Horizontal apply
(<*>+) ::  Form t n ev e m (a -> b) ->  Form t n ev e m a ->  Form t n ev e m b
(<*>+) = FormHoriz
infixl 4 <*>+

-- | Horizontal left-apply
(<*+) ::  Form t n ev e m a ->  Form t n ev e m b ->  Form t n ev e m a
(<*+) a b = const <$> a <*>+ b
infixl 4 <*+

-- | Horizontal right-apply
(*>+) ::  Form t n ev e m a ->  Form t n ev e m b ->  Form t n ev e m b
(*>+) a b = const id <$> a <*>+ b
infixl 4 *>+

-- | Vertical apply
(<*>=) ::  Form t n ev e m (a -> b) ->  Form t n ev e m a ->  Form t n ev e m b
(<*>=) = FormVert
infixl 4 <*>=

-- | Vertical left-apply
(<*=) ::  Form t n ev e m a ->  Form t n ev e m b ->  Form t n ev e m a
(<*=) a b = const <$> a <*>= b
infixl 4 <*=

-- | Vertical right-apply
(*>=) ::  Form t n ev e m a ->  Form t n ev e m b ->  Form t n ev e m b
(*>=) a b = const id <$> a <*>= b
infixl 4 *>=

fieldM ::
  (Dynamic t (Maybe n) ->
   m (FormField t n e a)) ->
   Form t n ev e m a
fieldM = FormLift

field :: Applicative m => FormField t n e a -> Form t n ev e m a
field f = fieldM (\_ -> pure f)

-- |
-- Use a transformation function to change the way a 'Form' is rendered
styled :: (Widget n -> Widget n) ->  Form t n ev e m a ->  Form t n ev e m a
styled = FormStyle

-- | Infix operator for 'styled'
(@@=) :: (Widget n -> Widget n) ->  Form t n ev e m a ->  Form t n ev e m a
(@@=) = styled

infixr 5 @@=

-- | Lay out 'Form's left-to-right, collecting their results
besides :: [ Form t n ev e m a] ->  Form t n ev e m [a]
besides [] = FormPure []
besides (f : fs) = FormHoriz (FormMap (:) f) (besides fs)

-- | Lay out 'Form's top-to-bottom, collecting their results
aboves :: [ Form t n ev e m a] ->  Form t n ev e m [a]
aboves [] = FormPure []
aboves (f : fs) = FormVert (FormMap (:) f) (aboves fs)

makeForm ::
  forall e t n ev m a.
  ( Reflex t, MonadHold t m, MonadFix m
  , Ord n, Semigroup e
  ) =>
  AttrMap -> -- ^ Styling
  Event t () -> -- ^ Cycle backward through form
  Event t () -> -- ^ Cycle forward through form
  Form t n ev e m a -> -- ^ The form
  m
    ( Dynamic t a
    , Dynamic t (Validation (Map n e) a)
    , Dynamic t (Maybe n)
    , Dynamic t (ReflexBrickAppState n)
    )
makeForm style ePrev eNext form = do
  rec
    let dFocus = focusGetCurrent <$> dFocusRing
    ff <- runReaderT (go form) dFocus
    dFocusRing <- dynFocusRing ePrev eNext $ _fieldNames ff
  pure $
    ( _fieldData ff
    , coerceDynamic (_fieldValidation ff)
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
       Form t n ev e m x ->
      ReaderT (Dynamic t (Maybe n)) m (FormField t n e x)
    go (FormPure a) = pure $ emptyField a
    go (FormMap f ma) = fmap f <$> go ma
    go (FormLift ma) = ask >>= lift . ma
    go (FormStyle f ma) = do
      a <- go ma
      pure $ a & fieldWidget.mapped %~ f
    go (FormVert mf ma) = combineFieldsWith (<=>) <$> go mf <*> go ma
    go (FormHoriz mf ma) = combineFieldsWith (<+>) <$> go mf <*> go ma

textFieldBase ::
  forall t n ev e m.
  ( Reflex t, MonadHold t m, MonadFix m
  , Ord n, Show n
  ) =>
  ([Text] -> Widget n) -> -- ^ How to render contents
  n -> -- ^ Widget name (must be unique)
  Maybe Text -> -- ^ Initial contents
  Maybe Int -> -- ^ Line limit
  ([Text] -> Validation e [Text]) -> -- ^ Validation function
  EventSelector t (RBEvent n ev) -> -- ^ Terminal events
  Dynamic t (Maybe n) -> -- ^ Current focus
  m (FormField t n e [Text])
textFieldBase renderLines name def limit validate eVtyEvent dFocus = do
  let initial = editorText name limit (fromMaybe mempty def)
  dInFocus <- holdUniqDyn $ (== Just name) <$> dFocus
  dEditor <-
    foldDyn ($) initial $
    gate (current dInFocus) (handleEditorEvent $ select eVtyEvent RBKey)
  let dData = getEditContents <$> dEditor
  pure $
    FormField
    { _fieldData = dData
    , _fieldWidget =
      (\focus -> addStyle focus . renderEditor renderLines focus) <$>
      dInFocus <*>
      dEditor
    , _fieldNames = [name]
    , _fieldValidation = first (MonoidalMap.singleton name) . validate <$> dData
    }
  where
    addStyle focus = if focus then withDefAttr focusedFormInputAttr else id

textField ::
  forall t n ev e m.
  ( Reflex t, MonadHold t m, MonadFix m
  , Ord n, Show n
  ) =>
  n -> -- ^ Widget name (must be unique)
  Maybe Text -> -- ^ Initial contents
  Maybe Int -> -- ^ Line limit
  ([Text] -> Validation e [Text]) -> -- ^ Validation function
  EventSelector t (RBEvent n ev) -> -- ^ Terminal events
  Dynamic t (Maybe n) -> -- ^ Current focus
  m (FormField t n e [Text])
textField name def limit =
  textFieldBase
    (txt . Text.intercalate "\n")
    name
    def
    limit

passwordField ::
  forall t n ev e m.
  ( Reflex t, MonadHold t m, MonadFix m
  , Ord n, Show n
  ) =>
  n -> -- ^ Widget name (must be unique)
  Maybe Text -> -- ^ Initial contents
  (Text -> Validation e Text) -> -- ^ Validation function
  EventSelector t (RBEvent n ev) -> -- ^ Terminal events
  Dynamic t (Maybe n) -> -- ^ Current focus
  m (FormField t n e Text)
passwordField name def validate eVtyEvent =
  (fmap Text.concat <$>) .
  textFieldBase
    (txt . stars)
    name
    def
    (Just 1)
    (fmap pure . validate . Text.concat)
    eVtyEvent
  where
    stars s = Text.replicate (Text.length $ Text.concat s) (Text.singleton '*')

radioField ::
  ( Reflex t, MonadHold t m
  , Eq n
  ) =>
  NonEmpty (n, a, Text) -> -- ^ Selections
  Event t () -> -- ^ Select event
  Dynamic t (Maybe n) -> -- ^ Current focus
  m (FormField t n e a)
radioField choices eSelect dFocus = do
  let
    names = foldr (\a b -> (^.) a _1 : b) [] choices
    initial = let x = NonEmpty.head choices in (x ^. _1, x ^. _2)

  let dHighlighted = (>>= \n -> (,) n <$> lookupValue n choices) <$> dFocus
  dSelected <- holdDyn initial $ attachWithMaybe const (current dHighlighted) eSelect

  let dData = (^. _2) <$> dSelected

  pure $
    FormField
    { _fieldData = dData
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
    , _fieldValidation = Success <$> dData
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
  n -> -- ^ Name
  Text -> -- ^ Label
  Event t () -> -- ^ Select events
  Dynamic t (Maybe n) -> -- ^ Current focus
  m (FormField t n e Bool)
checkboxField name label eSelect dFocus = do
  let dHighlighted = (==Just name) <$> dFocus
  rec
    dChecked <-
      holdDyn False $
      (not <$>
      current dChecked <@
      attachWithMaybe
        (\h _ -> guard h)
        (current dHighlighted)
        eSelect)

  pure $
    FormField
    { _fieldData = dChecked
    , _fieldWidget =
        (\h c -> addStyle h $ txt $ check c <> label) <$>
        dHighlighted <*>
        dChecked
    , _fieldNames = [name]
    , _fieldValidation = Success <$> dChecked
    }
  where
    addStyle h =
      if h
      then showCursor name (Location (1, 0)) . withDefAttr focusedFormInputAttr
      else id

    check c = if c then "[x] " else "[ ] "

listField ::
  forall t n e m a.
  ( Reflex t, MonadHold t m, MonadFix m
  , Ord n
  ) =>
  [(n, Text, a)] -> -- ^ Choices
  Event t () -> -- ^ Selection event
  Dynamic t (Maybe n) -> -- ^ Current focus
  m (FormField t n e [a])
listField choices eSelect eFocus = do
  let
    names = fmap (\(x, _, _) -> x) choices

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
      gate (current dInFocus) eSelect

  let
    dData =
      (\ixs ->
         foldr
           (\(n, _, a) b -> if n `Set.member` ixs then a : b else b)
           []
           choices) <$>
      dIxs

  pure $
    FormField
    { _fieldData = dData
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
    , _fieldValidation = Success <$> dData
    }

  where
    addStyle n b =
      if b
      then showCursor n (Location (0, 0)) . withDefAttr focusedFormInputAttr
      else id

makeButton ::
  forall t n e m.
  ( Reflex t, MonadHold t m, MonadFix m
  , Eq n
  ) =>
  n -> -- ^ name
  Text -> -- ^ value
  Event t () -> -- ^ Button pressed event
  Dynamic t (Maybe n) -> -- ^ Current focus
  m (Event t (), FormField t n e ())
makeButton name value ePressed dFocus =
  pure
  ( gate ((==Just name) <$> current dFocus) ePressed
  , FormField
    { _fieldData = pure ()
    , _fieldWidget =
      (\f -> addStyle (f == Just name) (txt $ "[" <> value <> "]")) <$>
      dFocus
    , _fieldNames = [name]
    , _fieldValidation = pure $ Success ()
    }
  )
  where
    addStyle b =
      if b
      then withDefAttr focusedFormInputAttr
      else id

onSuccess :: Reflex t => Dynamic t (Validation e a) -> Event t b -> Event t a
onSuccess =
  attachWithMaybe (\v _ -> case v of; Success a -> Just a; _ -> Nothing) . current

onFailure :: Reflex t => Dynamic t (Validation e a) -> Event t b -> Event t e
onFailure =
  attachWithMaybe (\v _ -> case v of; Failure a -> Just a; _ -> Nothing) . current
