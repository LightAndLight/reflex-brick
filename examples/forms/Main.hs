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
import Reflex.Brick.Forms
  ( (<*=), (<*>=), (@@=)
  , makeForm, fieldM, field
  , textField, passwordField, checkboxField, radioField, listField
  , makeButton
  , onSuccess
  )

import Brick.AttrMap (AttrMap, attrMap)
import Brick.Forms (focusedFormInputAttr)
import Brick.Types (Padding(..))
import Brick.Util (on)
import Brick.Widgets.Border (border)
import Brick.Widgets.Core ((<=>), txt, padBottom)
import Control.Monad (guard)
import Control.Monad.Fix (MonadFix)
import Data.Function ((&))
import Data.Validation (Validation(..))
import Lens.Micro ((%~), _last)

import qualified Data.Text as Text
import qualified Graphics.Vty.Attributes as Vty
import qualified Graphics.Vty.Input.Events as Vty

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
    (dData, dValidated, dFocus, dAppState) <-
      makeForm @() eVtyEvent styling ePrev eNext $
      (,,,,) <$>
      border @@= fieldM (textField FormName Nothing (Just 1) Success) <*>=
      border @@= fieldM (passwordField FormPassword Nothing Success) <*>=
      padBottom (Pad 1) @@=
        fieldM (radioField [(FormX, X, "X"), (FormY, Y, "Y"), (FormZ, Z, "Z")]) <*>=
      fieldM (checkboxField FormQuestion "???") <*>=
      fieldM (listField [(FormListX, "X", X), (FormListY, "Y", Y), (FormListZ, "Z", Z)]) <*=
      field button

  let eQuit = () <$ onSuccess dValidated eSubmit

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
