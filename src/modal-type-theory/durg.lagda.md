```agda
{-# OPTIONS --cohesion --flat-split #-}
module modal-type-theory.durg where

open import foundation.dependent-pair-types
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.equivalences

open import durg.base
open import durg.universe

open import modal-type-theory.flat-modality
open import modal-type-theory.flat-discrete-crisp-types

private
  ϵ-♭ = counit-flat


module _ {@♭ l1 : Level} where
  flat-universe : UU (lsuc l1)
  flat-universe = ♭ (UU l1)

  S-flat-universe : UARel flat-universe l1
  S-flat-universe .UARel._≅_ (intro-flat A) (intro-flat B)
    = ♭ ((S-universe l1) .UARel._≅_ A B)
  S-flat-universe .UARel.ua (intro-flat A) (intro-flat B) = {!!}


  disctypes : UU (lsuc l1)
  disctypes = Σ (♭ (UU l1)) f
    where
      f : ♭ (UU l1) → UU l1
      f (intro-flat A) = is-flat-discrete-crisp A



```
