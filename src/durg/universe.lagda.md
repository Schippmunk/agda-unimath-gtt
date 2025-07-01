```agda
{-# OPTIONS #-}

module durg.universe where

open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.equivalences

open import durg.base

module _ (l : Level) where
  S-universe : UARel (UU l) l
  UARel._≅_ S-universe = _≃_
  UARel.ua S-universe = equiv-eq-equiv



```
