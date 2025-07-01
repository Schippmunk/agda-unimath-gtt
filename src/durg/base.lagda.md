```agda
{-# OPTIONS --cohesion --flat-split #-}

module durg.base where

open import foundation.dependent-pair-types
open import foundation.universe-levels
open import foundation.identity-types
open import foundation.propositions
open import foundation-core.equivalences
open import foundation-core.invertible-maps
open import foundation-core.dependent-identifications
open import foundation-core.transport-along-identifications

-- syntax dependent-identification p b b' = b ＝⟨ p ⟩ b'

implicit-dependent-identification : {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {a a' : A}
  (b : B a) → (p : a ＝ a') → (b' : B a') → UU l2
implicit-dependent-identification {B = B} b p b' = (tr B p b) ＝ b'

syntax implicit-dependent-identification b p b' = b ＝⟨ p ⟩ b'


module _ {lA : Level} where

  record UARel (A : UU lA) (l≅A : Level) : UU (lA ⊔ lsuc l≅A) where
    no-eta-equality
    constructor uarel
    field
      _≅_ : A → A → UU l≅A
      ua : (a a' : A) → (a ≅ a') ≃ (a ＝ a')

    uaIso : (a a' : A) → invertible-map (a ≅ a') (a ＝ a')
    uaIso a a' = (map-equiv (ua a a')) , (is-invertible-is-equiv (is-equiv-map-equiv (ua a a')))

    ≅→＝ : {a a' : A} (p : a ≅ a') → a ＝ a'
    ≅→＝ {a} {a'} = map-invertible-map (uaIso a a')

    ＝→≅ : {a a' : A} (p : a ＝ a') → a ≅ a'
    ＝→≅ {a} {a'} = map-inv-invertible-map (uaIso a a')

    ρ : (a : A) → a ≅ a
    ρ a = ＝→≅ refl
    

module _ {lA l≅A lB : Level} where
  record DUARel
    {A : UU lA} (S-A : UARel A l≅A) (B : A → UU lB) (l≅B : Level) : UU (lA ⊔ lB ⊔ l≅A ⊔ lsuc l≅B) where
    no-eta-equality
    constructor duarel
    open UARel S-A
    field
      _≅ᴰ⟨_⟩_ : {a a' : A} → B a → a ≅ a' → B a' → UU l≅B
      uaᴰ : {a a' : A} (b : B a) (p : a ≅ a') (b' : B a') → (b ≅ᴰ⟨ p ⟩ b') ≃ b ＝⟨ ≅→＝ p ⟩ b'
```
