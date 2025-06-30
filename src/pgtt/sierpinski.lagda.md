```agda
{-# OPTIONS --cohesion --flat-split #-}
module pgtt.sierpinski where

open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.universe-levels
open import foundation.identity-types
open import foundation-core.contractible-types
open import foundation.function-extensionality
open import foundation.identity-truncated-types
open import foundation.cartesian-product-types
open import foundation.sets

open import order-theory.meet-semilattices

open import modal-type-theory.flat-modality

private
  ϵ-♭ = counit-flat

module _ {l1 l2 : Level} (X : Order-Theoretic-Meet-Semilattice l1 l2) (@♭ l3 : Level) where
  private
    _≤_ = leq-Order-Theoretic-Meet-Semilattice X
    <X> = type-Order-Theoretic-Meet-Semilattice X
    _∧_ = meet-Order-Theoretic-Meet-Semilattice X

  join-structure : UU (l1 ⊔ lsuc l3)
  join-structure =
    (♭I : ♭ (UU l3))
    → ((ϵ-♭ ♭I) → <X>)
    → <X>

  module _ (⋁ : join-structure) where

    join-is-ub : UU (l1 ⊔ l2 ⊔ lsuc l3)
    join-is-ub =
      (♭I : ♭ (UU l3))
      → (φ : (ϵ-♭ ♭I) → <X>)
      → (i : ϵ-♭ ♭I)
      → φ i ≤ ⋁ ♭I φ

    join-is-ub-is-prop : is-prop (join-is-ub)
    join-is-ub-is-prop =
      is-prop-Π
        λ ♭I → is-prop-Π
          (λ φ → is-prop-Π
            (λ i → is-prop-leq-Order-Theoretic-Meet-Semilattice X (φ i) (⋁ ♭I φ)))

    join-is-least : UU (l1 ⊔ l2 ⊔ lsuc l3)
    join-is-least =
      (x : <X>)
      → (♭I : ♭ (UU l3))
      → (φ : (ϵ-♭ ♭I) → <X>)
      → ((i : ϵ-♭ ♭I) → φ i ≤ x)
      → ⋁ ♭I φ ≤ x

    join-is-least-is-prop : is-prop (join-is-least)
    join-is-least-is-prop =
      is-prop-Π
        (λ x → is-prop-Π
          (λ ♭I → is-prop-Π
            (λ φ → is-prop-Π
              (λ _ → is-prop-leq-Order-Theoretic-Meet-Semilattice X (⋁ ♭I φ) x) )))

    is-distributive : UU (l1 ⊔ lsuc l3)
    is-distributive =
      (x : <X>)
      → (♭I : ♭ (UU l3))
      → (φ : (ϵ-♭ ♭I) → <X>)
      → (x ∧ (⋁ ♭I φ)) ＝ (⋁ ♭I (λ i → x ∧ (φ i)))

    is-distributive-is-prop : is-prop (is-distributive)
    is-distributive-is-prop =
      is-prop-Π
        (λ x → is-prop-Π
          (λ ♭I → is-prop-Π
            (λ φ → is-set-type-Order-Theoretic-Meet-Semilattice
              X
              (x ∧ ⋁ ♭I φ)
              (⋁ ♭I (λ i → x ∧ φ i)))))


module _ {l1 l2 : Level} {@♭ l3 : Level} where
  frame : UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
  frame =
    Σ (Order-Theoretic-Meet-Semilattice l1 l2)
      λ X → Σ (join-structure X l3)
        λ ⋁ → (join-is-ub X l3 ⋁) × (join-is-least X l3 ⋁) × (is-distributive X l3 ⋁)
```
