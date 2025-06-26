```agda
{-# OPTIONS --cohesion --flat-split #-}
module pgtt.sierpinski where

open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.universe-levels
open import foundation.identity-types
open import foundation-core.contractible-types
open import foundation.function-extensionality

open import order-theory.meet-semilattices

open import modal-type-theory.flat-modality

module _ (@♭ l1 : Level) (@♭ I : UU l1) {l2 : Level}  where
  is-prop-♭-Π : (X : ♭ I → UU l2)
    → ((i : ♭ I) → is-prop (X i))
    → is-prop ((i : ♭ I) → X i)
  is-prop-♭-Π _ = is-prop-Π

  is-prop-♭-→ : (X : UU l2) → is-prop X → is-prop (♭ I → X)
  is-prop-♭-→ _ = is-prop-function-type

-- is-prop-♭-Π-implicit : {@♭ l1 : Level}
--   → {l2 : Level}
--   → {X : UU l1 → UU l2}
--   → (X-is-prop : {@♭ I : UU l1} → is-prop (X I))
--   → is-prop ({@♭ I : UU l1} → X I)
-- is-prop-♭-Π-implicit {X=X} X-is-prop = {!!}


module _ (@♭ l1 : Level) (@♭ I : UU l1) {l2 : Level} (X : UU l2) where
  discrete-family : UU (l1 ⊔ l2)
  discrete-family = ♭ I → X


module _ {l1 : Level} (X : Meet-Semilattice l1) (@♭ l2 : Level) where

  private
    _≤_ = leq-Meet-Semilattice X
    <X> = type-Meet-Semilattice X

  -- join structure
  join-structures : UU (l1 ⊔ lsuc l2)
  join-structures = (@♭ I : UU l2)
    → discrete-family l2 I <X>
    → <X>

  join-is-ub : (⋁ : join-structures) → Prop (l1 ⊔ lsuc l2)
  pr1 (join-is-ub ⋁) = (@♭ I : UU l2)
    → (f : discrete-family l2 I <X>)
    → (i : ♭ I)
    → f i ≤ ⋁ I f
  pr2 (join-is-ub ⋁) = a4 -- a4
    where
      a1 : (@♭ I : UU l2)
        → (f : discrete-family l2 I <X>)
        → (i : ♭ I) → is-prop (f i ≤ ⋁ I f)
      a1 I f i = is-prop-leq-Meet-Semilattice X (f i) (⋁ I f)

      a2 : (@♭ I : UU l2)
        → (f : discrete-family l2 I <X>)
        → is-prop ((i : ♭ I) → (f i ≤ ⋁ I f))
      a2 I f = is-prop-Π λ i → a1 I f i

      a3 : (@♭ I : UU l2)
        → is-prop ((f : discrete-family l2 I <X>) → (i : ♭ I) → (f i ≤ ⋁ I f))
      a3 I = is-prop-Π (λ f → a2 I f)

      g : (@♭ I : UU l2) → UU (l1 ⊔ l2)
      g I = (f : discrete-family l2 I <X>)
        → (i : ♭ I)
        → (f i ≤ ⋁ I f)

      -- this requires function extensionality for Pi-types with flat domain
      a4 : is-prop ((@♭ I : UU l2) → g I)
      a4 = is-prop-all-elements-equal λ r s → {!!}


  --                                                            --
  -- join-is-lub : Prop {!!}                                    --
  -- pr1 join-is-lub = {!!}                                     --
  -- p                                                          --
  -- r2 join-is-lub = {!!}
```
