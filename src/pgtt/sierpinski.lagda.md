```agda
{-# OPTIONS --cohesion --flat-split #-}
module pgtt.sierpinski where

open import foundation.universe-levels

open import order-theory.meet-semilattices

open import modal-type-theory.flat-modality


module _ {l1 : Level} (X : Meet-Semilattice l1) {@♭ l2 : Level} where

  flat-joins : UU (l1 ⊔ lsuc l2)
  flat-joins = (f : {@♭ I : UU l2} → I → type-Meet-Semilattice X) → type-Meet-Semilattice X


```
