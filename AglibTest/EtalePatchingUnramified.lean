/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

import Aglib.RingTheory.Etale.MilnorPatching.Unramified
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.GroupTheory.Perm.Fin

open Polynomial
open scoped TensorProduct
open RingHom.Etale.MilnorPatching

noncomputable section

namespace AglibTest.EtalePatchingUnramified

universe u
variable (k : Type u) [Field k] (n : ℕ)

/-- The two actual polynomial endpoint maps. -/
def endpointMap : k[X] →+* k × k :=
  (Polynomial.evalRingHom (0 : k)).prod (Polynomial.evalRingHom (1 : k))

theorem endpointMap_surjective : Function.Surjective (endpointMap k) := by
  intro a
  refine ⟨C a.1 + C (a.2 - a.1) * X, ?_⟩
  ext <;> simp [endpointMap]

/-- The actual cyclic rotation at the first conductor endpoint. -/
def cyclicTwist : (Fin n → k × k) ≃ₐ[k × k] (Fin n → k × k) where
  toFun a i := ((a ((finRotate n).symm i)).1, (a i).2)
  invFun a i := ((a (finRotate n i)).1, (a i).2)
  left_inv a := by ext <;> simp only [Equiv.symm_apply_apply]
  right_inv a := by ext <;> simp only [Equiv.apply_symm_apply]
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

private abbrev conductorBase := fiberRing (endpointMap k) (algebraMap k (k × k))
private abbrev conductorCover :=
  fiberRing ((endpointMap k).compLeft (Fin n))
    ((cyclicTwist k n).toRingHom.comp ((algebraMap k (k × k)).compLeft (Fin n)))

local notation "P" => conductorBase k
local notation "Q" => conductorCover k n

attribute [local instance] FiniteFree.fstAlgebra FiniteFree.sndAlgebra
local instance normalizationAlgebra : Algebra P k[X] :=
  FiniteFree.fstAlgebra (endpointMap k) (algebraMap k (k × k))
local instance normalizationModule : Module P k[X] :=
  @Algebra.toModule P k[X] _ _ (normalizationAlgebra k)
local instance : Algebra P Q :=
  (FiniteFree.map (endpointMap k) (algebraMap k (k × k)) (cyclicTwist k n)).toAlgebra

/-- The canonical normalization comparison, over the actual polynomial ring. -/
example : k[X] ⊗[P] Q ≃ₐ[k[X]] (Fin n → k[X]) :=
  FiniteFree.fstTensorEquiv (endpointMap k) (algebraMap k (k × k)) (cyclicTwist k n)
    (endpointMap_surjective k)

/-- The canonical node comparison uses the literal diagonal field map. -/
example : k ⊗[P] Q ≃ₐ[k] (Fin n → k) :=
  FiniteFree.sndTensorEquiv (endpointMap k) (algebraMap k (k × k)) (cyclicTwist k n)
    (endpointMap_surjective k)

/-- The displayed seven-map cyclic conductor morphism is etale for all n,
without a supplied patching proposition or a characteristic restriction. -/
example :
    (fiberMap (endpointMap k) (algebraMap k (k × k))
      (algebraMap k[X] (Fin n → k[X])) (algebraMap k (Fin n → k))
      (algebraMap (k × k) (Fin n → k × k))
      ((endpointMap k).compLeft (Fin n))
      ((cyclicTwist k n).toRingHom.comp ((algebraMap k (k × k)).compLeft (Fin n)))
      (by apply RingHom.ext; intro p; rfl)
      (by
        apply RingHom.ext
        intro a
        exact (cyclicTwist k n).commutes (algebraMap k (k × k) a))).Etale :=
  FiniteFree.etale_map (endpointMap k) (algebraMap k (k × k)) (cyclicTwist k n)
    (endpointMap_surjective k)

end AglibTest.EtalePatchingUnramified
