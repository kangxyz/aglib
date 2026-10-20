/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

import Aglib.RingTheory.Etale.MilnorPatching.FiniteFree
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.GroupTheory.Perm.Fin

open Polynomial
open RingHom.Etale.MilnorPatching

noncomputable section

namespace AglibTest.EtalePatching

universe u

variable (k : Type u) [Field k] (n : ℕ)

/-- The actual two-endpoint conductor boundary. -/
def endpointMap : k[X] →+* k × k :=
  (Polynomial.evalRingHom (0 : k)).prod (Polynomial.evalRingHom (1 : k))

theorem endpointMap_surjective : Function.Surjective (endpointMap k) := by
  intro a
  refine ⟨C a.1 + C (a.2 - a.1) * X, ?_⟩
  ext <;> simp [endpointMap]

/-- Rotation on one endpoint and identity on the other: the cyclic clutching
transition, rather than a common-base extension of an untwisted cover. -/
def cyclicTwist : (Fin n → k × k) ≃ₐ[k × k] (Fin n → k × k) where
  toFun a i := ((a ((finRotate n).symm i)).1, (a i).2)
  invFun a i := ((a (finRotate n i)).1, (a i).2)
  left_inv a := by ext <;> simp only [Equiv.symm_apply_apply]
  right_inv a := by ext <;> simp only [Equiv.apply_symm_apply]
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- All finite cyclic conductor maps are genuinely finite and flat. This
statement supplies no formal-unramified or etale conclusion. -/
example :
    (FiniteFree.map (endpointMap k) (algebraMap k (k × k)) (cyclicTwist k n)).Finite ∧
    (FiniteFree.map (endpointMap k) (algebraMap k (k × k)) (cyclicTwist k n)).Flat :=
  FiniteFree.finite_flat_map (endpointMap k) (algebraMap k (k × k))
    (endpointMap_surjective k) (cyclicTwist k n)

end AglibTest.EtalePatching
