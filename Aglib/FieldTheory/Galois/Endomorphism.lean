/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# The endomorphism equivalence of a finite Galois extension

The original linear-combination map sending `c` to `x ↦ ∑ g, c g * g x`
is an equivalence for a finite Galois extension. Artin independence supplies
injectivity, and the Galois degree formula supplies the dimension equality.
This is a field-level result; it does not imply surjectivity of the corresponding
map on an integral closure before the additional unramifiedness comparison.
-/

@[expose] public section

noncomputable section

namespace IsGalois

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [Fintype (L ≃ₐ[K] L)]

/-- Every base-linear endomorphism of a finite Galois field extension is uniquely
a linear combination of its field automorphisms. The equivalence keeps the
original coefficient-to-endomorphism map. -/
def endomorphismEquiv : ((L ≃ₐ[K] L) → L) ≃ₗ[L] Module.End K L :=
  LinearEquiv.ofInjectiveOfFinrankEq
    (Fintype.linearCombination L fun g : L ≃ₐ[K] L => g.toLinearMap)
    (linearIndependent_iff_injective_fintypeLinearCombination.mp
      ((linearIndependent_algHom_toLinearMap K L L).comp
        (fun g : L ≃ₐ[K] L => g.toAlgHom) AlgEquiv.coe_toAlgHom_injective))
    (by
      rw [Module.finrank_fintype_fun_eq_card, Module.finrank_linearMap_self]
      exact Nat.card_eq_fintype_card.symm.trans (IsGalois.card_aut_eq_finrank K L))

/-- Evaluation of the field equivalence is the literal sum of weighted automorphisms. -/
theorem endomorphismEquiv_apply (c : (L ≃ₐ[K] L) → L) (x : L) :
    endomorphismEquiv K L c x = ∑ g, c g * g x := by
  change (Fintype.linearCombination L (fun g : L ≃ₐ[K] L => g.toLinearMap) c) x = _
  simp [Fintype.linearCombination_apply]

end IsGalois
