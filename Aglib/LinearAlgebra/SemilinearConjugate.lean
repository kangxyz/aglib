/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Group.Equiv.Basic

/-! # Semilinear conjugation through original additive comparisons

Scalar operators on the additive target are retained explicitly. No module
structure is transported to that target.
-/

@[expose] public section

namespace AddEquiv

variable {R M H : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid H]

/-- Conjugate an additive operator using its actual scalar intertwining law. -/
def semilinearConjugate (E : M ≃+ H) (σ : R →+* R)
    (A : R → H →+ H) (F : H →+ H)
    (hE : ∀ r x, E (r • x) = A r (E x))
    (hF : ∀ r y, F (A r y) = A (σ r) (F y)) : M →ₛₗ[σ] M where
  toAddHom := (E.symm.toAddMonoidHom.comp (F.comp E.toAddMonoidHom)).toAddHom
  map_smul' r x := by
    apply E.injective
    change E (E.symm (F (E (r • x)))) = E (σ r • E.symm (F (E x)))
    rw [E.apply_symm_apply]
    calc
      F (E (r • x)) = F (A r (E x)) := congrArg F (hE r x)
      _ = A (σ r) (F (E x)) := hF r (E x)
      _ = E (σ r • E.symm (F (E x))) := by
        rw [hE, E.apply_symm_apply]

/-- The semilinear map retains the original additive operator under comparison. -/
theorem semilinearConjugate_apply (E : M ≃+ H) (σ : R →+* R)
    (A : R → H →+ H) (F : H →+ H)
    (hE : ∀ r x, E (r • x) = A r (E x))
    (hF : ∀ r y, F (A r y) = A (σ r) (F y)) (x : M) :
    E (semilinearConjugate E σ A F hE hF x) = F (E x) :=
  E.apply_symm_apply _

end AddEquiv
