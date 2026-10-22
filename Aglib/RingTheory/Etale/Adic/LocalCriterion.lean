/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Flat.Adic.FiniteFree
public import Aglib.RingTheory.Etale.FiniteFlatPurity
public import Mathlib.RingTheory.Smooth.Flat

/-!
# Etaleness of a finite local algebra from all adic reductions

All positive reductions being etale first implies that the original finite
module is free. The discriminant of its basis is a unit after the first
quotient, hence a unit in the original local ring. This argument permits any
proper ideal and includes the zero algebra. It uses neither completeness nor
an algebraization theorem.
-/

@[expose] public section

noncomputable section

open Module TensorProduct

namespace Algebra

/-- A finite free algebra over a Noetherian local ring is etale if its
reduction modulo a proper ideal is etale. This proves the discriminant step
before supplying the all-order freeness construction. -/
theorem etale_of_etale_quotient_of_free {R B : Type*}
    [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [CommRing B] [Algebra R B] [Module.Finite R B] [Module.Free R B]
    (J : Ideal R) (hJ : J ≠ ⊤)
    (h : Etale (R ⧸ J) ((R ⧸ J) ⊗[R] B)) : Etale R B := by
  classical
  let b := Module.Free.chooseBasis R B
  apply (etale_iff_isUnit_discr_of_basis b).mpr
  have : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  have : IsLocalHom (algebraMap R (R ⧸ J)) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  apply isUnit_of_map_unit (algebraMap R (R ⧸ J))
  rw [← discr_baseChange b]
  exact (etale_iff_isUnit_discr_of_basis (TensorProduct.basis (R ⧸ J) b)).mp h

/-- A finite algebra over a Noetherian local ring is etale if every positive
reduction modulo powers of a proper ideal is etale over its quotient ring.
The tensor products are the original algebra scalar extensions. -/
theorem etale_of_etale_quotient_pow {R B : Type*}
    [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [CommRing B] [Algebra R B] [Module.Finite R B]
    (J : Ideal R) (hJ : J ≠ ⊤)
    (h : ∀ n : ℕ, 0 < n → Etale (R ⧸ J ^ n) ((R ⧸ J ^ n) ⊗[R] B)) :
    Etale R B := by
  have : Module.Free R B := Module.free_of_flat_quotient_pow J hJ fun n hn ↦ by
    let := h n hn
    infer_instance
  exact etale_of_etale_quotient_of_free (J ^ 1)
    (ne_top_of_le_ne_top hJ (Ideal.pow_le_self Nat.one_ne_zero)) (h 1 Nat.zero_lt_one)

end Algebra
