/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.FiniteAlgebraNormLength
public import Mathlib.RingTheory.DualNumber
public import Mathlib.LinearAlgebra.Basis.Fin

/-!
# Consumers of the actual finite-algebra norm formula

These tests cover arbitrary units, possibly inseparable field extensions,
a genuine local square-zero algebra, a disconnected two-branch algebra,
and the zero algebra. They concern the determinant norm, not motivic
cohomology or its remaining geometric comparison maps.
-/

@[expose] public section

noncomputable section

namespace AglibTest.FiniteAlgebraNormLength

universe u v

variable {k : Type u} [Field k]

/-- The requested unit case is a specialization of the actual norm theorem. -/
theorem unitNorm {B : Type v} [CommRing B] [Algebra k B] [Module.Finite k B]
    [Fintype (MaximalSpectrum B)] (u : Bˣ) :
    Algebra.norm k (u : B) = ∏ p : MaximalSpectrum B,
      Algebra.norm k (Ideal.Quotient.mk p.asIdeal (u : B)) ^
        (Module.length (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime p.asIdeal)).toNat :=
  Algebra.norm_eq_prod_quotient_norm_pow_local_length (u : B)

/-- No separability hypothesis is introduced for finite field extensions. -/
theorem arbitraryFieldExtension {E : Type v} [Field E] [Algebra k E]
    [Module.Finite k E] [Fintype (MaximalSpectrum E)] (x : E) :
    Algebra.norm k x = ∏ p : MaximalSpectrum E,
      Algebra.norm k (Ideal.Quotient.mk p.asIdeal x) ^
        (Module.length (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime p.asIdeal)).toNat :=
  Algebra.norm_eq_prod_quotient_norm_pow_local_length x

/-- This test algebra contains an actual nonzero element with square zero. -/
theorem dualNumber_nonreduced :
    (DualNumber.eps : DualNumber k) ≠ 0 ∧ (DualNumber.eps : DualNumber k) ^ 2 = 0 := by
  constructor
  · intro h
    have := congrArg TrivSqZeroExt.snd h
    simp at this
  · exact DualNumber.eps_pow_two

/-- The determinant norm on the nonreduced algebra is the square of the
constant coefficient, including every nilpotent coefficient. -/
theorem dualNumber_norm (x : DualNumber k) : Algebra.norm k x = x.fst ^ 2 := by
  let e : Module.Basis (Fin 2) k (DualNumber k) := Module.Basis.finTwoProd k
  rw [Algebra.norm_eq_matrix_det e, Matrix.det_fin_two]
  rw [Algebra.leftMulMatrix_eq_repr_mul e x 0 0,
    Algebra.leftMulMatrix_eq_repr_mul e x 1 1,
    Algebra.leftMulMatrix_eq_repr_mul e x 0 1,
    Algebra.leftMulMatrix_eq_repr_mul e x 1 0]
  have h0 : e 0 = 1 := Module.Basis.finTwoProd_zero k
  have h1 : e 1 = DualNumber.eps := Module.Basis.finTwoProd_one k
  have hr0 (y : DualNumber k) : e.repr y 0 = y.fst :=
    congrFun (Module.Basis.coe_finTwoProd_repr y) 0
  have hr1 (y : DualNumber k) : e.repr y 1 = y.snd :=
    congrFun (Module.Basis.coe_finTwoProd_repr y) 1
  rw [h0, h1, hr0, hr1, hr0, hr1]
  simp [pow_two]

/-- The local square-zero algebra has length two over itself, witnessed by
its actual nilpotent ideal and constant-coefficient quotient exact sequence. -/
theorem dualNumber_length : Module.length (DualNumber k) (DualNumber k) = 2 := by
  let : Algebra (DualNumber k) k := TrivSqZeroExt.algebraBase k k
  let f : k →ₗ[DualNumber k] DualNumber k :=
    { toFun := TrivSqZeroExt.inr
      map_add' := TrivSqZeroExt.inr_add k
      map_smul' := fun r x => by
        change (TrivSqZeroExt.inr (r.fst * x) : DualNumber k) =
          r * TrivSqZeroExt.inr x
        ext <;> simp }
  let g : DualNumber k →ₗ[DualNumber k] k := Algebra.linearMap (DualNumber k) k
  have hf : Function.Injective f := TrivSqZeroExt.inr_injective
  have hg : Function.Surjective g := TrivSqZeroExt.fst_surjective
  have hex : Function.Exact f g := by
    intro x
    change x.fst = 0 ↔ ∃ y, TrivSqZeroExt.inr y = x
    constructor
    · intro hx
      exact ⟨x.snd, TrivSqZeroExt.ext hx.symm rfl⟩
    · rintro ⟨y, rfl⟩
      rfl
  have hlen : Module.length (DualNumber k) k = 1 :=
    (Module.length_eq_of_surjective (R := k) (M := k)
      (S := DualNumber k) hg).trans (Module.length_eq_one k k)
  simpa only [hlen, one_add_one_eq_two] using
    Module.length_eq_add_of_exact f g hf hg hex

/-- The literal localization appearing in the norm exponent has length two. -/
theorem dualNumber_local_length :
    Module.length (Localization.AtPrime (IsLocalRing.maximalIdeal (DualNumber k)))
      (Localization.AtPrime (IsLocalRing.maximalIdeal (DualNumber k))) = 2 := by
  rw [IsLocalRing.length_localization_maximalIdeal, dualNumber_length]

/-- The norm/length identity applies directly to the local nonreduced algebra. -/
theorem dualNumber_normLength [Fintype (MaximalSpectrum (DualNumber k))]
    (x : DualNumber k) :
    x.fst ^ 2 = ∏ p : MaximalSpectrum (DualNumber k),
      Algebra.norm k (Ideal.Quotient.mk p.asIdeal x) ^
        (Module.length (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime p.asIdeal)).toNat := by
  let : Module.Finite k (DualNumber k) := inferInstanceAs (Module.Finite k (k × k))
  rw [← dualNumber_norm]
  exact Algebra.norm_eq_prod_quotient_norm_pow_local_length x

/-- Both independent branches contribute to the actual product-algebra norm. -/
theorem product_norm (a b : k) : Algebra.norm k (a, b) = a * b := by
  rw [Algebra.norm_apply]
  have h : Algebra.lmul k (k × k) (a, b) =
      (LinearMap.mulLeft k a).prodMap (LinearMap.mulLeft k b) := by
    apply LinearMap.ext
    intro x
    rfl
  rw [h, LinearMap.det_prodMap, LinearMap.det_mulLeft, LinearMap.det_mulLeft]

/-- The all-point formula sees both components of a disconnected algebra. -/
theorem product_normLength [Fintype (MaximalSpectrum (k × k))] (a b : k) :
    a * b = ∏ p : MaximalSpectrum (k × k),
      Algebra.norm k (Ideal.Quotient.mk p.asIdeal (a, b)) ^
        (Module.length (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime p.asIdeal)).toNat := by
  rw [← product_norm]
  exact Algebra.norm_eq_prod_quotient_norm_pow_local_length (a, b)

/-- A zero algebra has zero-dimensional multiplication operators and norm one. -/
theorem zeroAlgebra_norm {B : Type v} [CommRing B] [Subsingleton B] [Algebra k B]
    (b : B) : Algebra.norm k b = 1 := by
  rw [Algebra.norm_apply]
  exact LinearMap.det_eq_one_of_subsingleton _

/-- The theorem agrees with the empty product in the zero-ring case. -/
theorem zeroAlgebra_emptyProduct {B : Type v} [CommRing B] [Subsingleton B]
    [Algebra k B] [Fintype (MaximalSpectrum B)] :
    (∏ p : MaximalSpectrum B,
      Algebra.norm k (Ideal.Quotient.mk p.asIdeal (0 : B)) ^
        (Module.length (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime p.asIdeal)).toNat) = 1 := by
  rw [← Algebra.norm_eq_prod_quotient_norm_pow_local_length]
  exact zeroAlgebra_norm 0

open Lean in
run_cmd do
  for name in #[``Module.det_lsmul_restrictScalars_eq_of_equiv,
      ``Module.det_lsmul_restrictScalars_eq_mul,
      ``Module.PrimeFiltrationFrom.det_lsmul_restrictScalars_eq_prod,
      ``Module.localized_length_ne_top_of_finiteDimensional,
      ``Module.det_lsmul_eq_prod_norm_pow_localized_length,
      ``Algebra.local_length_ne_top_of_finite,
      ``Algebra.norm_eq_prod_quotient_norm_pow_local_length_of_finite,
      ``IsLocalRing.length_localization_maximalIdeal,
      ``Algebra.norm_eq_quotient_norm_pow_length,
      ``unitNorm, ``arbitraryFieldExtension, ``dualNumber_nonreduced,
      ``dualNumber_norm, ``dualNumber_length, ``dualNumber_local_length,
      ``dualNumber_normLength, ``product_norm, ``product_normLength,
      ``zeroAlgebra_norm, ``zeroAlgebra_emptyProduct] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Finite-algebra norms and local lengths use only standard foundations."

end AglibTest.FiniteAlgebraNormLength
