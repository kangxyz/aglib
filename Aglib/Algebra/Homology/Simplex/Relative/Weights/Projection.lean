/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.Simplex.Relative.Weights.Maps

/-!
# Original Laurent coefficient projections onto individual weights

Taking the actual coefficient of an allowed original exponent gives a native
cosimplicial and chain map to the unchanged relative-simplex weight complex.
Restriction preserves that coefficient when the smaller tuple permits the
weight and makes it zero otherwise. No finite-vertex premise is required.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicTopology

universe u v

namespace MvPolynomial

variable {ι : Type v} (R : Type u) [CommRing R]

/-- Original coordinate restriction retains every exponent allowed on the
smaller tuple, with its actual native coefficient. -/
theorem coordinateLaurentDegreeMap_weight_coeff (d : ℤ) {m n : ℕ}
    (a : Fin (n + 1) → ι) (f : Fin (m + 1) → Fin (n + 1))
    (e : coordinateLaurentWeight (ι := ι) d) (ha : coordinateWeightAllowed a e)
    (hf : coordinateWeightAllowed (a ∘ f) e)
    (x : coordinateGrading R (coordinateTupleSet (a ∘ f)) d) :
    (coordinateLaurentDegreeMap R (coordinateTupleSet_comp_subset a f) d x).val.coeff
        (coordinateWeightExponent a e ha) =
      x.val.coeff (coordinateWeightExponent (a ∘ f) e hf) := by
  change (Finsupp.mapDomain (coordinateExponentInclusion (coordinateTupleSet_comp_subset a f))
    x.val.coeff) (coordinateWeightExponent a e ha) = _
  have he : coordinateExponentInclusion (coordinateTupleSet_comp_subset a f)
      (coordinateWeightExponent (a ∘ f) e hf) = coordinateWeightExponent a e ha :=
    Subtype.ext rfl
  rw [← he]
  exact Finsupp.mapDomain_apply_of_injective
    (coordinateExponentInclusion_injective (coordinateTupleSet_comp_subset a f)) _ _

/-- A weight not allowed on the smaller tuple has zero actual coefficient
after its original coordinate restriction. -/
theorem coordinateLaurentDegreeMap_weight_coeff_eq_zero (d : ℤ) {m n : ℕ}
    (a : Fin (n + 1) → ι) (f : Fin (m + 1) → Fin (n + 1))
    (e : coordinateLaurentWeight (ι := ι) d) (ha : coordinateWeightAllowed a e)
    (hf : ¬ coordinateWeightAllowed (a ∘ f) e)
    (x : coordinateGrading R (coordinateTupleSet (a ∘ f)) d) :
    (coordinateLaurentDegreeMap R (coordinateTupleSet_comp_subset a f) d x).val.coeff
      (coordinateWeightExponent a e ha) = 0 := by
  change (Finsupp.mapDomain (coordinateExponentInclusion (coordinateTupleSet_comp_subset a f))
    x.val.coeff) (coordinateWeightExponent a e ha) = 0
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨b, hb⟩
  apply hf
  apply (coordinateExponentAllowed_iff_negativeSupport (a ∘ f) e.val).mp
  have he : b.val = e.val := congrArg
    (fun z : coordinateExponentMonoid (coordinateTupleSet a) => z.val) hb
  exact he ▸ b.property

/-- Projection onto one actual weight takes the literal original Laurent
coefficient on every tuple permitting that exponent. -/
def coordinateLaurentTupleWeightProjection (d : ℤ)
    (e : coordinateLaurentWeight (ι := ι) d) (n : ℕ) :
    coordinateLaurentTupleCochains (ι := ι) R d n →ₗ[R]
      RelativeSimplex.Cochains R (coordinateNegativeSupport e.val) n where
  toFun x a := (x a.val).val.coeff (coordinateWeightExponent a.val e a.property)
  map_add' x y := by
    funext a
    simp
  map_smul' r x := by
    funext a
    simp

/-- The original coefficient projection commutes with every tuple-position
restriction, including faces that omit required negative coordinates. -/
theorem coordinateLaurentTupleWeightProjection_naturality (d : ℤ)
    (e : coordinateLaurentWeight (ι := ι) d) {m n : ℕ}
    (f : Fin (m + 1) → Fin (n + 1))
    (x : coordinateLaurentTupleCochains (ι := ι) R d m) :
    coordinateLaurentTupleWeightProjection R d e n
        (coordinateLaurentTuplePositionMap R d f x) =
      RelativeSimplex.positionMap f (coordinateLaurentTupleWeightProjection R d e m x) := by
  classical
  funext a
  change (coordinateLaurentDegreeMap R (coordinateTupleSet_comp_subset a.val f) d
      (x (a.val ∘ f))).val.coeff (coordinateWeightExponent a.val e a.property) =
    RelativeSimplex.extendByZero (coordinateLaurentTupleWeightProjection R d e m x) (a.val ∘ f)
  by_cases hf : coordinateWeightAllowed (a.val ∘ f) e
  · rw [RelativeSimplex.extendByZero, dite_eq_left hf]
    exact coordinateLaurentDegreeMap_weight_coeff R d a.val f e a.property hf _
  · rw [RelativeSimplex.extendByZero, dite_eq_right hf]
    exact coordinateLaurentDegreeMap_weight_coeff_eq_zero R d a.val f e a.property hf _

/-- Literal weight coefficients define a genuine native cosimplicial projection. -/
def coordinateLaurentWeightCosimplicialProjection (d : ℤ)
    (e : coordinateLaurentWeight (ι := ι) d) :
    coordinateLaurentTupleCosimplicial (ι := ι) R d ⟶
      RelativeSimplex.cosimplicial R (coordinateNegativeSupport e.val) where
  app n := ModuleCat.ofHom (coordinateLaurentTupleWeightProjection R d e n.len)
  naturality {_ _} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact coordinateLaurentTupleWeightProjection_naturality R d e f.toOrderHom x

/-- The actual original-coefficient chain projection onto one unchanged
relative-simplex weight complex, without a finite-vertex hypothesis. -/
def coordinateLaurentWeightComplexProjection (d : ℤ)
    (e : coordinateLaurentWeight (ι := ι) d) :
    coordinateLaurentTupleComplex (ι := ι) R d ⟶
      RelativeSimplex.complex R (coordinateNegativeSupport e.val) :=
  (alternatingCofaceMapComplex _).map (coordinateLaurentWeightCosimplicialProjection R d e)

@[simp]
theorem coordinateLaurentWeightComplexProjection_f (d : ℤ)
    (e : coordinateLaurentWeight (ι := ι) d) (n : ℕ) :
    (coordinateLaurentWeightComplexProjection R d e).f n =
      ModuleCat.ofHom (coordinateLaurentTupleWeightProjection R d e n) := rfl

/-- The original coefficient projection retracts its literal single-monomial insertion. -/
@[simp]
theorem coordinateLaurentTupleWeightProjection_injection (d : ℤ)
    (e : coordinateLaurentWeight (ι := ι) d) (n : ℕ)
    (x : RelativeSimplex.Cochains R (coordinateNegativeSupport e.val) n) :
    coordinateLaurentTupleWeightProjection R d e n
      (coordinateLaurentTupleWeightInjection R d e n x) = x := by
  classical
  funext a
  simp [coordinateLaurentTupleWeightProjection, coordinateLaurentTupleWeightInjection,
    a.property, AddMonoidAlgebra.coeff_single]

/-- Distinct original weights have zero cross-coefficient projection. -/
theorem coordinateLaurentTupleWeightProjection_injection_of_ne (d : ℤ)
    (e e' : coordinateLaurentWeight (ι := ι) d) (he : e' ≠ e) (n : ℕ)
    (x : RelativeSimplex.Cochains R (coordinateNegativeSupport e'.val) n) :
    coordinateLaurentTupleWeightProjection R d e n
      (coordinateLaurentTupleWeightInjection R d e' n x) = 0 := by
  classical
  funext a
  by_cases ha : coordinateWeightAllowed a.val e'
  · have hne : coordinateWeightExponent a.val e' ha ≠
        coordinateWeightExponent a.val e a.property := by
      intro h
      exact he (Subtype.ext (congrArg
        (fun z : coordinateExponentMonoid (coordinateTupleSet a.val) => z.val) h))
    simp [coordinateLaurentTupleWeightProjection, coordinateLaurentTupleWeightInjection,
      ha, coordinateLaurentTupleWeightSingle_val, AddMonoidAlgebra.coeff_single, hne]
  · simp [coordinateLaurentTupleWeightProjection, coordinateLaurentTupleWeightInjection, ha]

/-- The actual coefficient chain projection retracts its actual monomial chain map. -/
@[simp]
theorem coordinateLaurentWeightComplexMap_projection (d : ℤ)
    (e : coordinateLaurentWeight (ι := ι) d) :
    coordinateLaurentWeightComplexMap R d e ≫ coordinateLaurentWeightComplexProjection R d e =
      𝟙 _ := by
  ext n x
  exact coordinateLaurentTupleWeightProjection_injection R d e n x

/-- Distinct original monomial chain maps are killed by the coefficient projection. -/
theorem coordinateLaurentWeightComplexMap_projection_of_ne (d : ℤ)
    (e e' : coordinateLaurentWeight (ι := ι) d) (he : e' ≠ e) :
    coordinateLaurentWeightComplexMap R d e' ≫ coordinateLaurentWeightComplexProjection R d e =
      0 := by
  ext n x
  exact coordinateLaurentTupleWeightProjection_injection_of_ne R d e e' he n x

end MvPolynomial
