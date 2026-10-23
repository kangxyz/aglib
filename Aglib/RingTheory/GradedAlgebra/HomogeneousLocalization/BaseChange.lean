/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.GradedAlgebra.HomogeneousLocalization.DegreeOne
public import Mathlib.RingTheory.GradedAlgebra.TensorProduct
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Arbitrary scalar extension of degree-one homogeneous charts

The original homogeneous chart is identified with its dehomogenizing
quotient. The native tensor/quotient comparison then gives the chart of
the full scalar-extended graded algebra. The formula on tensor fractions
retains the original numerator, coefficient and denominator maps.

No flatness, domain, Noetherianity or finite generation is assumed. The
scheme pullback and the blowup tautological-module comparison are separate
consumers of this actual ring isomorphism.
-/

@[expose] public noncomputable section

open TensorProduct

universe u

namespace HomogeneousLocalization.Away

variable (R : Type u) [CommRing R] {D : Type u} [CommRing D] [Algebra R D]
  (G : ℕ → Submodule R D) [GradedAlgebra G] {f : D}

/-- The original coefficient-ring action through the original degree-zero component. -/
@[instance_reducible]
def scalarAlgebra (f : D) : Algebra R (Away G f) :=
  ((fromZeroRingHom G (Submonoid.powers f)).comp (algebraMap R (G 0))).toAlgebra

/-- The quotient equivalence respects the actual coefficient-ring action. -/
def degreeOneQuotientAlgEquiv (hf : f ∈ G 1) :
    letI := scalarAlgebra R G f
    Away G f ≃ₐ[R] (D ⧸ dehomogenizingIdeal (f := f)) := by
  letI := scalarAlgebra R G f
  refine { degreeOneQuotientEquiv G hf with commutes' := ?_ }
  intro r
  change degreeOneQuotientEquiv G hf
      (fromZeroRingHom G (Submonoid.powers f) (algebraMap R (G 0) r)) =
    Ideal.Quotient.mk (dehomogenizingIdeal (f := f)) (algebraMap R D r)
  exact degreeOneQuotientEquiv_fromZero G hf (algebraMap R (G 0) r)

/-- The algebra comparison has exactly the original ring-equivalence map. -/
@[simp]
theorem degreeOneQuotientAlgEquiv_apply (hf : f ∈ G 1) (x : Away G f) :
    letI := scalarAlgebra R G f
    degreeOneQuotientAlgEquiv R G hf x = degreeOneQuotientEquiv G hf x := by
  let := scalarAlgebra R G f
  rfl

variable (S : Type u) [CommRing S] [Algebra R S]

/-- The native grading on the full tensor algebra. -/
abbrev scalarGrading (n : ℕ) : Submodule S (S ⊗[R] D) := (G n).baseChange S

omit [GradedAlgebra G] in
/-- The original degree-one denominator remains homogeneous after scalar extension. -/
theorem scalarDenominator_mem (hf : f ∈ G 1) :
    (1 ⊗ₜ[R] f : S ⊗[R] D) ∈ scalarGrading R G S 1 :=
  Submodule.tmul_mem_baseChange_of_mem _ hf

/-- The original dehomogenizing relation is taken to the same tensor relation. -/
theorem dehomogenizingIdeal_map :
    (dehomogenizingIdeal (f := f)).map
        (Algebra.TensorProduct.includeRight : D →ₐ[R] S ⊗[R] D) =
      dehomogenizingIdeal (f := (1 ⊗ₜ[R] f : S ⊗[R] D)) := by
  simp only [dehomogenizingIdeal, Ideal.map_span, Set.image_singleton,
    map_sub, map_one, Algebra.TensorProduct.includeRight_apply]

/-- Arbitrary scalar extension of the original degree-one homogeneous chart. -/
def scalarExtensionEquiv (hf : f ∈ G 1) :
    letI := scalarAlgebra R G f
    letI := scalarAlgebra S (scalarGrading R G S) (1 ⊗ₜ[R] f)
    S ⊗[R] Away G f ≃ₐ[S] Away (scalarGrading R G S) (1 ⊗ₜ[R] f) := by
  letI := scalarAlgebra R G f
  letI := scalarAlgebra S (scalarGrading R G S) (1 ⊗ₜ[R] f)
  exact (Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S)
      (degreeOneQuotientAlgEquiv R G hf)).trans
    ((Algebra.TensorProduct.tensorQuotientEquiv (R := R) S D S
        (dehomogenizingIdeal (f := f))).trans
      ((Ideal.quotientEquivAlgOfEq S (dehomogenizingIdeal_map R S (f := f))).trans
        (degreeOneQuotientAlgEquiv S (scalarGrading R G S)
          (scalarDenominator_mem R G S hf)).symm))

/-- The original tensor fraction is taken to the same scalar-extended numerator. -/
theorem scalarExtensionEquiv_tmul_mk (hf : f ∈ G 1)
    (n : ℕ) (a : D) (ha : a ∈ G n) (s : S) :
    letI := scalarAlgebra R G f
    letI := scalarAlgebra S (scalarGrading R G S) (1 ⊗ₜ[R] f)
    scalarExtensionEquiv R G S hf
        (s ⊗ₜ[R] Away.mk G hf n a (by simpa only [smul_eq_mul, mul_one] using ha)) =
      Away.mk (scalarGrading R G S) (scalarDenominator_mem R G S hf) n
        (s ⊗ₜ[R] a)
        (by simpa only [smul_eq_mul, mul_one] using
          (Submodule.tmul_mem_baseChange_of_mem s ha)) := by
  let := scalarAlgebra R G f
  let := scalarAlgebra S (scalarGrading R G S) (1 ⊗ₜ[R] f)
  apply (degreeOneQuotientAlgEquiv S (scalarGrading R G S)
    (scalarDenominator_mem R G S hf)).injective
  simp only [scalarExtensionEquiv, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply,
    Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
    AlgEquiv.coe_toAlgHom, AlgEquiv.coe_refl,
    degreeOneQuotientAlgEquiv_apply, degreeOneQuotientEquiv_mk,
    Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul,
    Ideal.quotientEquivAlgOfEq_mk]
  rfl

end HomogeneousLocalization.Away
