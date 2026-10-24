/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Blowup.RegularPair.Differentials
public import Aglib.LinearAlgebra.ExteriorPower.CyclicCokernel

/-!
# The one-pole exterior bound on the original regular-pair chart

The coefficient map is the original Kähler base-change map, and the extra
generator is the differential of the
original chart root. No free differential module or residue-field assumption
is used. The saturated-chart specialization retains both regular-pair premises.
-/

@[expose] public noncomputable section

open Polynomial TensorProduct

universe u v w

namespace KaehlerDifferential

/-- The native exterior-image formula, with its original ring and module instances
fixed before specialization to a concrete blowup algebra. -/
def baseChangeExteriorImageBound
    (Λ : Type w) (R : Type u) (S : Type v)
    [CommRing Λ] [CommRing R] [CommRing S]
    [Algebra Λ R] [Algebra R S] [Algebra Λ S] [IsScalarTower Λ R S]
    (x : R) : Prop :=
  ∀ (n : ℕ) (α : ⋀[S]^n (_root_.KaehlerDifferential Λ S)),
    algebraMap R S x • α ∈ LinearMap.range
      (exteriorPower.map (R := S)
        (M := S ⊗[R] _root_.KaehlerDifferential Λ R)
        (N := _root_.KaehlerDifferential Λ S) n (mapBaseChange Λ R S))

end KaehlerDifferential

namespace IsAdjoinRoot

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  {x y : R} (h : IsAdjoinRoot S (Localization.Away.pairPolynomial x y))
  (Λ : Type w) [CommRing Λ] [Algebra Λ R] [Algebra Λ S]
  [IsScalarTower Λ R S]

/-- Actual coefficient forms and the differential of the original root generate. -/
theorem pairDifferential_generated_by_base_and_root (v : KaehlerDifferential Λ S) :
    ∃ p : S ⊗[R] KaehlerDifferential Λ R, ∃ a : S,
      v = KaehlerDifferential.mapBaseChange Λ R S p +
        a • KaehlerDifferential.D Λ S h.root := by
  obtain ⟨z, hz⟩ := (S ∙ pairDifferentialRelation h Λ).mkQ_surjective
    (pairDifferentialEquiv h Λ v)
  have hv := congrArg (pairDifferentialEquiv h Λ).symm hz
  change (pairDifferentialEquiv h Λ).symm (pairDifferentialMk h Λ z) =
    (pairDifferentialEquiv h Λ).symm (pairDifferentialEquiv h Λ v) at hv
  rw [pairDifferentialEquiv_symm_mk, LinearEquiv.symm_apply_apply] at hv
  exact ⟨z.1, z.2, hv.symm⟩

/-- The exceptional equation times the original root differential is a scalar form. -/
theorem pair_exceptional_smul_root_mem_range :
    algebraMap R S x • KaehlerDifferential.D Λ S h.root ∈
      LinearMap.range (KaehlerDifferential.mapBaseChange Λ R S) := by
  have hr : algebraMap R S x * h.root = algebraMap R S y := by
    have hz := h.aeval_root_self
    simpa only [Localization.Away.pairPolynomial, aeval_sub, aeval_mul,
      aeval_C, aeval_X, sub_eq_zero] using hz
  have hd := congrArg (KaehlerDifferential.D Λ S) hr
  simp only [Derivation.leibniz] at hd
  refine ⟨(1 : S) ⊗ₜ[R] KaehlerDifferential.D Λ R y -
    h.root ⊗ₜ[R] KaehlerDifferential.D Λ R x, ?_⟩
  calc
    KaehlerDifferential.mapBaseChange Λ R S
        ((1 : S) ⊗ₜ[R] KaehlerDifferential.D Λ R y -
          h.root ⊗ₜ[R] KaehlerDifferential.D Λ R x) =
        KaehlerDifferential.D Λ S (algebraMap R S y) -
          h.root • KaehlerDifferential.D Λ S (algebraMap R S x) := by
      simp only [map_sub, KaehlerDifferential.mapBaseChange_tmul,
        KaehlerDifferential.map_D, one_smul]
    _ = algebraMap R S x • KaehlerDifferential.D Λ S h.root :=
      sub_eq_iff_eq_add.mpr hd.symm

include h in
/-- Multiplication by the actual exceptional equation puts every raw exterior
form in the image of the original scalar exterior map. -/
theorem pair_exceptional_smul_exterior_mem_range (n : ℕ)
    (α : ⋀[S]^n (KaehlerDifferential Λ S)) :
    algebraMap R S x • α ∈
      LinearMap.range (exteriorPower.map (R := S)
        (M := S ⊗[R] KaehlerDifferential Λ R) (N := KaehlerDifferential Λ S)
        n (KaehlerDifferential.mapBaseChange Λ R S)) :=
  exteriorPower.smul_mem_range_map_of_cyclic_cokernel
    (R := S) (P := S ⊗[R] KaehlerDifferential Λ R) (Q := KaehlerDifferential Λ S)
    (KaehlerDifferential.mapBaseChange Λ R S) (KaehlerDifferential.D Λ S h.root)
    (algebraMap R S x) (pairDifferential_generated_by_base_and_root h Λ)
    (pair_exceptional_smul_root_mem_range h Λ) n α

end IsAdjoinRoot

namespace Localization.Away

variable {R : Type u} [CommRing R] (x y : R)
  (Λ : Type w) [CommRing Λ] [Algebra Λ R]

/-- The literal quotient chart, with its original coefficient algebra. -/
theorem pairQuotient_exceptional_smul_exterior_mem_range (n : ℕ)
    (α : ⋀[pairQuotient x y]^n (KaehlerDifferential Λ (pairQuotient x y))) :
    algebraMap R (pairQuotient x y) x • α ∈ LinearMap.range
      (exteriorPower.map (R := pairQuotient x y)
        (M := pairQuotient x y ⊗[R] KaehlerDifferential Λ R)
        (N := KaehlerDifferential Λ (pairQuotient x y))
        n (KaehlerDifferential.mapBaseChange Λ R (pairQuotient x y))) :=
  IsAdjoinRoot.pair_exceptional_smul_exterior_mem_range
    (R := R) (S := pairQuotient x y) (x := x) (y := y)
    (pairChartPresentation x y) Λ n α

/-- The same bound on the actual saturated blowup algebra, using the proved
regular-pair chart equivalence rather than an assumed presentation. -/
theorem saturatedPair_exceptional_smul_exterior_mem_range
    (hx : IsSMulRegular R x) (hy : IsSMulRegular (R ⧸ Ideal.span {x}) y) :
    KaehlerDifferential.baseChangeExteriorImageBound Λ R
      (saturatedChart R (Ideal.span {x, y}) x) x :=
  IsAdjoinRoot.pair_exceptional_smul_exterior_mem_range
    (R := R) (S := saturatedChart R (Ideal.span {x, y}) x) (x := x) (y := y)
    (saturatedPairPresentation x y hx hy) Λ

end Localization.Away
