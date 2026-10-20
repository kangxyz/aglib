/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module


public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Valuation.Integral
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Invariant.Profinite
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.Galois.Profinite

/-!
# Residual Galois quotient for a complete nonarchimedean field

Supporting P16 residual-quotient prerequisite for
`K2-015#lem:k2015-frobenius`, mathematical snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`. The spectral-norm construction derives the actual
residue homomorphism, its exact reduction square, continuity, and surjectivity
under the stated hypotheses; no residual map or surjectivity premise is supplied.
The identification `residueClosureEquiv` is chosen compatibly with the base
residue field. No independence of that choice is asserted. Elliptic/root
specialization, arithmetic same-class injection, and the full specialization
comparison remain outside this module.
-/

/-!
Extraction source: `R5Lab.Aglib.RingTheory.Valuation.ResidualGalois`,
R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`b57e1fca9972876935bb58af9f65184ee38525b19f804fb7f8d73cc1528533d7`.
Historical source locators retain their original basis. -/

@[expose] public section

noncomputable section

open Polynomial IsLocalRing
open scoped NNReal Topology

namespace Valuation.ResidualGalois

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K]

/-- The actual multiplicative extension of the complete nonarchimedean norm.
Supporting P16 residual-quotient prerequisite for
`K2-015#lem:k2015-frobenius` at `e73d98b1b5c1e5abcdebf7d058e436d792b87982`;
see the module scope and chosen-identification boundary. -/
def closureValuation : Valuation (AlgebraicClosure K) ℝ≥0 where
  toFun x := ⟨spectralNorm K (AlgebraicClosure K) x, spectralNorm_nonneg x⟩
  map_zero' := by apply Subtype.ext; exact spectralNorm_zero
  map_one' := by apply Subtype.ext; exact spectralNorm_one
  map_mul' x y := by
    apply Subtype.ext
    exact spectralAlgNorm_mul x y
  map_add_le_max' x y := isNonarchimedean_spectralNorm x y

abbrev ClosureIntegers := (closureValuation K).valuationSubring

@[simp] theorem closureValuation_algebraMap (x : K) :
    closureValuation K (algebraMap K (AlgebraicClosure K) x) = ‖x‖₊ := by
  apply Subtype.ext
  exact spectralNorm_extends x

@[simp] theorem closureValuation_aut (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (x : AlgebraicClosure K) : closureValuation K (g x) = closureValuation K x := by
  apply Subtype.ext
  exact (spectralNorm_eq_of_equiv g x).symm

variable (V : ValuationSubring K) [hV : Fact (∀ x : K, x ∈ V ↔ ‖x‖₊ ≤ 1)]

/-- The actual inclusion from the base valuation ring into the closure valuation ring.
Supporting P16 residual-quotient prerequisite for
`K2-015#lem:k2015-frobenius` at `e73d98b1b5c1e5abcdebf7d058e436d792b87982`;
see the module scope and chosen-identification boundary. -/
def integerMap : V →+* ClosureIntegers K where
  toFun x := ⟨algebraMap K (AlgebraicClosure K) x,
    by simpa only [Valuation.mem_valuationSubring_iff, closureValuation_algebraMap]
      using (hV.out x).mp x.property⟩
  map_zero' := by ext; exact map_zero _
  map_one' := by ext; exact map_one _
  map_add' x y := by ext; exact map_add _ _ _
  map_mul' x y := by ext; exact map_mul _ _ _

instance closureIntegersAlgebra : Algebra V (ClosureIntegers K) :=
  (integerMap K V).toAlgebra

instance closureIntegersScalarTower : IsScalarTower V (ClosureIntegers K)
    (AlgebraicClosure K) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

instance integerMap_isLocalHom : IsLocalHom (integerMap K V) where
  map_nonunit a ha := by
    have hv :=
      (Valuation.valuationSubring.integers (closureValuation K)).isUnit_iff_valuation_eq_one.mp ha
    change closureValuation K (algebraMap K (AlgebraicClosure K) a) = 1 at hv
    rw [closureValuation_algebraMap] at hv
    have ha0 : (a : K) ≠ 0 := by
      intro h
      simp [h] at hv
    have hainv : (a : K)⁻¹ ∈ V := (hV.out _).mpr (by simp [nnnorm_inv, hv])
    apply IsUnit.of_mul_eq_one (⟨(a : K)⁻¹, hainv⟩ : V)
    apply Subtype.ext
    exact mul_inv_cancel₀ ha0

instance closureIntegersAlgebra_isLocalHom :
    IsLocalHom (algebraMap V (ClosureIntegers K)) := integerMap_isLocalHom K V

/-- Restriction of each actual absolute Galois automorphism to the unit ball.
Supporting P16 residual-quotient prerequisite for
`K2-015#lem:k2015-frobenius` at `e73d98b1b5c1e5abcdebf7d058e436d792b87982`;
see the module scope and chosen-identification boundary. -/
def integerAut (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    ClosureIntegers K ≃ₐ[V] ClosureIntegers K where
  toFun x := ⟨g x, by simpa only [Valuation.mem_valuationSubring_iff,
    closureValuation_aut] using x.property⟩
  invFun x := ⟨g.symm x, by simpa only [Valuation.mem_valuationSubring_iff,
    closureValuation_aut] using x.property⟩
  left_inv x := by ext; exact g.symm_apply_apply x
  right_inv x := by ext; exact g.apply_symm_apply x
  map_add' x y := by ext; exact map_add g _ _
  map_mul' x y := by ext; exact map_mul g _ _
  commutes' x := by ext; exact g.commutes x

/-- The induced residue action, built by restricting the actual Galois automorphisms.
Supporting P16 residual-quotient prerequisite for
`K2-015#lem:k2015-frobenius` at `e73d98b1b5c1e5abcdebf7d058e436d792b87982`;
see the module scope and chosen-identification boundary. -/
def residueHom : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →*
    (ResidueField (ClosureIntegers K) ≃ₐ[ResidueField V]
      ResidueField (ClosureIntegers K)) where
  toFun g := ResidueField.mapAlgEquiv' (integerAut K V g)
  map_one' := by
    ext z
    obtain ⟨a, rfl⟩ := residue_surjective z
    rfl
  map_mul' g h := by
    ext z
    obtain ⟨a, rfl⟩ := residue_surjective z
    rfl

/-- Exact compatibility with reduction of the same integral element.
Supporting P16 residual-quotient prerequisite for
`K2-015#lem:k2015-frobenius` at `e73d98b1b5c1e5abcdebf7d058e436d792b87982`;
see the module scope and chosen-identification boundary. -/
@[simp] theorem residueHom_residue
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (a : ClosureIntegers K) :
    residueHom K V g (residue (ClosureIntegers K) a) =
      residue (ClosureIntegers K) (integerAut K V g a) := rfl

/-- Supporting P16 residual-quotient prerequisite for
`K2-015#lem:k2015-frobenius` at `e73d98b1b5c1e5abcdebf7d058e436d792b87982`;
see the module scope and chosen-identification boundary. -/
theorem residue_isAlgClosed {L : Type*} [Field L] [IsAlgClosed L]
    (A : ValuationSubring L) : IsAlgClosed (ResidueField A) := by
  apply IsAlgClosed.of_exists_root
  intro f hf hirr
  obtain ⟨p, hpmap, hpdeg, hpmon⟩ :=
    lifts_and_degree_eq_and_monic
      (mem_lifts_of_surjective (residue_surjective (R := A)) f) hf
  have hp0 : p.degree ≠ 0 := by
    rw [hpdeg]
    exact hirr.degree_pos.ne'
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_aeval_eq_zero_of_injective L
    Subtype.val_injective p hp0
  have hxi : IsIntegral A x := ⟨p, hpmon, hx⟩
  have hA : A.valuation.Integers A :=
    ⟨Subtype.val_injective, A.valuation_le_one,
      fun r hr => ⟨⟨r, (A.valuation_le_one_iff r).mp hr⟩, rfl⟩⟩
  let a : A := ⟨x, (A.valuation_le_one_iff x).mp (hA.isIntegral_iff_v_le_one.mp hxi)⟩
  have ha : algebraMap A L a = x := rfl
  refine ⟨residue A a, ?_⟩
  rw [← hpmap, eval_map, eval₂_at_apply]
  have hpa : p.eval a = 0 := by
    apply FaithfulSMul.algebraMap_injective A L
    simpa only [Polynomial.aeval_def, ← ha, eval₂_at_apply, map_zero] using hx
  simp [hpa]

/-- Every closure integer is integral over the actual base valuation ring.
Supporting P16 residual-quotient prerequisite for
`K2-015#lem:k2015-frobenius` at `e73d98b1b5c1e5abcdebf7d058e436d792b87982`;
see the module scope and chosen-identification boundary. -/
theorem closureInteger_isIntegral (a : ClosureIntegers K) :
    IsIntegral V (a : AlgebraicClosure K) := by
  let p := minpoly K (a : AlgebraicClosure K)
  have hpmon : p.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral _)
  have hpcoeff : ∀ n : ℕ, ‖p.coeff n‖ ≤ 1 :=
    (spectralValue_le_one_iff hpmon).mp a.property
  have hplift : p ∈ lifts (algebraMap V K) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨p.coeff n, (hV.out _).mpr (by exact_mod_cast hpcoeff n)⟩, rfl⟩
  obtain ⟨q, hq, _, hqmon⟩ := lifts_and_degree_eq_and_monic hplift hpmon
  refine ⟨q, hqmon, ?_⟩
  have hroot := minpoly.aeval K (a : AlgebraicClosure K)
  change aeval (a : AlgebraicClosure K) p = 0 at hroot
  rw [← hq, aeval_map_algebraMap] at hroot
  exact hroot

instance closureIntegersIntegral : Algebra.IsIntegral V (ClosureIntegers K) where
  isIntegral a :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom V (ClosureIntegers K)
      (AlgebraicClosure K)) Subtype.val_injective).mp (closureInteger_isIntegral K V a)

/-- The spectral valuation ring is the integral closure of the same base ring.
Supporting P16 residual-quotient prerequisite for
`K2-015#lem:k2015-frobenius` at `e73d98b1b5c1e5abcdebf7d058e436d792b87982`;
see the module scope and chosen-identification boundary. -/
instance closureIntegers_isIntegralClosure :
    IsIntegralClosure (ClosureIntegers K) V (AlgebraicClosure K) where
  algebraMap_injective := Subtype.val_injective
  isIntegral_iff := by
    intro x
    constructor
    · intro hx
      have hx' : IsIntegral (ClosureIntegers K) x := hx.tower_top
      exact ⟨⟨x, (Valuation.valuationSubring.integers
        (closureValuation K)).isIntegral_iff_v_le_one.mp hx'⟩, rfl⟩
    · rintro ⟨a, rfl⟩
      exact closureInteger_isIntegral K V a

/-- Canonical identification with the literal integral-closure subalgebra.
Supporting P16 residual-quotient prerequisite for
`K2-015#lem:k2015-frobenius` at `e73d98b1b5c1e5abcdebf7d058e436d792b87982`;
see the module scope and chosen-identification boundary. -/
def integralClosureEquiv : integralClosure V (AlgebraicClosure K) ≃ₐ[V] ClosureIntegers K :=
  IsIntegralClosure.equiv V (integralClosure V (AlgebraicClosure K))
    (AlgebraicClosure K) (ClosureIntegers K)

@[simp] theorem integralClosureEquiv_coe (a : integralClosure V (AlgebraicClosure K)) :
    (integralClosureEquiv K V a : AlgebraicClosure K) = (a : AlgebraicClosure K) :=
  IsIntegralClosure.algebraMap_equiv V (integralClosure V (AlgebraicClosure K))
    (AlgebraicClosure K) (ClosureIntegers K) a

instance closureResidueIsAlgClosure :
    IsAlgClosure (ResidueField V) (ResidueField (ClosureIntegers K)) where
  isAlgClosed := residue_isAlgClosed (ClosureIntegers K)
  isAlgebraic := by
    have : Algebra.IsIntegral V (ResidueField (ClosureIntegers K)) :=
      inferInstanceAs (Algebra.IsIntegral V
        ((ClosureIntegers K) ⧸ maximalIdeal (ClosureIntegers K)))
    let : Algebra.IsIntegral (ResidueField V) (ResidueField (ClosureIntegers K)) :=
      Algebra.IsIntegral.tower_top V
    infer_instance

/-- A chosen compatible identification of the constructed residue closure.
Supporting P16 residual-quotient prerequisite for
`K2-015#lem:k2015-frobenius` at `e73d98b1b5c1e5abcdebf7d058e436d792b87982`;
see the module scope and chosen-identification boundary. -/
def residueClosureEquiv : ResidueField (ClosureIntegers K) ≃ₐ[ResidueField V]
    AlgebraicClosure (ResidueField V) := IsAlgClosure.equiv _ _ _

/-- The actual residue homomorphism, before adding its continuity and surjectivity proofs.
Supporting P16 residual-quotient prerequisite for
`K2-015#lem:k2015-frobenius` at `e73d98b1b5c1e5abcdebf7d058e436d792b87982`;
see the module scope and chosen-identification boundary. -/
def absoluteResidueHom : Field.absoluteGaloisGroup K →*
    Field.absoluteGaloisGroup (ResidueField V) :=
  (AlgEquiv.autCongr (residueClosureEquiv K V)).toMonoidHom.comp (residueHom K V)

@[simp] theorem absoluteResidueHom_residue
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (a : ClosureIntegers K) :
    AlgEquiv.toAlgHom (absoluteResidueHom K V g)
      (residueClosureEquiv K V (residue (ClosureIntegers K) a)) =
    residueClosureEquiv K V (residue (ClosureIntegers K) (integerAut K V g a)) := by
  change residueClosureEquiv K V ((residueHom K V g)
    ((residueClosureEquiv K V).symm
      (residueClosureEquiv K V (residue (ClosureIntegers K) a)))) = _
  rw [AlgEquiv.symm_apply_apply]
  rfl

def integerAutHom : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →*
    (ClosureIntegers K ≃ₐ[V] ClosureIntegers K) where
  toFun := integerAut K V
  map_one' := by ext a; rfl
  map_mul' g h := by ext a; rfl

instance closureIntegersAction :
    MulSemiringAction (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (ClosureIntegers K) where
  smul g a := ⟨g a, by simpa only [Valuation.mem_valuationSubring_iff,
    closureValuation_aut] using a.property⟩
  one_smul a := by ext; rfl
  mul_smul g h a := by ext; rfl
  smul_zero g := by ext; exact map_zero g
  smul_one g := by ext; exact map_one g
  smul_add g a b := by ext; exact map_add g _ _
  smul_mul g a b := by ext; exact map_mul g _ _

instance closureIntegers_smulCommClass :
    SMulCommClass (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) V (ClosureIntegers K) where
  smul_comm g c a := (integerAut K V g).toLinearMap.map_smul c a

instance closureIntegersInvariant [PerfectField K] :
    Algebra.IsInvariant V (ClosureIntegers K)
      (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) where
  isInvariant a ha := by
    obtain ⟨b, hb⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (a : AlgebraicClosure K)).mpr
      (fun g => congrArg Subtype.val (ha g))
    have hbV : b ∈ V := (hV.out b).mpr (by
      rw [← closureValuation_algebraMap K b, hb]
      exact a.property)
    refine ⟨⟨b, hbV⟩, ?_⟩
    exact Subtype.ext hb

section Surjectivity

local instance : TopologicalSpace (ClosureIntegers K) := ⊥
local instance : DiscreteTopology (ClosureIntegers K) := ⟨rfl⟩

local instance closureIntegers_continuousSMul :
    ContinuousSMul (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (ClosureIntegers K) := by
  rw [continuousSMul_iff_stabilizer_isOpen]
  intro a
  have heq : (MulAction.stabilizer (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) a :
      Set (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)) =
      MulAction.stabilizer (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
        (a : AlgebraicClosure K) := by
    ext g
    exact Subtype.ext_iff
  rw [heq]
  exact stabilizer_isOpen_of_isIntegral (a : AlgebraicClosure K)

theorem residueHom_surjective [PerfectField K] : Function.Surjective (residueHom K V) := by
  intro s
  obtain ⟨g, hg⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite
    (G := AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (maximalIdeal V) (maximalIdeal (ClosureIntegers K)) s
  refine ⟨g.1, ?_⟩
  rw [← hg]
  ext a
  obtain ⟨a, rfl⟩ := residue_surjective a
  rfl

/-- Supporting P16 residual-quotient prerequisite for
`K2-015#lem:k2015-frobenius` at `e73d98b1b5c1e5abcdebf7d058e436d792b87982`;
see the module scope and chosen-identification boundary. -/
theorem absoluteResidueHom_surjective [PerfectField K] :
    Function.Surjective (absoluteResidueHom K V) :=
  (AlgEquiv.autCongr (residueClosureEquiv K V)).surjective.comp
    (residueHom_surjective K V)

end Surjectivity

/-- Surjective reduction to the chosen literal algebraic closure of the residue field.
Supporting P16 residual-quotient prerequisite for
`K2-015#lem:k2015-frobenius` at `e73d98b1b5c1e5abcdebf7d058e436d792b87982`;
see the module scope and chosen-identification boundary. -/
def closureReduction : ClosureIntegers K →+* AlgebraicClosure (ResidueField V) :=
  (residueClosureEquiv K V).toRingEquiv.toRingHom.comp (residue (ClosureIntegers K))

/-- Supporting P16 residual-quotient prerequisite for
`K2-015#lem:k2015-frobenius` at `e73d98b1b5c1e5abcdebf7d058e436d792b87982`;
see the module scope and chosen-identification boundary. -/
theorem closureReduction_surjective : Function.Surjective (closureReduction K V) :=
  (residueClosureEquiv K V).surjective.comp residue_surjective

/-- The residue embedding is induced by the same base valuation-ring inclusion.
Supporting P16 residual-quotient prerequisite for
`K2-015#lem:k2015-frobenius` at `e73d98b1b5c1e5abcdebf7d058e436d792b87982`;
see the module scope and chosen-identification boundary. -/
@[simp] theorem closureReduction_algebraMap (a : V) :
    closureReduction K V (algebraMap V (ClosureIntegers K) a) =
      algebraMap (ResidueField V) (AlgebraicClosure (ResidueField V))
        (IsLocalRing.residue V a) := by
  change residueClosureEquiv K V
    (IsLocalRing.residue (ClosureIntegers K) (algebraMap V (ClosureIntegers K) a)) = _
  rw [← ResidueField.algebraMap_residue]
  exact (residueClosureEquiv K V).commutes _

/-- Krull continuity follows because finitely many residual generators have integral lifts.
Supporting P16 residual-quotient prerequisite for
`K2-015#lem:k2015-frobenius` at `e73d98b1b5c1e5abcdebf7d058e436d792b87982`;
see the module scope and chosen-identification boundary. -/
theorem absoluteResidueHom_continuous : Continuous (absoluteResidueHom K V) := by
  classical
  let f : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →*
      (AlgebraicClosure (ResidueField V) ≃ₐ[ResidueField V]
        AlgebraicClosure (ResidueField V)) := absoluteResidueHom K V
  change Continuous f
  apply continuous_of_continuousAt_one f (continuousAt_def.mpr ?_)
  intro U hU
  rw [map_one, krullTopology_mem_nhds_one_iff] at hU
  obtain ⟨E, hfin, hE⟩ := hU
  have : FiniteDimensional (ResidueField V) E := hfin
  obtain ⟨s, hs⟩ := IntermediateField.essFiniteType_iff.mp
    (inferInstance : Algebra.EssFiniteType (ResidueField V) E)
  choose lift hlift using closureReduction_surjective K V
  have hsmall : ∀ᶠ g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K in 𝓝 1,
      ∀ y ∈ s, g (lift y : AlgebraicClosure K) = (lift y : AlgebraicClosure K) := by
    rw [Filter.eventually_all_finset]
    intro y hy
    exact (stabilizer_isOpen_of_isIntegral (lift y : AlgebraicClosure K)).mem_nhds
      (MulAction.stabilizer (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
        (lift y : AlgebraicClosure K)).one_mem
  filter_upwards [hsmall] with g hg
  apply hE
  change f g ∈ E.fixingSubgroup
  rw [← hs, IntermediateField.mem_fixingSubgroup_iff]
  apply (IntermediateField.forall_mem_adjoin_smul_eq_self_iff (ResidueField V)
    (S := (s : Set (AlgebraicClosure (ResidueField V)))) (f g)).mpr
  intro y hy
  have hga : integerAut K V g (lift y) = lift y := Subtype.ext (hg y hy)
  change f g y = y
  rw [← hlift y]
  exact (absoluteResidueHom_residue K V g (lift y)).trans (congrArg (closureReduction K V) hga)

/-- Actual continuous residue Galois quotient for a complete nonarchimedean field.
Supporting P16 residual-quotient prerequisite for
`K2-015#lem:k2015-frobenius` at `e73d98b1b5c1e5abcdebf7d058e436d792b87982`;
see the module scope and chosen-identification boundary. -/
def absoluteResidue : Field.absoluteGaloisGroup K →ₜ*
    Field.absoluteGaloisGroup (ResidueField V) where
  __ := absoluteResidueHom K V
  continuous_toFun := absoluteResidueHom_continuous K V

end Valuation.ResidualGalois
