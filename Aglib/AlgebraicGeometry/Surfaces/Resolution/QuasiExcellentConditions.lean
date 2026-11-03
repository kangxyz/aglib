/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Dimension.Finite
public import Aglib.AlgebraicGeometry.Normalization.QuasiExcellent
public import Aglib.AlgebraicGeometry.Surfaces.Resolution.RationalDoublePoint.ClosedSingularPoints
public import Aglib.AlgebraicGeometry.Dimension.Finite.Stalk

/-! # Quasi-excellent normalization conditions for surface resolution

Genuine affine quasi-excellence supplies finite original generic normalization,
finite singular support, and normal domain completions at its singular points.
These are conditions for the resolution criterion, not a resolution-existence
proof. No global affine base or new normalization model is chosen.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u

/-- The original normalization of an integral Noetherian surface with genuine
affine QE rings has finitely many singular points. -/
theorem genericNormalization_finite_singularSet_of_isQuasiExcellentRing
    (W : Scheme.{u}) [IsIntegral W] [IsNoetherian W]
    (hdimW : topologicalKrullDim W ≤ 2)
    (hQE : ∀ U : W.affineOpens, Nonempty U.1 →
      IsQuasiExcellentRing.{u, 0} Γ(W, U.1)) :
    {y : (W.fromSpecStalk (genericPoint W)).normalization |
      ¬ IsRegularLocalRing
        ((W.fromSpecStalk (genericPoint W)).normalization.presheaf.stalk y)}.Finite := by
  classical
  let γ := W.fromSpecStalk (genericPoint W)
  let N := γ.normalization
  let ν : N ⟶ W := γ.fromNormalization
  let : IsFinite ν := genericNormalization_isFinite_of_isQuasiExcellentRing W hdimW hQE
  have hdimN : topologicalKrullDim N ≤ 2 :=
    ν.topologicalKrullDim_le_of_finite.trans hdimW
  let (y : N) : IsIntegrallyClosed (N.presheaf.stalk y) :=
    (genericNormalization_normalStalks W y).2
  let 𝒰 := W.affineCover.finiteSubcover
  have haff (i : 𝒰.I₀) : IsAffine (𝒰.X i) := by
    change IsAffine (W.affineCover.X (W.affineCover.idx i.val))
    exact Scheme.isAffine_affineCover W _
  let U (i : 𝒰.I₀) : W.Opens := (𝒰.f i).opensRange
  have hU (i : 𝒰.I₀) : IsAffineOpen (U i) := by
    let : IsAffine (𝒰.X i) := haff i
    exact isAffineOpen_opensRange (𝒰.f i)
  let V (i : 𝒰.I₀) : N.Opens := ν ⁻¹ᵁ U i
  have hV (i : 𝒰.I₀) : IsAffineOpen (V i) := (hU i).preimage ν
  have hf (i : 𝒰.I₀) :
      {y : N | y ∈ V i ∧ ¬ IsRegularLocalRing (N.presheaf.stalk y)}.Finite := by
    by_cases hne : Nonempty (V i)
    · let : Nonempty (V i) := hne
      obtain ⟨y⟩ := hne
      have hneU : Nonempty (U i) := ⟨⟨ν y.1, y.2⟩⟩
      let A := Γ(W, U i)
      let B := Γ(N, V i)
      let : Algebra A B := (ν.app (U i)).hom.toAlgebra
      let : Module.Finite A B := ν.finite_app (U i) (hU i)
      let : IsIntegrallyClosed B := isIntegrallyClosed_sections_of_isAffineOpen N (V i) (hV i)
      have hd : ringKrullDim B ≤ 2 := by
        have h := (hV i).fromSpec.isOpenEmbedding.isEmbedding.isInducing.topologicalKrullDim_le
        change topologicalKrullDim (PrimeSpectrum B) ≤ topologicalKrullDim N at h
        rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim] at h
        exact h.trans hdimN
      have hfin := PrimeSpectrum.finite_compl_regularLocus_of_finiteType_of_isJ2Ring
        A B (hQE ⟨U i, hU i⟩ hneU).2 hd
      exact finite_singularSet_inter_affine_of_finite_compl_regularLocus (V i) (hV i) hfin
    · apply Set.finite_empty.subset
      rintro y ⟨hy, _⟩
      exact (hne ⟨⟨y, hy⟩⟩).elim
  apply (Set.finite_iUnion hf).subset
  intro y hy
  obtain ⟨i, z, hz⟩ := 𝒰.exists_eq (ν y)
  apply Set.mem_iUnion.mpr
  refine ⟨i, ?_, hy⟩
  change ν y ∈ Set.range (𝒰.f i)
  exact ⟨z, hz⟩

/-- At a singular point of the original generic normalization, genuine affine
QE hypotheses give a normal domain completion of the original stalk. -/
theorem genericNormalization_completion_normalDomain_of_singular_of_isQuasiExcellentRing
    (W : Scheme.{u}) [IsIntegral W] [IsNoetherian W]
    (hdimW : topologicalKrullDim W ≤ 2)
    (hQE : ∀ U : W.affineOpens, Nonempty U.1 →
      IsQuasiExcellentRing.{u, 0} Γ(W, U.1))
    (y : (W.fromSpecStalk (genericPoint W)).normalization)
    (hy : ¬ IsRegularLocalRing
      ((W.fromSpecStalk (genericPoint W)).normalization.presheaf.stalk y)) :
    IsDomain (AdicCompletion
      (IsLocalRing.maximalIdeal
        ((W.fromSpecStalk (genericPoint W)).normalization.presheaf.stalk y))
      ((W.fromSpecStalk (genericPoint W)).normalization.presheaf.stalk y)) ∧
    IsIntegrallyClosed (AdicCompletion
      (IsLocalRing.maximalIdeal
        ((W.fromSpecStalk (genericPoint W)).normalization.presheaf.stalk y))
      ((W.fromSpecStalk (genericPoint W)).normalization.presheaf.stalk y)) := by
  let γ := W.fromSpecStalk (genericPoint W)
  let N := γ.normalization
  let ν : N ⟶ W := γ.fromNormalization
  let : IsFinite ν := genericNormalization_isFinite_of_isQuasiExcellentRing W hdimW hQE
  let : IsLocallyNoetherian N := LocallyOfFiniteType.isLocallyNoetherian ν
  have hdimN : topologicalKrullDim N ≤ 2 :=
    ν.topologicalKrullDim_le_of_finite.trans hdimW
  have hd := stalk_dimension_eq_two_of_singular_of_normal_dimension_le_two
    N (genericNormalization_normalStalks W) hdimN y hy
  exact genericNormalization_completion_normalDomain_of_dim_eq_two W hdimW hQE y hd

end AlgebraicGeometry.Scheme
