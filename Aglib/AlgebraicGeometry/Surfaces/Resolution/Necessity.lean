/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.ProperBirational
public import Aglib.AlgebraicGeometry.Spec.CompletionLocalRing.Normal
public import Aglib.AlgebraicGeometry.Morphisms.Proper.BirationalSurface
public import Aglib.AlgebraicGeometry.Morphisms.Proper.BirationalFunctions
public import Aglib.AlgebraicGeometry.Properties.Regular.OpenCover
public import Aglib.AlgebraicGeometry.Stalk.FlatBaseChange
public import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Necessity of the normal-completion conditions for resolution

A supplied proper birational regular integral model of an integral
Noetherian surface forces finiteness of its literal generic normalization,
finiteness of that normalization's singular set, and normal domain
completions at every normalization point.

The local structural section bijection is derived from the original
normal-birational structure map and the actual flat section pushout.
It is not a hypothesis of the final implication. No resolution existence,
Nagata, excellence, J-2, or absolute separatedness assumption is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme

universe u

private theorem normalStalks_of_regularStalks {X : Scheme.{u}}
    (hX : RegularStalks X) : NormalStalks X := by
  intro x
  let := hX x
  exact ⟨IsRegularLocalRing.isDomain_of_regularLocal _,
    IsRegularLocalRing.isIntegrallyClosed_of_regularLocal _⟩

private theorem appLE_top {X Y : Scheme.{u}} (f : X ⟶ Y) (h : ⊤ ≤ f ⁻¹ᵁ ⊤) :
    f.appLE ⊤ ⊤ h = f.appTop := by
  simpa only [Hom.preimage_top] using (f.appLE_eq_app (U := ⊤))

private theorem stalkDimension_le_of_finite
    {N Y : Scheme.{u}} (ν : N ⟶ Y) [IsFinite ν]
    (hdim : topologicalKrullDim Y ≤ 2) : SurfaceDimensionAtMostTwo N := by
  intro n
  obtain ⟨U, hU, hnU, _⟩ := exists_isAffineOpen_mem_and_subset
    (U := ⊤) (x := ν n) (by trivial)
  let V := ν ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage ν
  have hnV : n ∈ V := hnU
  let A := Γ(Y, U)
  let C := Γ(N, V)
  let : Algebra A C := (ν.app U).hom.toAlgebra
  let : Module.Finite A C := ν.finite_app U hU
  have hCA : ringKrullDim C ≤ ringKrullDim A := by
    apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap A C))
    intro P Q hPQ
    exact Ideal.IsIntegral.under_lt_under (R := A) hPQ
  have hAY : ringKrullDim A ≤ topologicalKrullDim Y := by
    have h := hU.fromSpec.isOpenEmbedding.isEmbedding.isInducing.topologicalKrullDim_le
    change topologicalKrullDim (PrimeSpectrum A) ≤ topologicalKrullDim Y at h
    rwa [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim] at h
  let p := (hV.primeIdealOf ⟨n, hnV⟩).asIdeal
  let : p.IsPrime := (hV.primeIdealOf ⟨n, hnV⟩).isPrime
  let : Algebra C (N.presheaf.stalk n) := N.presheaf.algebra_section_stalk ⟨n, hnV⟩
  let : IsLocalization.AtPrime (N.presheaf.stalk n) p := hV.isLocalization_stalk ⟨n, hnV⟩
  have hnC : ringKrullDim (N.presheaf.stalk n) ≤ ringKrullDim C := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p (N.presheaf.stalk n)]
    exact p.height_le_ringKrullDim_of_isPrime
  exact hnC.trans (hCA.trans (hAY.trans hdim))

/-- Localize the original proper structural map at a target point. Its
literal section homomorphism is bijective by the original flat pushout. -/
private theorem bijective_localStructuralSections_of_isIso_c
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (hc : IsIso f.c) (y : Y) :
    Function.Bijective
      (LocalRing.properStructuralSectionsMap (pullback.snd f (Y.fromSpecStalk y))) := by
  let : IsIso f.c := hc
  let l := Y.fromSpecStalk y
  let P := pullback f l
  let a : P ⟶ X := pullback.fst f l
  let p : P ⟶ Spec (Y.presheaf.stalk y) := pullback.snd f l
  let : Flat l := fromSpecStalk_flat Y y
  obtain ⟨U, hU, hyU, _⟩ := exists_isAffineOpen_mem_and_subset
    (U := ⊤) (x := y) (by trivial)
  have hlU : l ⁻¹ᵁ U = ⊤ := preimage_eq_top_of_closedPoint_mem l (by
    rw [fromSpecStalk_closedPoint]
    exact hyU)
  have hUST : (⊤ : (Spec (Y.presheaf.stalk y)).Opens) ≤ l ⁻¹ᵁ U := hlU.ge
  have H : IsPullback a p f l := IsPullback.of_hasPullback f l
  have hP : (⊤ : P.Opens) = a ⁻¹ᵁ (f ⁻¹ᵁ U) ⊓ p ⁻¹ᵁ ⊤ := by
    rw [← Hom.comp_preimage, pullback.condition, Hom.comp_preimage, hlU]
    simp
  have hiso := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H hUST le_rfl hP
    hU (isAffineOpen_top _) (f.isCompact_preimage hU.isCompact)
    (f.isQuasiSeparated_preimage hU.isQuasiSeparated)
  have hPO := (isIso_pushoutSection_iff H hUST le_rfl hP).mp hiso
  rw [Hom.appLE_eq_app] at hPO
  let : IsIso (f.app U) := inferInstanceAs (IsIso (f.c.app (op U)))
  have hp : IsIso (p.appLE ⊤ ⊤ (by rw [Hom.preimage_top])) :=
    hPO.isIso_inr_of_isIso
  have : IsIso p.appTop := (appLE_top p _) ▸ hp
  exact (ConcreteCategory.bijective_of_isIso p.appTop).comp
    (ConcreteCategory.bijective_of_isIso (ΓSpecIso (Y.presheaf.stalk y)).inv)

private theorem regularStalks_pullback_fromSpecStalk
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hX : RegularStalks X) (y : Y) :
    RegularStalks (pullback f (Y.fromSpecStalk y)) := by
  let l := Y.fromSpecStalk y
  let a := pullback.fst f l
  let : Flat l := fromSpecStalk_flat Y y
  let : Flat a := inferInstance
  let : IsPreimmersion a := inferInstance
  intro z
  let := hX (a z)
  let : IsIso (a.stalkMap z) := Hom.isIso_stalkMap_of_flat_of_surjectiveOnStalks a z
  exact IsRegularLocalRing.of_ringEquiv (asIso (a.stalkMap z)).commRingCatIsoToRingEquiv

/-- A proper birational regular model of a normal locally Noetherian
integral target forces normal domain completion at every actual target point. -/
theorem Hom.completion_normal_at_of_proper_birational_regular
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] [IsDominant f] (hX : RegularStalks X)
    (hY : NormalStalks Y) (hff : IsIso (CommRingCat.ofHom (functionFieldMap f)))
    (y : Y) :
    IsDomain (AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
      (Y.presheaf.stalk y)) ∧
    IsIntegrallyClosed (AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
      (Y.presheaf.stalk y)) := by
  let p := pullback.snd f (Y.fromSpecStalk y)
  have hP : RegularStalks (pullback f (Y.fromSpecStalk y)) :=
    regularStalks_pullback_fromSpecStalk f hX y
  have hβ : Function.Bijective (LocalRing.properStructuralSectionsMap p) :=
    bijective_localStructuralSections_of_isIso_c f (isIso_c_of_isProper_birational f hY hff) y
  exact LocalRing.completion_normal_of_proper_regular_structuralSections
    (Y.presheaf.stalk y) p hP hβ

private theorem finite_singularSet_of_proper_birational_regular
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsNoetherian Y]
    (f : X ⟶ Y) [IsProper f] [IsDominant f] (hX : RegularStalks X)
    (hY : NormalStalks Y) (hff : IsIso (CommRingCat.ofHom (functionFieldMap f)))
    (hdim : topologicalKrullDim Y ≤ 2) :
    {y : Y | ¬ IsRegularLocalRing (Y.presheaf.stalk y)}.Finite := by
  let U := f.targetIsomorphismLocus
  let : IsIso (f ∣_ U) := f.isIso_restrict_targetIsomorphismLocus
  have hU : RegularStalks U.toScheme :=
    hX.of_isOpenImmersion (inv (f ∣_ U) ≫ (f ⁻¹ᵁ U).ι)
  apply (f.finite_compl_targetIsomorphismLocus_of_isProper_birational hff hY hdim).subset
  intro y hy hyU
  exact hy (RegularStalks.at_image U.ι hU ⟨y, hyU⟩)

/-- Necessity in the absolute resolution criterion. A supplied proper
birational regular integral model gives the three conditions for the literal
generic normalization, with normal domain completions at every point. -/
theorem Hom.normalization_conditions_of_proper_birational_regular
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsNoetherian Y]
    (f : X ⟶ Y) [IsProper f] [IsDominant f] (hX : RegularStalks X)
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f)))
    (hdim : topologicalKrullDim Y ≤ 2) :
    let γ := Y.fromSpecStalk (genericPoint Y)
    IsFinite γ.fromNormalization ∧
      {y : γ.normalization | ¬ IsRegularLocalRing (γ.normalization.presheaf.stalk y)}.Finite ∧
      ∀ y : γ.normalization,
        IsDomain (AdicCompletion (IsLocalRing.maximalIdeal (γ.normalization.presheaf.stalk y))
          (γ.normalization.presheaf.stalk y)) ∧
        IsIntegrallyClosed
          (AdicCompletion (IsLocalRing.maximalIdeal (γ.normalization.presheaf.stalk y))
            (γ.normalization.presheaf.stalk y)) := by
  let γ := Y.fromSpecStalk (genericPoint Y)
  let N := γ.normalization
  let ν : N ⟶ Y := γ.fromNormalization
  have hXnormal : NormalStalks X := normalStalks_of_regularStalks hX
  let : IsFinite ν := genericNormalization_isFinite_of_proper_birational f hXnormal hff
  let : IsLocallyNoetherian N := LocallyOfFiniteType.isLocallyNoetherian ν
  let : CompactSpace N := QuasiCompact.compactSpace_of_compactSpace ν
  let : IsNoetherian N := ⟨⟩
  let g : X ⟶ N := genericNormalizationLift f hXnormal
  let : IsProper g := genericNormalizationLift_isProper f hXnormal
  let : IsDominant g := genericNormalizationLift_isDominant f hXnormal
  have hgff : IsIso (CommRingCat.ofHom (functionFieldMap g)) :=
    genericNormalizationLift_fieldMap_isIso f hXnormal hff
  have hNnormal : NormalStalks N := genericNormalization_normalStalks Y
  have hNdim : topologicalKrullDim N ≤ 2 := by
    rw [topologicalKrullDim_eq_iSup_stalk]
    exact iSup_le (stalkDimension_le_of_finite ν hdim)
  refine ⟨inferInstance, finite_singularSet_of_proper_birational_regular
    g hX hNnormal hgff hNdim, ?_⟩
  intro y
  exact g.completion_normal_at_of_proper_birational_regular hX hNnormal hgff y

end AlgebraicGeometry.Scheme
