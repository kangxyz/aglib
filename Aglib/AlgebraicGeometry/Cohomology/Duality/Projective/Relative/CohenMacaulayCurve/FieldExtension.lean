/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Flat
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Structure
public import Mathlib.RingTheory.Algebraic.Integral
public import Aglib.AlgebraicGeometry.Stalk.Dimension
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Regular.IsSMulRegular
public import Aglib.RingTheory.KrullDimension.RegularQuotient
public import Aglib.RingTheory.KrullDimension.IntegralExtension
public import Aglib.AlgebraicGeometry.Dimension.OpenCover
public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.RingTheory.Regular.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Closed parameters and geometric extension of coefficient curves

The dimension bound required for geometric extension is derived from the
original closed-stalk parameter condition. It is not an extra curve hypothesis.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- A maximal-primary principal ideal bounds the dimension of a Noetherian
local ring, without reducedness or regularity of the ambient ring. -/
theorem ringKrullDim_le_one_of_primary_parameter
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (b : R) (hb : b ∈ IsLocalRing.maximalIdeal R)
    (hrad : (Ideal.span {b}).radical = IsLocalRing.maximalIdeal R) :
    ringKrullDim R ≤ 1 := by
  have hm : (Ideal.span {b}).minimalPrimes =
      (IsLocalRing.maximalIdeal R).minimalPrimes := by
    calc
      (Ideal.span {b}).minimalPrimes = (Ideal.span {b}).radical.minimalPrimes :=
        Ideal.radical_minimalPrimes.symm
      _ = _ := congrArg Ideal.minimalPrimes hrad
  have hh : (Ideal.span {b}).height = (IsLocalRing.maximalIdeal R).height := by
    rw [Ideal.height_eq_inf_minimalPrimes, hm, ← Ideal.height_eq_inf_minimalPrimes]
  have h := Ideal.height_span_singleton_le_one
    (show ¬ IsUnit b by
      simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hb)
  rw [hh] at h
  exact IsLocalRing.maximalIdeal_height_eq_ringKrullDim.symm.le.trans
    (WithBot.coe_le_coe.mpr h)

/-- On a compact scheme, the original closed-stalk parameter condition
already gives the full dimension bound. Every point has a closed specialization;
there is no Jacobson, reducedness, or algebraically closed field premise. -/
theorem dimension_le_one_of_closed_parameters (C : Scheme.{u})
    [CompactSpace C] [IsLocallyNoetherian C]
    (hCM : ∀ x : C, IsClosed ({x} : Set C) →
      ∃ b ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk x),
        IsSMulRegular (C.presheaf.stalk x) b ∧
          (Ideal.span {b}).radical = IsLocalRing.maximalIdeal (C.presheaf.stalk x)) :
    topologicalKrullDim C ≤ 1 := by
  rw [topologicalKrullDim_eq_iSup_stalk]
  refine iSup_le fun x => ?_
  obtain ⟨y, hy, hyclosed⟩ := isClosed_closure.exists_closed_singleton
    (show (closure ({x} : Set C)).Nonempty from ⟨x, subset_closure (by simp)⟩)
  obtain ⟨b, hb, _, hrad⟩ := hCM y hyclosed
  have hd := ringKrullDim_le_one_of_primary_parameter (C.presheaf.stalk y) b hb hrad
  rw [ringKrullDim_stalk_eq_coheight] at hd ⊢
  have hxy : y ≤ x := (specializes_iff_mem_closure).mpr hy
  exact (WithBot.coe_le_coe.mpr (Order.coheight_anti hxy)).trans hd

/-- A regular nonunit on a Noetherian local ring of dimension at most one
generates a maximal-primary ideal, including in the nonreduced case. -/
theorem radical_span_eq_maximalIdeal_of_regular_of_dimension_le_one
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hd : ringKrullDim R ≤ 1) (b : R)
    (hb : b ∈ IsLocalRing.maximalIdeal R) (hreg : IsSMulRegular R b) :
    (Ideal.span {b}).radical = IsLocalRing.maximalIdeal R := by
  let : IsArtinianRing (R ⧸ Ideal.span {b}) :=
    RingHom.quotient_isArtinianRing_of_regular_kernel_element
      (Ideal.Quotient.mk (Ideal.span {b})) Ideal.Quotient.mk_surjective hd b hreg
      (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp)))
  obtain ⟨n, hn⟩ :=
    IsLocalRing.exists_maximalIdeal_pow_le_of_isArtinianRing_quotient (Ideal.span {b})
  apply le_antisymm
  · apply (Ideal.IsPrime.radical_le_iff
      (inferInstance : (IsLocalRing.maximalIdeal R).IsPrime)).mpr
    exact Ideal.span_le.mpr (by simpa using hb)
  · intro r hr
    exact Ideal.mem_radical_iff.mpr ⟨n, hn (Ideal.pow_mem_pow hr n)⟩


/-- The original flat stalk map transports a regular closed parameter.
The dimension input is discharged below for the integral projection. -/
theorem closed_parameters_of_flat_integral_of_dimension
    {Y X : Scheme.{u}} (f : Y ⟶ X) [Flat f] [IsIntegralHom f]
    [IsLocallyNoetherian Y] (hd : topologicalKrullDim Y ≤ 1)
    (hCM : ∀ x : X, IsClosed ({x} : Set X) →
      ∃ b ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x),
        IsSMulRegular (X.presheaf.stalk x) b ∧
          (Ideal.span {b}).radical = IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :
    ∀ y : Y, IsClosed ({y} : Set Y) →
      ∃ b ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y),
        IsSMulRegular (Y.presheaf.stalk y) b ∧
          (Ideal.span {b}).radical = IsLocalRing.maximalIdeal (Y.presheaf.stalk y) := by
  intro y hy
  have hx : IsClosed ({f y} : Set X) := by
    simpa only [Set.image_singleton] using f.isClosedMap _ hy
  obtain ⟨b, hb, hreg, _⟩ := hCM (f y) hx
  let := (f.stalkMap y).hom.toAlgebra
  let : Module.Flat (X.presheaf.stalk (f y)) (Y.presheaf.stalk y) :=
    RingHom.flat_algebraMap_iff.mp (Flat.stalkMap f y)
  have hb' : (f.stalkMap y).hom b ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y) := by
    simpa only [IsLocalRing.mem_maximalIdeal, map_mem_nonunits_iff] using hb
  have hr' : IsSMulRegular (Y.presheaf.stalk y) ((f.stalkMap y).hom b) :=
    hreg.of_flat
  have hd' : ringKrullDim (Y.presheaf.stalk y) ≤ 1 := by
    rw [topologicalKrullDim_eq_iSup_stalk] at hd
    exact (le_iSup (fun z : Y => ringKrullDim (Y.presheaf.stalk z)) y).trans hd
  exact ⟨_, hb', hr', radical_span_eq_maximalIdeal_of_regular_of_dimension_le_one
    _ hd' _ hb' hr'⟩


/-- Integral morphisms do not increase dimension. The proof uses only
actual affine section maps; no localized stalk map is asserted integral. -/
theorem dimension_le_of_integralHom {Y X : Scheme.{u}} (f : Y ⟶ X)
    [IsIntegralHom f] : topologicalKrullDim Y ≤ topologicalKrullDim X := by
  let U := X.affineCover
  apply topologicalKrullDim_le_of_openCover (U.pullback₁ f)
  intro i
  let g := U.pullbackHom f i
  have : IsAffine (U.X i) := Scheme.isAffine_affineCover X i
  have : IsOpenImmersion (U.f i) := X.affineCover.map_prop i
  have : IsIntegralHom g := by
    change IsIntegralHom (CategoryTheory.Limits.pullback.snd f (U.f i))
    infer_instance
  have : IsAffine ((U.pullback₁ f).X i) := isAffine_of_isAffineHom g
  let := g.appTop.hom.toAlgebra
  have : Algebra.IsIntegral Γ(U.X i, ⊤) Γ((U.pullback₁ f).X i, ⊤) :=
    ⟨g.isIntegral_app ⊤ (isAffineOpen_top (U.X i))⟩
  have hr : ringKrullDim Γ((U.pullback₁ f).X i, ⊤) ≤ ringKrullDim Γ(U.X i, ⊤) := by
    apply Order.krullDim_le_of_strictMono
      (PrimeSpectrum.comap (algebraMap Γ(U.X i, ⊤) Γ((U.pullback₁ f).X i, ⊤)))
    intro p q hpq
    exact Ideal.IsIntegral.under_lt_under hpq
  have hs : topologicalKrullDim ((U.pullback₁ f).X i) =
      ringKrullDim Γ((U.pullback₁ f).X i, ⊤) :=
    (IsHomeomorph.topologicalKrullDim_eq _
      ((U.pullback₁ f).X i).isoSpec.hom.homeomorph.isHomeomorph).trans
      (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _)
  have ht : topologicalKrullDim (U.X i) = ringKrullDim Γ(U.X i, ⊤) :=
    (IsHomeomorph.topologicalKrullDim_eq _
      (U.X i).isoSpec.hom.homeomorph.isHomeomorph).trans
      (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _)
  rw [hs]
  exact hr.trans (ht.symm.le.trans
    (U.f i).isOpenEmbedding.isEmbedding.isInducing.topologicalKrullDim_le)

/-- The original closed-parameter condition is preserved by an integral flat
map between locally Noetherian schemes with compact source base. In
particular this applies to the actual algebraic field-extension projection;
no separability, perfection, or new dimension premise is required. -/
theorem closed_parameters_of_flat_integral
    {Y X : Scheme.{u}} (f : Y ⟶ X) [Flat f] [IsIntegralHom f]
    [CompactSpace X] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (hCM : ∀ x : X, IsClosed ({x} : Set X) →
      ∃ b ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x),
        IsSMulRegular (X.presheaf.stalk x) b ∧
          (Ideal.span {b}).radical = IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :
    ∀ y : Y, IsClosed ({y} : Set Y) →
      ∃ b ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y),
        IsSMulRegular (Y.presheaf.stalk y) b ∧
          (Ideal.span {b}).radical = IsLocalRing.maximalIdeal (Y.presheaf.stalk y) :=
  closed_parameters_of_flat_integral_of_dimension f
    ((dimension_le_of_integralHom f).trans (dimension_le_one_of_closed_parameters X hCM)) hCM

/-- Algebraic field extension of the original embedded curve preserves its
original closed-stalk parameter condition. The curve is the literal
pullback along the projective coefficient map, with no separability or
perfection assumption and no extra dimension premise. -/
theorem closed_parameters_projective_algebraic_field_extension
    (k K : Type u) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (ι : Type u) [Finite ι] {C : Scheme.{u}}
    (j : C ⟶ ProjectiveSpace k ι) [IsClosedImmersion j]
    (hCM : ∀ x : C, IsClosed ({x} : Set C) →
      ∃ b ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk x),
        IsSMulRegular (C.presheaf.stalk x) b ∧
          (Ideal.span {b}).radical = IsLocalRing.maximalIdeal (C.presheaf.stalk x)) :
    ∀ y : ↥(Limits.pullback j (ProjectiveSpace.map (algebraMap k K) ι) : Scheme.{u}),
      IsClosed ({y} : Set ↥(Limits.pullback j
        (ProjectiveSpace.map (algebraMap k K) ι) : Scheme.{u})) →
      ∃ b ∈ IsLocalRing.maximalIdeal
          ((Limits.pullback j (ProjectiveSpace.map (algebraMap k K) ι)).presheaf.stalk y),
        IsSMulRegular
          ((Limits.pullback j (ProjectiveSpace.map (algebraMap k K) ι)).presheaf.stalk y) b ∧
          (Ideal.span {b}).radical = IsLocalRing.maximalIdeal
            ((Limits.pullback j (ProjectiveSpace.map (algebraMap k K) ι)).presheaf.stalk y) := by
  let t := ProjectiveSpace.map (algebraMap k K) ι
  let f := Limits.pullback.fst j t
  let jK := Limits.pullback.snd j t
  have hSpec : IsIntegralHom (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
    IsIntegralHom.SpecMap_iff.mpr (algebraMap_isIntegral_iff.mpr inferInstance)
  let : IsIntegralHom t :=
    MorphismProperty.of_isPullback
      (ProjectiveSpace.isPullback_map (algebraMap k K) ι).flip hSpec
  let : Flat t := ProjectiveSpace.flat_map_algebraMap k K ι
  let : IsIntegralHom f := inferInstance
  let : Flat f := inferInstance
  let : IsClosedImmersion jK := inferInstance
  let : IsLocallyNoetherian C :=
    LocallyOfFiniteType.isLocallyNoetherian (j ≫ ProjectiveSpace.toSpec k ι)
  let : IsLocallyNoetherian (Limits.pullback j t) :=
    LocallyOfFiniteType.isLocallyNoetherian (jK ≫ ProjectiveSpace.toSpec K ι)
  let : CompactSpace C :=
    QuasiCompact.compactSpace_of_compactSpace (j ≫ ProjectiveSpace.toSpec k ι)
  exact closed_parameters_of_flat_integral f hCM

end AlgebraicGeometry.Scheme
