/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Smooth.SectionComponentLocusClopen
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.GenericSectionComponentDenseOpen
public import Aglib.Topology.Constructible.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Constructibility of the original smooth section-component locus

Over a Noetherian affine base, the actual quotient at the image of a generic
point reduces the question to the established domain principal-stage theorem.
The same clopen and section are retained. Existing closed-embedding topology
and the Noetherian irreducible-closed criterion finish the original locus.
-/

@[expose] public noncomputable section
open CategoryTheory Limits Opposite Topology
open IsLocalization.PrincipalDiagram
open scoped nonZeroDivisors

namespace AlgebraicGeometry.Scheme
open PrincipalNeighborhoodLimit
universe u

/-- Construct a whole ambient constant open from the original closed map,
open stage, clopen partition, and literal composite preimage. -/
private theorem exists_open_constant_from_clopen_stage
    {X Y T : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace T]
    (a : Y → X) (j : T → Y) (ha : Topology.IsClosedEmbedding a) (hj : IsOpenMap j)
    (C Z : Set X) {x : X} (hx : IsGenericPoint x Z)
    (t : T) (ht : a (j t) = x) (V : Set T) (hV : IsClopen V)
    (hpre : (a ∘ j) ⁻¹' C = V) :
    ∃ U : Set X, IsOpen U ∧ (U ∩ Z).Nonempty ∧
      (U ∩ Z ⊆ C ∨ U ∩ Z ⊆ Cᶜ) := by
  have hZ : Z ⊆ Set.range a :=
    (hx.mem_closed_set_iff ha.isClosed_range).mp ⟨j t, ht⟩
  have hlocal (B : Set T) (hB : IsOpen B) (htB : t ∈ B)
      (D : Set X) (hBD : ∀ w ∈ B, a (j w) ∈ D) :
      ∃ U : Set X, IsOpen U ∧ (U ∩ Z).Nonempty ∧ U ∩ Z ⊆ D := by
    obtain ⟨U, hU, he⟩ := ha.isInducing.image_eq_isOpen_inter_range (hj B hB)
    have hxt : x ∈ a '' (j '' B) := ⟨j t, ⟨t, htB, rfl⟩, ht⟩
    rw [he] at hxt
    refine ⟨U, hU, ⟨x, hxt.1, hx.mem⟩, ?_⟩
    intro z hz
    have hz' : z ∈ a '' (j '' B) := he.symm ▸ ⟨hz.1, hZ hz.2⟩
    obtain ⟨y, ⟨w, hw, rfl⟩, rfl⟩ := hz'
    exact hBD w hw
  by_cases htV : t ∈ V
  · obtain ⟨U, hU, hne, hsub⟩ := hlocal V hV.isOpen htV C (by
      intro w hw
      change w ∈ (a ∘ j) ⁻¹' C
      rw [hpre]
      exact hw)
    exact ⟨U, hU, hne, Or.inl hsub⟩
  · obtain ⟨U, hU, hne, hsub⟩ := hlocal Vᶜ hV.isClosed.isOpen_compl htV Cᶜ (by
      intro w hw hc
      have hw' : w ∈ (a ∘ j) ⁻¹' C := hc
      rw [hpre] at hw'
      exact hw hw')
    exact ⟨U, hU, hne, Or.inr hsub⟩

/-- For an original quasi-compact quasi-separated smooth family of fixed
relative dimension over a Noetherian affine base, the original section-component
locus is constructible. No normality or domain assumption on the base is added. -/
theorem isConstructible_sectionComponentLocus
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (n : ℕ)
    [SmoothOfRelativeDimension n f] [QuasiCompact f] [QuasiSeparated f]
    (σ : Spec (.of R) ⟶ X) (hσ : σ ≫ f = 𝟙 _) :
    IsConstructible (sectionComponentLocus f σ hσ) := by
  classical
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : IsNoetherian X :=
    { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }
  apply TopologicalSpace.NoetherianSpace.isConstructible_of_isIrreducible
  intro Z hZ hZi
  let z := hZi.genericPoint
  have hz : IsGenericPoint z Z := hZi.isGenericPoint_genericPoint hZ
  let p : PrimeSpectrum R := f z
  let D := R ⧸ p.asIdeal
  let b : Spec (.of D) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk p.asIdeal))
  let Y := pullback f b
  let a : Y ⟶ X := pullback.fst f b
  let q : Y ⟶ Spec (.of D) := pullback.snd f b
  let : IsClosedImmersion b :=
    IsClosedImmersion.spec_of_quotient_mk (R := .of R) p.asIdeal
  let : IsClosedImmersion a := MorphismProperty.of_isPullback
    (IsPullback.of_hasPullback f b).flip (inferInstance : IsClosedImmersion b)
  let : SmoothOfRelativeDimension n q :=
    @MorphismProperty.IsStableUnderBaseChange.of_isPullback
      Scheme.{u} _ (@SmoothOfRelativeDimension n)
      (smoothOfRelativeDimension_isStableUnderBaseChange n)
      (Spec (.of D)) X Y (Spec (.of R)) b f a q
      (IsPullback.of_hasPullback f b) (inferInstance : SmoothOfRelativeDimension n f)
  let : Smooth q := SmoothOfRelativeDimension.smooth n q
  let σD : Spec (.of D) ⟶ Y := pullback.lift (b ≫ σ) (𝟙 _) (by
    rw [Category.assoc, hσ, Category.comp_id, Category.id_comp])
  have hσD : σD ≫ q = 𝟙 _ := pullback.lift_snd _ _ _
  have hσDa : σD ≫ a = b ≫ σ := pullback.lift_fst _ _ _
  have hpreD := sectionComponentLocus_preimage_of_isPullback f a q b
    (.of_hasPullback f b) σ hσ σD hσD hσDa
  let K := FractionRing D
  let Ω := AlgebraicClosure K
  obtain ⟨s, V, hr, hV, _, hGI, τ, hτ, _⟩ :=
    exists_principal_geometricallyIntegral_section_component K Ω q n σD hσD
  let c := Spec.algebraMap D (stage D⁰ s)
  let j : (PrincipalNeighborhoodLimit.baseChangeDiagram D⁰ q).obj (op s) ⟶ Y := pullback.snd c q
  let q' : (PrincipalNeighborhoodLimit.baseChangeDiagram D⁰ q).obj (op s) ⟶
      Spec (.of (stage D⁰ s)) := pullback.fst c q
  let σ' := principalSection D⁰ q σD hσD (op s)
  have hσ' : σ' ≫ q' = 𝟙 _ := pullback.lift_fst _ _ _
  have hσ'j : σ' ≫ j = c ≫ σD := pullback.lift_snd _ _ _
  let : GeometricallyIntegral (V.ι ≫ q') := hGI
  let : GeometricallyConnected (V.ι ≫ q') := by
    constructor
    intro L _ v Z fst snd H
    let : IsIntegral Z := GeometricallyIntegral.geometrically_isIntegral v fst snd H
    infer_instance
  have hVloc : sectionComponentLocus q' σ' hσ' = (V : Set _) :=
    sectionComponentLocus_eq_clopen q' σ' hσ' V hV τ hτ
  have hpreStage := sectionComponentLocus_preimage_of_isPullback q j q' c
    (IsPullback.of_hasPullback c q).flip σD hσD σ' hσ' hσ'j
  have hpre : (a ∘ j) ⁻¹' sectionComponentLocus f σ hσ = (V : Set _) := by
    change j ⁻¹' (a ⁻¹' sectionComponentLocus f σ hσ) = _
    rw [hpreD, hpreStage, hVloc]
  let η : Spec (.of D) := ⟨⊥, inferInstance⟩
  have hη : b η = p := by
    apply PrimeSpectrum.ext
    change Ideal.comap (Ideal.Quotient.mk p.asIdeal) ⊥ = p.asIdeal
    exact Ideal.mk_ker
  obtain ⟨y, hya, hyq⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := f) (g := b) z η hη.symm
  have hηrange : η ∈ Set.range c := by
    change η ∈ Set.range (PrimeSpectrum.comap (algebraMap D (stage D⁰ s)))
    rw [PrimeSpectrum.localization_away_comap_range (stage D⁰ s) (denominator D⁰ s)]
    change denominator D⁰ s ∉ (⊥ : Ideal D)
    simpa only [Ideal.mem_bot] using hr
  obtain ⟨v, hv⟩ := hηrange
  obtain ⟨w, _, hwj⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := c) (g := q) v y (hv.trans hyq.symm)
  have hw : a (j w) = z := (congrArg a hwj).trans hya
  let : IsOpenImmersion c := stage_isOpenImmersion D⁰ s
  let : IsOpenImmersion j := MorphismProperty.of_isPullback
    (IsPullback.of_hasPullback c q) (inferInstance : IsOpenImmersion c)
  exact exists_open_constant_from_clopen_stage a j a.isClosedEmbedding j.isOpenMap
    (sectionComponentLocus f σ hσ) Z hz w hw (V : Set _) ⟨hV, V.isOpen⟩ hpre

end AlgebraicGeometry.Scheme
