/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.BoundarySeparation.Global
public import Aglib.AlgebraicGeometry.Blowup.FlatBaseChange
public import Aglib.AlgebraicGeometry.Blowup.AffineCenter.Restriction
public import Aglib.AlgebraicGeometry.Blowup.Construction
public import Aglib.AlgebraicGeometry.Blowup.Properness
public import Aglib.AlgebraicGeometry.Blowup.Admissible

/-!
# Boundary separation on arbitrary schemes

Conrad's separation argument is local on both the original base and the ambient
scheme. The localization below uses open flat base change of the original blowup.
The closed subscheme on the ambient scheme is fixed before base change; no
commutation of schematic image with a nonflat base change is asserted.
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry
universe u

namespace AlgebraicGeometry.Scheme.Blowup

/-- Global separation for a fixed original ambient ideal. This stronger subset
form allows specialization to the actual original schematic image without any
schematic-image base-change hypothesis. -/
theorem boundary_separation {X Z : Scheme.{u}} (p : Z ⟶ X)
    (I₁ I₂ : X.IdealSheafData) (B : BlowupDatum (I₁ ⊔ I₂))
    (J : Z.IdealSheafData)
    (hcontain : I₂.comap p ≤ (I₁ ^ 2).comap p ⊔ J)
    (S : Set Z) (hSJ : S ⊆ J.support)
    (hSavoid : ∀ z ∈ S, p z ∉ I₂.support)
    (T : Set X) (hT : T ⊆ I₁.support)
    (hTavoid : Disjoint T (I₁ ⊔ I₂).support) :
    Disjoint (closure (pullback.fst p B.map ⁻¹' S))
      (pullback.snd p B.map ⁻¹' closure (B.map ⁻¹' T)) := by
  apply Set.disjoint_left.mpr
  intro z hz hzT
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (x := p (pullback.fst p B.map z)) (U := ⊤) (by trivial)
  obtain ⟨W, hW, hzW, hWU⟩ := exists_isAffineOpen_mem_and_subset
    (x := pullback.fst p B.map z) (U := p ⁻¹ᵁ U) hxU
  let A : CommRingCat := Γ(X, U)
  let R : CommRingCat := Γ(Z, W)
  let : Algebra A R := (p.appLE U W hWU).hom.toAlgebra
  let u : Spec A ⟶ X := hU.fromSpec
  let v : Spec R ⟶ Z := hW.fromSpec
  let p₀ : Spec R ⟶ Spec A := Spec.map (CommRingCat.ofHom (algebraMap A R))
  have hp : p₀ ≫ u = v ≫ p := hU.SpecMap_appLE_fromSpec p hW hWU
  let K₁ : Ideal A := I₁.ideal ⟨U, hU⟩
  let K₂ : Ideal A := I₂.ideal ⟨U, hU⟩
  let L : Ideal R := J.ideal ⟨W, hW⟩
  have hc : (I₁ ⊔ I₂).comap u = affineCenter A (K₁ ⊔ K₂) :=
    comap_fromSpec_eq_affineCenter (I₁ ⊔ I₂) ⟨U, hU⟩
  let B₀ := affineProjBlowupDatum (K₁ ⊔ K₂)
  let b : B₀.Y ⟶ B.Y := BaseChange.map u hc B B₀
  have hb : IsPullback b B₀.map B.map u :=
    BaseChange.isPullback_of_flat u inferInstance hc B B₀
  let : IsOpenImmersion b := MorphismProperty.of_isPullback hb.flip inferInstance
  have hbrange : Set.range b = B.map ⁻¹' Set.range u := by
    rw [← hb.isoPullback_hom_fst, Scheme.Hom.Range.range_iso_comp,
      Scheme.Pullback.range_fst]
  let e : pullback p₀ B₀.map ⟶ pullback p B.map :=
    pullback.map _ _ _ _ v b u hp (BaseChange.map_triangle u hc B B₀).symm
  let : IsOpenImmersion e := by dsimp [e]; infer_instance
  have he₁ : e ≫ pullback.fst p B.map = pullback.fst p₀ B₀.map ≫ v :=
    pullback.lift_fst _ _ _
  have he₂ : e ≫ pullback.snd p B.map = pullback.snd p₀ B₀.map ≫ b :=
    pullback.lift_snd _ _ _
  have herange : Set.range e = pullback.fst p B.map ⁻¹' Set.range v ∩
      pullback.snd p B.map ⁻¹' Set.range b :=
    Scheme.Pullback.range_map _ _ _ _ _ _ _ _ _
  have hzrange : z ∈ Set.range e := by
    rw [herange, hbrange]
    refine ⟨?_, ?_⟩
    · change pullback.fst p B.map z ∈ Set.range hW.fromSpec
      rw [hW.range_fromSpec]
      exact hzW
    · change B.map (pullback.snd p B.map z) ∈ Set.range hU.fromSpec
      rw [hU.range_fromSpec]
      have hw := congrArg (fun g : pullback p B.map ⟶ X => g z)
        (pullback.condition (f := p) (g := B.map))
      change p (pullback.fst p B.map z) = B.map (pullback.snd p B.map z) at hw
      rw [← hw]
      exact hxU
  obtain ⟨z₀, rfl⟩ := hzrange
  have hring : K₂.map (algebraMap A R) ≤ (K₁ ^ 2).map (algebraMap A R) ⊔ L := by
    have h := hcontain ⟨W, hW⟩
    change (I₂.comap p).ideal ⟨W, hW⟩ ≤
      ((I₁ ^ 2).comap p).ideal ⟨W, hW⟩ ⊔ L at h
    rw [Scheme.IdealSheafData.ideal_comap_eq_map_appLE I₂ p ⟨U, hU⟩ ⟨W, hW⟩ hWU,
      Scheme.IdealSheafData.ideal_comap_eq_map_appLE (I₁ ^ 2) p ⟨U, hU⟩ ⟨W, hW⟩ hWU] at h
    exact h
  have hlocalS : v ⁻¹' S ⊆ PrimeSpectrum.zeroLocus (L : Set R) := by
    intro y hy
    exact (Scheme.IdealSheafData.fromSpec_mem_support_iff J ⟨W, hW⟩ y).mp (hSJ hy)
  have hlocalAvoid : ∀ y ∈ v ⁻¹' S, PrimeSpectrum.comap (algebraMap A R) y ∉
      PrimeSpectrum.zeroLocus (K₂ : Set A) := by
    intro y hy hbad
    have hmem : u (p₀ y) ∈ I₂.support :=
      (Scheme.IdealSheafData.fromSpec_mem_support_iff I₂ ⟨U, hU⟩ (p₀ y)).mpr hbad
    have hw := congrArg (fun g : Spec R ⟶ X => g y) hp
    change u (p₀ y) = p (v y) at hw
    exact hSavoid (v y) hy (hw ▸ hmem)
  have hlocalT : u ⁻¹' T ⊆ PrimeSpectrum.zeroLocus (K₁ : Set A) := by
    intro y hy
    exact (Scheme.IdealSheafData.fromSpec_mem_support_iff I₁ ⟨U, hU⟩ y).mp (hT hy)
  have hlocalTAvoid : Disjoint (u ⁻¹' T)
      (PrimeSpectrum.zeroLocus ((K₁ ⊔ K₂ : Ideal A) : Set A)) := by
    apply Set.disjoint_left.mpr
    intro y hy hbad
    exact Set.disjoint_left.mp hTavoid hy
      ((Scheme.IdealSheafData.fromSpec_mem_support_iff (I₁ ⊔ I₂) ⟨U, hU⟩ y).mpr hbad)
  have hsep := affine_boundary_separation K₁ K₂ B₀ L hring
    (v ⁻¹' S) hlocalS hlocalAvoid (u ⁻¹' T) hlocalT hlocalTAvoid
  have hclosedS : e ⁻¹' closure (pullback.fst p B.map ⁻¹' S) =
      closure (pullback.fst p₀ B₀.map ⁻¹' (v ⁻¹' S)) := by
    rw [e.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage e.continuous]
    congr 1
    ext y
    change pullback.fst p B.map (e y) ∈ S ↔ v (pullback.fst p₀ B₀.map y) ∈ S
    rw [← Scheme.Hom.comp_apply, he₁, Scheme.Hom.comp_apply]
  have hclosedT : b ⁻¹' closure (B.map ⁻¹' T) =
      closure (B₀.map ⁻¹' (u ⁻¹' T)) := by
    rw [b.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage b.continuous]
    congr 1
    ext y
    change B.map (b y) ∈ T ↔ u (B₀.map y) ∈ T
    rw [← Scheme.Hom.comp_apply, hb.w, Scheme.Hom.comp_apply]
  have hz₀ : z₀ ∈ closure (pullback.fst p₀ B₀.map ⁻¹' (v ⁻¹' S)) := by
    rw [← hclosedS]
    exact hz
  have hz₀T : pullback.snd p₀ B₀.map z₀ ∈ closure (B₀.map ⁻¹' (u ⁻¹' T)) := by
    rw [← hclosedT]
    change b (pullback.snd p₀ B₀.map z₀) ∈ closure (B.map ⁻¹' T)
    rw [← Scheme.Hom.comp_apply, ← he₂, Scheme.Hom.comp_apply]
    exact hzT
  exact Set.disjoint_left.mp hsep hz₀ hz₀T

/-- **Conrad's Lemma 1.5, separation conclusion.** The kernel is that of the
original immersion. The source and its base change may be nonreduced and have
arbitrary dimension; the exact squared-ideal containment is retained. -/
theorem originalDiagram_boundary_separation {X Z Y : Scheme.{u}} (p : Z ⟶ X)
    (f : Y ⟶ Z) [IsImmersion f] [QuasiCompact f]
    (U V : X.Opens) (hUV : U ≤ V) (hfU : Set.range (f ≫ p) ⊆ U)
    (I₁ I₂ : X.IdealSheafData)
    (hI₁ : (V : Set X) \ (U : Set X) ⊆ I₁.support)
    (_hI₁U : (I₁.support : Set X) ⊆ (U : Set X)ᶜ)
    (hI₂ : (I₂.support : Set X) ⊆ (I₁.support : Set X) ∩ (V : Set X)ᶜ)
    (hcontain : I₂.comap p ≤ (I₁ ^ 2).comap p ⊔ f.ker)
    (B : BlowupDatum (I₁ ⊔ I₂)) :
    Disjoint
      (closure (Set.range (pullback.snd f (pullback.fst p B.map))))
      (pullback.snd p B.map ⁻¹'
        closure (B.map ⁻¹' ((V : Set X) \ (U : Set X)))) := by
  have hSavoid : ∀ z ∈ Set.range f, p z ∉ I₂.support := by
    rintro _ ⟨y, rfl⟩ hy
    exact (hI₂ hy).2 (hUV (hfU ⟨y, rfl⟩))
  have hTavoid : Disjoint ((V : Set X) \ (U : Set X)) (I₁ ⊔ I₂).support := by
    apply Set.disjoint_left.mpr
    intro x hx hxI
    have hxI₂ : x ∈ I₂.support := by
      rw [Scheme.IdealSheafData.support_sup] at hxI
      exact hxI.2
    exact (hI₂ hxI₂).2 hx.1
  rw [Scheme.Pullback.range_snd]
  exact boundary_separation p I₁ I₂ B f.ker hcontain (Set.range f)
    f.range_subset_ker_support hSavoid ((V : Set X) \ (U : Set X)) hI₁ hTavoid

/-- The canonical blowup in Conrad's Lemma 1.5 is proper over a locally
Noetherian base, unchanged over the protected larger open, and separates the
specified closures in the actual original diagram. -/
theorem canonical_boundary_separation {X Z Y : Scheme.{u}} [IsLocallyNoetherian X]
    (p : Z ⟶ X) (f : Y ⟶ Z) [IsImmersion f] [QuasiCompact f]
    (U V : X.Opens) (hUV : U ≤ V) (hfU : Set.range (f ≫ p) ⊆ U)
    (I₁ I₂ : X.IdealSheafData)
    (hI₁ : (V : Set X) \ (U : Set X) ⊆ I₁.support)
    (hI₁U : (I₁.support : Set X) ⊆ (U : Set X)ᶜ)
    (hI₂ : (I₂.support : Set X) ⊆ (I₁.support : Set X) ∩ (V : Set X)ᶜ)
    (hcontain : I₂.comap p ≤ (I₁ ^ 2).comap p ⊔ f.ker) :
    let B := blowupDatum (I₁ ⊔ I₂)
    IsProper B.map ∧ IsIso (B.map ∣_ V) ∧
      Disjoint
        (closure (Set.range (pullback.snd f (pullback.fst p B.map))))
        (pullback.snd p B.map ⁻¹'
          closure (B.map ⁻¹' ((V : Set X) \ (U : Set X)))) := by
  dsimp only
  let B := blowupDatum (I₁ ⊔ I₂)
  refine ⟨B.isProper_of_isLocallyNoetherian, ?_,
    originalDiagram_boundary_separation p f U V hUV hfU I₁ I₂ hI₁ hI₁U hI₂ hcontain B⟩
  apply B.restrict_isIso_of_comap_eq_top
  apply BlowupDatum.comap_eq_top_of_disjoint
  apply Set.disjoint_left.mpr
  intro x hx hxI
  rw [Scheme.IdealSheafData.support_sup] at hxI
  exact (hI₂ hxI.2).2 hx

end AlgebraicGeometry.Scheme.Blowup
