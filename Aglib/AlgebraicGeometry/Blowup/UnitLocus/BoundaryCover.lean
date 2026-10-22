/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.UnitLocus.Boundary
public import Aglib.AlgebraicGeometry.Blowup.AffineCenter.Restriction
public import Aglib.AlgebraicGeometry.Blowup.AffineAtlas
public import Aglib.AlgebraicGeometry.Blowup.FlatBaseChange
public import Aglib.AlgebraicGeometry.Blowup.Properness

/-!
# Native principal-boundary charts of a global blowup

The cover uses the original saturated affine charts over all affine opens of
the base. Every chart has its actual base-change map and original pivot.
The complement of the centre pulls back to the principal open of that pivot.
The cover itself is arbitrary-base; a finite subcover is selected only under
compactness, supplied for Noetherian bases by actual blowup properness.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Blowup.BoundaryCover

variable {X : Scheme.{u}} (I : X.IdealSheafData) (B : BlowupDatum I)

/-- Original affine base open together with an original centre-ideal pivot. -/
abbrev Index := Σ U : X.affineOpens, I.ideal U

/-- The literal saturated coordinate ring of the indexed chart. -/
abbrev ring (k : Index I) : CommRingCat :=
  .of (affineBlowupAlgebra Γ(X, k.1) (I.ideal k.1) k.2)

/-- The actual affine-base restriction comparison, with the native affine
Rees Proj as source. -/
def localMap (U : X.affineOpens) :
    (affineProjBlowupDatum (I.ideal U)).Y ⟶ B.Y :=
  BaseChange.map U.2.fromSpec (comap_fromSpec_eq_affineCenter I U) B
    (affineProjBlowupDatum (I.ideal U))

theorem localMap_isPullback (U : X.affineOpens) :
    IsPullback (localMap I B U) (affineProjBlowupDatum (I.ideal U)).map B.map U.2.fromSpec :=
  BaseChange.isPullback_of_flat U.2.fromSpec inferInstance
    (comap_fromSpec_eq_affineCenter I U) B (affineProjBlowupDatum (I.ideal U))

instance localMap_isOpenImmersion (U : X.affineOpens) :
    IsOpenImmersion (localMap I B U) :=
  MorphismProperty.of_isPullback (localMap_isPullback I B U).flip inferInstance

theorem localMap_range (U : X.affineOpens) :
    Set.range (localMap I B U) = B.map ⁻¹' Set.range U.2.fromSpec := by
  rw [← (localMap_isPullback I B U).isoPullback_hom_fst,
    Scheme.Hom.Range.range_iso_comp, Scheme.Pullback.range_fst]
  rfl

/-- The original saturated chart followed by the actual base-change comparison. -/
def chart (k : Index I) : Spec (ring I k) ⟶ B.Y :=
  affineProjChart (I.ideal k.1) k.2 ≫ localMap I B k.1

instance chart_isOpenImmersion (k : Index I) : IsOpenImmersion (chart I B k) := by
  unfold chart
  infer_instance

@[reassoc]
theorem chart_map (k : Index I) :
    chart I B k ≫ B.map =
      affineChartMap Γ(X, k.1) (I.ideal k.1) k.2 ≫ k.1.2.fromSpec := by
  rw [chart, Category.assoc, show localMap I B k.1 ≫ B.map =
    (affineProjBlowupDatum (I.ideal k.1)).map ≫ k.1.2.fromSpec from
      BaseChange.map_triangle _ _ _ _, ← Category.assoc]
  exact congrArg (fun g ↦ g ≫ k.1.2.fromSpec)
    (affineProjChart_map (I.ideal k.1) k.2)

/-- These actual charts cover the whole native global blowup. -/
theorem covers (y : B.Y) : ∃ k : Index I, y ∈ Set.range (chart I B k) := by
  obtain ⟨U, hU, hyU, _⟩ := exists_isAffineOpen_mem_and_subset
    (x := B.map y) (U := ⊤) (by trivial)
  let V : X.affineOpens := ⟨U, hU⟩
  have hy : y ∈ Set.range (localMap I B V) := by
    rw [localMap_range, hU.range_fromSpec]
    exact hyU
  obtain ⟨z, rfl⟩ := hy
  obtain ⟨a, w, hw⟩ := affineProjChart_covers (I.ideal V) z
  refine ⟨⟨V, a⟩, w, ?_⟩
  change localMap I B V (affineProjChart (I.ideal V) a w) = localMap I B V z
  exact congrArg (localMap I B V) hw

/-- The centre complement in each indexed chart is its original pivot's
principal open. This is the input to principal-open coordinate extension. -/
theorem chart_preimage_complement (k : Index I) :
    (chart I B k ≫ B.map) ⁻¹ᵁ I.support.compl =
      PrimeSpectrum.basicOpen (algebraMap Γ(X, k.1) (ring I k) k.2) := by
  have hopen : k.1.2.fromSpec ⁻¹ᵁ I.support.compl =
      (affineCenter Γ(X, k.1) (I.ideal k.1)).support.compl := by
    rw [← comap_fromSpec_eq_affineCenter I k.1, IdealSheafData.support_comap]
    rfl
  rw [chart_map, Scheme.Hom.comp_preimage, hopen]
  have h := UnitLocus.chart_preimage_complement (affineProjAtlas (I.ideal k.1)) k.2
  change (affineProjChart (I.ideal k.1) k.2 ≫ affineProjMap (I.ideal k.1)) ⁻¹ᵁ
    (affineCenter Γ(X, k.1) (I.ideal k.1)).support.compl = _ at h
  have he := congrArg (fun g : Spec (ring I k) ⟶ Spec Γ(X, k.1) ↦
    g ⁻¹ᵁ (affineCenter Γ(X, k.1) (I.ideal k.1)).support.compl)
    (affineProjChart_map (I.ideal k.1) k.2)
  exact he.symm.trans h

/-- The actual indexed affine open cover, before making a finiteness choice. -/
def cover : B.Y.AffineOpenCover where
  I₀ := Index I
  X := ring I
  f := chart I B
  idx y := (covers I B y).choose
  covers y := (covers I B y).choose_spec

/-- Compactness chooses finitely many of these very charts, retaining their
original affine base opens and pivot labels. -/
theorem exists_finite_cover [CompactSpace B.Y] :
    ∃ s : Finset (Index I), ∀ y : B.Y, ∃ k ∈ s, y ∈ Set.range (chart I B k) := by
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun k ↦ Set.range (chart I B k))
    (fun k ↦ IsOpenImmersion.isOpen_range (chart I B k))
    (fun y _ ↦ Set.mem_iUnion.mpr (covers I B y))
  refine ⟨s, fun y ↦ ?_⟩
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (hs (Set.mem_univ y))
  obtain ⟨hks, hy⟩ := Set.mem_iUnion.mp hk
  exact ⟨k, hks, hy⟩

/-- Noetherian properness supplies the required compactness; the selected
charts are still the original saturated affine charts. -/
theorem exists_finite_cover_of_isNoetherian [IsNoetherian X] :
    ∃ s : Finset (Index I), ∀ y : B.Y, ∃ k ∈ s, y ∈ Set.range (chart I B k) := by
  let : IsProper B.map := B.isProper_of_isLocallyNoetherian
  let : CompactSpace B.Y := QuasiCompact.compactSpace_of_compactSpace B.map
  exact exists_finite_cover I B

include B in
/-- The literal saturated chart rings are Noetherian over a locally
Noetherian base. -/
theorem ring_isNoetherian [IsLocallyNoetherian X] (k : Index I) :
    IsNoetherianRing (ring I k) := by
  let : IsProper B.map := B.isProper_of_isLocallyNoetherian
  let : IsLocallyNoetherian B.Y := LocallyOfFiniteType.isLocallyNoetherian B.map
  let : IsLocallyNoetherian (Spec (ring I k)) :=
    LocallyOfFiniteType.isLocallyNoetherian (chart I B k)
  exact isLocallyNoetherian_Spec.mp inferInstance

end AlgebraicGeometry.Scheme.Blowup.BoundaryCover
