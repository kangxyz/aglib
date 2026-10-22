/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Boundary.CommonDomain
public import Aglib.AlgebraicGeometry.Compactification.Boundary.Transfer
public import Aglib.AlgebraicGeometry.SchemeTheoreticImage.FiniteProductComparison
public import Aglib.AlgebraicGeometry.SchemeTheoreticImage.FiniteProductSource
public import Aglib.AlgebraicGeometry.Blowup.AdmissibleSequence

/-!
# Finite boundary control on the actual product images

For normalized models with closed partial graphs, the original common source
and both finite-product schematic images are retained literally. Actual
protected centres are constructed, and the closure-disjointness conclusion
holds on the new native image. The initial boundary-empty hypothesis is the
one subsequently supplied by the original finite open cover.
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory Limits TopologicalSpace
universe u

namespace AlgebraicGeometry.Scheme.Compactification

/-- Finite normalized-model boundary control. No schematic-image base-change
identity or ideal-choice supplier is assumed. -/
theorem exists_normalized_finite_boundary_modification
    {S X : Scheme.{u}} [IsNoetherian S] {U : Over S} [IsNoetherian U.left]
    {n : ℕ} (C : Fin (n + 1) → Over S) [∀ i, IsProper (C i).hom]
    (j : ∀ i, U ⟶ C i) [IsOpenImmersion (j 0).left]
    (pX : X ⟶ S) (V : ∀ i, (C i).left.Opens)
    (q : ∀ i, (V i).toScheme ⟶ X)
    (hq : ∀ i, (V i).ι ≫ (C i).hom = q i ≫ pX)
    [∀ i, IsClosedImmersion (pullback.lift (V i).ι (q i) (hq i))]
    (a : ∀ i, U.left ⟶ (V i).toScheme)
    (ha : ∀ i, a i ≫ (V i).ι = (j i).left)
    (g : U.left ⟶ X) (hag : ∀ i, a i ≫ q i = g)
    (F : ∀ i, Closeds (V i).toScheme)
    (hempty : (⋂ i,
      ((finiteProductOverLift C j).left.imageι ≫ (finiteProductOverπ C i).left) ⁻¹'
        ((V i).ι '' (F i : Set (V i).toScheme))) = ∅) :
    ∃ (C' : Fin (n + 1) → Over S) (β : ∀ i, C' i ⟶ C i)
      (j' : ∀ i, U ⟶ C' i),
      (∀ i, Blowup.AdmissibleSequence (V i) (β i).left) ∧
      (∀ i, IsProper (C' i).hom) ∧ (∀ i, j' i ≫ β i = j i) ∧
      IsImmersion (j' 0).left ∧
      (⋂ i, ((finiteProductOverLift C' j').left.imageι ≫
        (finiteProductOverπ C' i).left) ⁻¹'
          closure ((β i).left ⁻¹' ((V i).ι '' (F i : Set (V i).toScheme)))) = ∅ := by
  let f := (finiteProductOverLift C j).left
  let M := f.image
  let s : U.left ⟶ M := f.toImage
  let pM : M ⟶ S := f.imageι ≫ (finiteProductOver C).hom
  let π : ∀ i, M ⟶ (C i).left := fun i => f.imageι ≫ (finiteProductOverπ C i).left
  let : IsNoetherian M := finiteProductOverLift_image_isNoetherian C j
  let : IsSchemeTheoreticallyDominant s := isSchemeTheoreticallyDominant_toImage f
  let : ∀ i, IsNoetherian (C i).left := fun i => by
    let : IsLocallyNoetherian (C i).left := LocallyOfFiniteType.isLocallyNoetherian (C i).hom
    let : CompactSpace (C i).left := QuasiCompact.compactSpace_of_compactSpace (C i).hom
    exact ⟨⟩
  have hsπ : ∀ i, s ≫ π i = (j i).left := by
    intro i
    dsimp only [π]
    rw [← Category.assoc, Scheme.Hom.toImage_imageι]
    exact congrArg (fun z => z.left) (finiteProductOverLift_π C j i)
  have hπ : ∀ i, π i ≫ (C i).hom = pM := by
    intro i
    simp only [π, pM, Category.assoc, finiteProductOverπ_hom]
  let Ω := π 0 ⁻¹ᵁ V 0
  have hΩ : ∀ i, π i ⁻¹ᵁ V i = Ω := by
    intro i
    exact preimage_open_eq_of_common_closedGraphs (fun i => (C i).hom) pM pX π hπ
      V q hq s g a (fun i => (ha i).trans (hsπ i).symm) hag i 0
  obtain ⟨hunit, T, hT, hcentres⟩ := exists_projected_boundary_centres π V F Ω hΩ hempty
  choose I _hsupp hI hproper _hiso hcontrol using hcentres
  let Bᵢ := fun i => Blowup.blowupDatum (I i)
  let C' : Fin (n + 1) → Over S := fun i => Over.mk ((Bᵢ i).map ≫ (C i).hom)
  let β : ∀ i, C' i ⟶ C i := fun i => Over.homMk (Bᵢ i).map rfl
  have hIj : ∀ i, (I i).comap (j i).left = ⊤ := by
    intro i
    rw [← ha i, IdealSheafData.comap_comp, hI i, IdealSheafData.comap_top]
  let t : ∀ i, U.left ⟶ (Bᵢ i).Y := fun i =>
    (Bᵢ i).lift (j i).left (Blowup.cartier_of_comap_eq_top (I i) (j i).left (hIj i))
  have ht : ∀ i, t i ≫ (Bᵢ i).map = (j i).left := fun i => (Bᵢ i).lift_map _ _
  let j' : ∀ i, U ⟶ C' i := fun i => Over.homMk (t i) (by
    change t i ≫ (Bᵢ i).map ≫ (C i).hom = U.hom
    rw [← Category.assoc, ht i]
    exact (j i).w)
  have hw : ∀ i, j' i ≫ β i = j i := by
    intro i
    apply Over.OverMorphism.ext
    exact ht i
  have hseq : ∀ i, Blowup.AdmissibleSequence (V i) (β i).left := fun i =>
    Blowup.AdmissibleSequence.single (Bᵢ i) (V i) (hI i)
  let : ∀ i, IsProper (Bᵢ i).map := fun i => hproper i
  let : ∀ i, IsProper (C' i).hom := fun i => inferInstanceAs (IsProper ((Bᵢ i).map ≫ (C i).hom))
  have hj' : IsImmersion (j' 0).left := by
    have he : (j' 0).left ≫ (β 0).left = (j 0).left := congrArg (fun z => z.left) (hw 0)
    let : IsImmersion ((j' 0).left ≫ (β 0).left) := by rw [he]; infer_instance
    exact IsImmersion.of_comp _ (β 0).left
  refine ⟨C', β, j', hseq, fun i => inferInstance, hw, hj', ?_⟩
  let f' := (finiteProductOverLift C' j').left
  let M' := f'.image
  let s' : U.left ⟶ M' := f'.toImage
  let π' : ∀ i, M' ⟶ (C' i).left := fun i => f'.imageι ≫ (finiteProductOverπ C' i).left
  let r : M' ⟶ M := finiteProductImageComparison β j' j hw
  let : IsNoetherian M' := finiteProductOverLift_image_isNoetherian C' j'
  let : IsSchemeTheoreticallyDominant s' := isSchemeTheoreticallyDominant_toImage f'
  have hr : s' ≫ r = s := toImage_finiteProductImageComparison β j' j hw
  have hrπ : ∀ i, π' i ≫ (β i).left = r ≫ π i := by
    intro i
    simpa only [π, π', Category.assoc] using
      (finiteProductImageComparison_π β j' j hw i).symm
  let E := fun i => π i ⁻¹' ((V i).ι '' (F i : Set (V i).toScheme))
  let K := fun i => IdealSheafData.vanishingIdeal (Closeds.closure (E i))
  let B := Blowup.blowupDatum (⨆ i, K i)
  have hsV : ∀ i, Set.range (s ≫ π i) ⊆ V i := by
    intro i
    rw [hsπ i, ← ha i]
    rintro _ ⟨x, rfl⟩
    exact (a i x).property
  have hsΩ : Set.range s ⊆ Ω := by
    rintro _ ⟨x, rfl⟩
    exact hsV 0 ⟨x, rfl⟩
  let sΩ := IsOpenImmersion.lift Ω.ι s (by simpa only [Opens.range_ι] using hsΩ)
  have hsΩfac : sΩ ≫ Ω.ι = s := IsOpenImmersion.lift_fac _ _ _
  have hKs : (⨆ i, K i).comap s = ⊤ := by
    rw [← hsΩfac, IdealSheafData.comap_comp, hunit, IdealSheafData.comap_top]
  exact boundary_empty_of_projected_control π π' (fun i => (β i).left) r hrπ
    s s' hr V hsV (⨆ i, K i) hKs B
    (fun i => (V i).ι '' (F i : Set (V i).toScheme)) T hT hcontrol

end AlgebraicGeometry.Scheme.Compactification
