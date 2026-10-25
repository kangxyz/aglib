/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ChartGeometricComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Local.ResidueFieldExtension
public import Aglib.AlgebraicGeometry.EtaleCohomology.PullbackIsomorphism
public import Aglib.RingTheory.Henselian.StrictHenselization.SeparablyClosedResidue

/-! # The original geometric-point transfer for a projective-line chart

An actual projective-line chart is transported to the strict-local and chosen
geometric fibres. Their original projections identify the retained point map
with the native line map of the actual field-valued ring homomorphism. Its
factorization through the native residue field supplies bijectivity without
identifying that residue field with the chosen separably closed field.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Stalk

universe u

attribute [local instance] hasSheafifyLarge HasExt.standard

open Continuity Finite.GeometricNeighborhood
open AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct

private theorem pullback_of_projection_iso {C : Type*} [Category* C]
    {X Y Z W : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    (e : W ≅ pullback f g) (p : W ⟶ X) (q : W ⟶ Y)
    (hp : e.hom ≫ pullback.fst f g = p) (hq : e.hom ≫ pullback.snd f g = q) :
    IsPullback p q f g := by
  have hw : p ≫ f = q ≫ g := by
    calc
      _ = (e.hom ≫ pullback.fst f g) ≫ f := congrArg (fun k => k ≫ f) hp.symm
      _ = e.hom ≫ (pullback.fst f g ≫ f) := Category.assoc _ _ _
      _ = e.hom ≫ (pullback.snd f g ≫ g) :=
        congrArg (fun k => e.hom ≫ k) (pullback.condition (f := f) (g := g))
      _ = (e.hom ≫ pullback.snd f g) ≫ g := (Category.assoc _ _ _).symm
      _ = _ := congrArg (fun k => k ≫ g) hq
  exact IsPullback.of_iso_pullback ⟨hw⟩ e hp hq

private theorem line_chart_pullback
    {R K : Type u} [CommRing R] [CommRing K] (τ : R →+* K)
    {X S : Scheme.{u}} (f : X ⟶ S) (j : Spec (.of R) ⟶ S)
    (E : Over.mk (ProjectiveLine.structureMap R) ≅ Over.mk (pullback.fst j f))
    (a : Spec (.of K) ⟶ S) (ha : Spec.map (CommRingCat.ofHom τ) ≫ j = a) :
    IsPullback (lineBaseChangeMap τ ≫ E.hom.left ≫ pullback.snd j f)
      (ProjectiveLine.structureMap K) f a := by
  let eR := (Over.forget (Spec (.of R))).mapIso E
  have hR : IsPullback (E.hom.left ≫ pullback.snd j f)
      (ProjectiveLine.structureMap R) f j :=
    (pullback_of_projection_iso j f eR (ProjectiveLine.structureMap R)
      (E.hom.left ≫ pullback.snd j f) E.hom.w rfl).flip
  let eK := (Over.forget (Spec (.of K))).mapIso (lineOverBaseChangeIso τ)
  have hK : IsPullback (lineBaseChangeMap τ) (ProjectiveLine.structureMap K)
      (ProjectiveLine.structureMap R) (Spec.map (CommRingCat.ofHom τ)) :=
    pullback_of_projection_iso (ProjectiveLine.structureMap R)
      (Spec.map (CommRingCat.ofHom τ)) eK (lineBaseChangeMap τ)
      (ProjectiveLine.structureMap K) (lineOverBaseChangeIso_hom_fst τ)
      (lineOverBaseChangeIso τ).hom.w
  simpa only [ha] using hK.paste_horiz hR

private def lineChartIso
    {R K : Type u} [CommRing R] [CommRing K] (τ : R →+* K)
    {X S : Scheme.{u}} (f : X ⟶ S) (j : Spec (.of R) ⟶ S)
    (E : Over.mk (ProjectiveLine.structureMap R) ≅ Over.mk (pullback.fst j f))
    (a : Spec (.of K) ⟶ S) (ha : Spec.map (CommRingCat.ofHom τ) ≫ j = a) :
    ProjectiveLine.projectiveP1 K ≅ pullback a f :=
  (line_chart_pullback τ f j E a ha).flip.isoPullback

private theorem lineChartIso_fst
    {R K : Type u} [CommRing R] [CommRing K] (τ : R →+* K)
    {X S : Scheme.{u}} (f : X ⟶ S) (j : Spec (.of R) ⟶ S)
    (E : Over.mk (ProjectiveLine.structureMap R) ≅ Over.mk (pullback.fst j f))
    (a : Spec (.of K) ⟶ S) (ha : Spec.map (CommRingCat.ofHom τ) ≫ j = a) :
    (lineChartIso τ f j E a ha).hom ≫ pullback.fst a f = ProjectiveLine.structureMap K :=
  (line_chart_pullback τ f j E a ha).flip.isoPullback_hom_fst

private theorem lineChartIso_snd
    {R K : Type u} [CommRing R] [CommRing K] (τ : R →+* K)
    {X S : Scheme.{u}} (f : X ⟶ S) (j : Spec (.of R) ⟶ S)
    (E : Over.mk (ProjectiveLine.structureMap R) ≅ Over.mk (pullback.fst j f))
    (a : Spec (.of K) ⟶ S) (ha : Spec.map (CommRingCat.ofHom τ) ≫ j = a) :
    (lineChartIso τ f j E a ha).hom ≫ pullback.snd a f =
      lineBaseChangeMap τ ≫ E.hom.left ≫ pullback.snd j f :=
  (line_chart_pullback τ f j E a ha).flip.isoPullback_hom_snd

private theorem pullback_map_iso_square {C : Type*} [Category* C]
    {X S A B P Q : C} (f : X ⟶ S) (a : A ⟶ S) (b : B ⟶ S)
    [HasPullback a f] [HasPullback b f]
    (e : P ≅ pullback a f) (d : Q ≅ pullback b f)
    (μ : pullback b f ⟶ pullback a f) (l : Q ⟶ P) (r : B ⟶ A)
    (s : P ⟶ A) (t : Q ⟶ B) (x : P ⟶ X) (y : Q ⟶ X)
    (ef : e.hom ≫ pullback.fst a f = s) (es : e.hom ≫ pullback.snd a f = x)
    (df : d.hom ≫ pullback.fst b f = t) (ds : d.hom ≫ pullback.snd b f = y)
    (mf : μ ≫ pullback.fst a f = pullback.fst b f ≫ r)
    (ms : μ ≫ pullback.snd a f = pullback.snd b f)
    (lf : l ≫ s = t ≫ r) (ls : l ≫ x = y) : d.hom ≫ μ = l ≫ e.hom := by
  apply pullback.hom_ext
  · calc
      _ = d.hom ≫ (μ ≫ pullback.fst a f) := Category.assoc _ _ _
      _ = d.hom ≫ (pullback.fst b f ≫ r) := congrArg (fun k => d.hom ≫ k) mf
      _ = (d.hom ≫ pullback.fst b f) ≫ r := (Category.assoc _ _ _).symm
      _ = t ≫ r := congrArg (fun k => k ≫ r) df
      _ = l ≫ s := lf.symm
      _ = l ≫ (e.hom ≫ pullback.fst a f) := congrArg (fun k => l ≫ k) ef.symm
      _ = _ := (Category.assoc _ _ _).symm
  · calc
      _ = d.hom ≫ (μ ≫ pullback.snd a f) := Category.assoc _ _ _
      _ = d.hom ≫ pullback.snd b f := congrArg (fun k => d.hom ≫ k) ms
      _ = y := ds
      _ = l ≫ x := ls.symm
      _ = l ≫ (e.hom ≫ pullback.snd a f) := congrArg (fun k => l ≫ k) es.symm
      _ = _ := (Category.assoc _ _ _).symm

private theorem bijective_from_comparison {A B C D : Type*}
    (a : A → B) (b : B → C) (c : A → D) (d : D → C)
    (ha : Function.Bijective a) (hb : Function.Bijective b) (hd : Function.Bijective d)
    (h : ∀ x, d (c x) = b (a x)) : Function.Bijective c := by
  constructor
  · intro x y hxy
    exact ha.injective (hb.injective ((h x).symm.trans ((congrArg d hxy).trans (h y))))
  · intro y
    obtain ⟨x, hx⟩ := (hb.comp ha).surjective (d y)
    exact ⟨x, hd.injective ((h x).trans hx)⟩

private theorem pullback_bijective_comp
    {X S T : Scheme.{u}} (f : S ⟶ X) (g : T ⟶ S)
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)
    (hf : Function.Bijective (cohomologyPullback.{u, u + 2, u + 2} f F q))
    (hg : Function.Bijective
      (cohomologyPullback.{u, u + 2, u + 2} g ((inverseImage f).obj F) q)) :
    Function.Bijective (cohomologyPullback.{u, u + 2, u + 2} (g ≫ f) F q) :=
  bijective_from_comparison (cohomologyPullback.{u, u + 2, u + 2} f F q)
    (cohomologyPullback.{u, u + 2, u + 2} g ((inverseImage f).obj F) q)
    (cohomologyPullback.{u, u + 2, u + 2} (g ≫ f) F q)
    (Sheaf.H.map ((inverseImageComp f g).hom.app F) q) hf hg
    (cohomologyMapIso_bijective ((inverseImageComp f g).app F) q)
    (cohomologyPullback_comp f g F q)

private theorem pullback_bijective_cancel_iso
    {X S T : Scheme.{u}} (f : S ⟶ X) (e : T ≅ S) (h : T ⟶ X)
    (he : e.hom ≫ f = h) (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)
    (hh : Function.Bijective (cohomologyPullback.{u, u + 2, u + 2} h F q)) :
    Function.Bijective (cohomologyPullback.{u, u + 2, u + 2} f F q) := by
  subst h
  exact bijective_from_comparison (cohomologyPullback.{u, u + 2, u + 2} (e.hom ≫ f) F q)
    (Sheaf.H.map ((inverseImageComp f e.hom).hom.app F) q)
    (cohomologyPullback.{u, u + 2, u + 2} f F q)
    (cohomologyPullback.{u, u + 2, u + 2} e.hom ((inverseImage f).obj F) q)
    hh (cohomologyMapIso_bijective ((inverseImageComp f e.hom).app F) q)
    (cohomologyPullback_bijective_of_isEquivalence e.hom ((inverseImage f).obj F) q)
    (fun x => (cohomologyPullback_comp f e.hom F q x).symm)

private theorem pullback_bijective_iso_square
    {X Y X' Y' : Scheme.{u}} (a : X' ≅ X) (b : Y' ≅ Y)
    (f : Y ⟶ X) (g : Y' ⟶ X') (h : b.hom ≫ f = g ≫ a.hom)
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)
    (hg : Function.Bijective
      (cohomologyPullback.{u, u + 2, u + 2} g ((inverseImage a.hom).obj F) q)) :
    Function.Bijective (cohomologyPullback.{u, u + 2, u + 2} f F q) :=
  pullback_bijective_cancel_iso f b (g ≫ a.hom) h F q
    (pullback_bijective_comp a.hom g F q
      (cohomologyPullback_bijective_of_isEquivalence a.hom F q) hg)

private theorem pullback_bijective_of_map_eq
    {X Y : Scheme.{u}} (f g : Y ⟶ X) (h : f = g)
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)
    (hf : Function.Bijective (cohomologyPullback.{u, u + 2, u + 2} f F q)) :
    Function.Bijective (cohomologyPullback.{u, u + 2, u + 2} g F q) := by
  subst g
  exact hf

private theorem killed_functor_obj {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] (L : C ⥤ D) [L.Additive]
    (n : ℕ) (F : C) (hF : n • 𝟙 F = 0) : n • 𝟙 (L.obj F) = 0 := by
  simpa using congrArg L.map hF

private theorem relativeTransfer_bijective_of_pullback
    {X : Scheme.{u}} (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)
    {A B : Over X} (a : A ⟶ B)
    (h : Function.Bijective
      (cohomologyPullback.{u, u + 2, u + 2} a.left ((inverseImage B.hom).obj F) q)) :
    Function.Bijective (relativeCohomologyTransfer.{u, u + 2} F q a) :=
  (cohomologyMapIso_bijective
    ((pullbackTriangleIso A.hom B.hom a.left (Over.w a)).symm.app F) q).comp h

private theorem strictLocal_nativeLine_point_bijective
    (R Ω : Type u) [CommRing R] [Field Ω] [IsSepClosed Ω] [Algebra R Ω]
    (n : ℕ) (hn : n ≠ 0)
    (F : AbelianSheaf.{u, u + 1} (ProjectiveLine.projectiveP1 (GeometricEtaleColimit R Ω)))
    (hF : n • 𝟙 F = 0) (q : ℕ) :
    Function.Bijective (cohomologyPullback.{u, u + 2, u + 2}
      (lineBaseChangeMap (GeometricEtaleColimit.residue R Ω).toRingHom) F q) :=
  pullback_bijective_of_map_eq
    (lineBaseChangeMap ((GeometricEtaleColimit.residueFieldEmbedding R Ω).comp
      (IsLocalRing.residue (GeometricEtaleColimit R Ω))))
    (lineBaseChangeMap (GeometricEtaleColimit.residue R Ω).toRingHom)
    (congrArg lineBaseChangeMap (GeometricEtaleColimit.residueFieldEmbedding_comp_residue R Ω))
    F q (Proper.projectiveLine_residueFieldExtension_bijective_of_killed
      (GeometricEtaleColimit R Ω) Ω (GeometricEtaleColimit.residueFieldEmbedding R Ω)
      n hn F hF q)

/-- For an actual projective-line chart, the defined transfer from the chosen
strict-local fibre to the retained geometric fibre is bijective. -/
theorem chartGeometricPointMap_projectiveLine_transfer_bijective
    (R Ω : Type u) [CommRing R] [Field Ω] [IsSepClosed Ω] [Algebra R Ω]
    {X S : Scheme.{u}} (η : Spec (.of Ω) ⟶ S) (f : X ⟶ S)
    (j : Spec (.of R) ⟶ S) [Etale j] [Mono j]
    (hη : Spec.algebraMap R Ω ≫ j = η)
    (E : Over.mk (ProjectiveLine.structureMap R) ≅ Over.mk (pullback.fst j f))
    (n : ℕ) (hn : n ≠ 0) (F : AbelianSheaf.{u, u + 1} X) (hF : n • 𝟙 F = 0) (q : ℕ) :
    Function.Bijective
      (relativeCohomologyTransfer.{u, u + 2} F q (chartGeometricPointMap Ω η f R j hη)) := by
  let B := GeometricEtaleColimit R Ω
  let a : Spec (.of B) ⟶ S := Spec.algebraMap R B ≫ j
  let ρ : B →+* Ω := (GeometricEtaleColimit.residue R Ω).toRingHom
  let eB : ProjectiveLine.projectiveP1 B ≅ pullback a f :=
    lineChartIso (algebraMap R B) f j E a rfl
  let eΩ : ProjectiveLine.projectiveP1 Ω ≅ pullback η f :=
    lineChartIso (algebraMap R Ω) f j E η hη
  let μ : pullback η f ⟶ pullback a f := (chartGeometricPointMap Ω η f R j hη).left
  let l := lineBaseChangeMap ρ
  let x := lineBaseChangeMap (algebraMap R B) ≫ E.hom.left ≫ pullback.snd j f
  let y := lineBaseChangeMap (algebraMap R Ω) ≫ E.hom.left ≫ pullback.snd j f
  have hl : l ≫ lineBaseChangeMap (algebraMap R B) = lineBaseChangeMap (algebraMap R Ω) :=
    (Proper.projectiveLine_nativeBaseChangeMap_comp (algebraMap R B) ρ).trans
      (congrArg lineBaseChangeMap (GeometricEtaleColimit.residue_comp_of R Ω))
  have hx : l ≫ x = y :=
    (Category.assoc l (lineBaseChangeMap (algebraMap R B))
      (E.hom.left ≫ pullback.snd j f)).symm.trans
      (congrArg (fun k => k ≫ E.hom.left ≫ pullback.snd j f) hl)
  have hsquare : eΩ.hom ≫ μ = l ≫ eB.hom :=
    pullback_map_iso_square f a η eB eΩ μ l (point R Ω)
      (ProjectiveLine.structureMap B) (ProjectiveLine.structureMap Ω) x y
      (lineChartIso_fst (algebraMap R B) f j E a rfl)
      (lineChartIso_snd (algebraMap R B) f j E a rfl)
      (lineChartIso_fst (algebraMap R Ω) f j E η hη)
      (lineChartIso_snd (algebraMap R Ω) f j E η hη)
      (chartGeometricPointMap_fst Ω η f R j hη)
      (chartGeometricPointMap_snd Ω η f R j hη)
      (lineBaseChangeMap_over ρ) hx
  let H := (inverseImage (pullback.snd a f)).obj F
  let H' := (inverseImage eB.hom).obj H
  have hH : n • 𝟙 H = 0 := killed_functor_obj (inverseImage (pullback.snd a f)) n F hF
  have hH' : n • 𝟙 H' = 0 := killed_functor_obj (inverseImage eB.hom) n H hH
  have hlbij : Function.Bijective (cohomologyPullback.{u, u + 2, u + 2} l H' q) :=
    strictLocal_nativeLine_point_bijective R Ω n hn H' hH' q
  have hμ : Function.Bijective (cohomologyPullback.{u, u + 2, u + 2} μ H q) :=
    pullback_bijective_iso_square eB eΩ μ l hsquare H q hlbij
  exact relativeTransfer_bijective_of_pullback F q (chartGeometricPointMap Ω η f R j hη) hμ

end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
