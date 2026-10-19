/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Grassmannian.ProjectiveSpace.Charts
public import Aglib.AlgebraicGeometry.Grassmannian.Representability
public import Aglib.AlgebraicGeometry.ProjectiveSpace.SchemeOver
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Transition
public import Aglib.RingTheory.Grassmannian.BaseChangeFormula

/-!
# Projective space is the Grassmannian of rank-one quotients

For a commutative ring `R` and a coordinate labeling `e : ι ≃ Fin m`, the glued Grassmannian
`Grassmannian.scheme R 1 m` of rank-one quotients of `R^m` is isomorphic over `Spec R` to Aglib's
polynomial projective space `ProjectiveSpace R ι` (`grassmannianIso`, `grassmannianOverIso`).

The comparison matches the Grassmannian chart at the basis vector `e_{e i}` with the standard
chart `D₊(Xᵢ)`: the chart coordinate `Φ_{0 j}` corresponds to the ratio `X_{e⁻¹ j} / X_i`
(`chartToCoordinate`, `coordinateToChart` in `Charts`). The map `toGrassmannian` from projective
space is glued on the standard cover; its chart maps agree on `D₊(Xᵢ Xₗ)` because the two
chart sections differ by the unit `X_i / X_l`, so their chart points agree
(`ofChartSection_overlap`). The inverse
`ofGrassmannian` is glued on the Grassmannian charts; its chart maps agree on the overlaps because
the overlap of the charts at `I` and `J` is identified with `D₊(Xᵢ Xₗ)` (`overlapChartEquiv`).
Both composites are identities chart by chart: `toGrassmannian ≫ ofGrassmannian` because the
chart ring maps are mutually inverse (`specMap_comp_chartAwayι_of_eq`), and
`ofGrassmannian ≫ toGrassmannian` by the classified point on the Grassmannian side.

This is Stacks, Tag 089V (Lemma 27.22.3, `G(n, n + 1) ≅ P^n_ℤ`), proved here directly by chart
gluing over any base ring; see `grassmannianIso` for the encoded subset.

## Main definitions and results

- `AlgebraicGeometry.ProjectiveSpace.toGrassmannian e :
  ProjectiveSpace R ι ⟶ Grassmannian.scheme R 1 m`.
- `AlgebraicGeometry.ProjectiveSpace.ofGrassmannian e :
  Grassmannian.scheme R 1 m ⟶ ProjectiveSpace R ι`.
- `AlgebraicGeometry.ProjectiveSpace.grassmannianIso e` and its version over `Spec R`,
  `grassmannianOverIso e : Grassmannian.schemeOver R 1 m ≅ ProjectiveSpace.schemeOver R ι`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite Limits MvPolynomial HomogeneousLocalization

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveSpace

open Module.Grassmannian (ChartRing coordinateTuple chartTransitionDet algHomToChartSection
  algHomToChartSection_mem ofChartSection)

variable (R : CommRingCat.{u}) {ι : Type u} {m : ℕ} (e : ι ≃ Fin m)

/-- The standard chart ring `B_i` as an `R`-algebra. -/
abbrev coordinateAlg (i : ι) : CommAlgCat.{u} R := CommAlgCat.of R (coordinateRing R ι i)

variable {R} in
/-- The Grassmannian chart attached to the coordinate `i`: the chart at `e_{e i}`. -/
abbrev chartIndex (i : ι) : ULift.{u} (Fin 1 → Fin m) := ⟨fun _ ↦ e i⟩

variable {R} in
/-- The coordinate attached to the Grassmannian chart `I`. -/
abbrev chartCoord (I : ULift.{u} (Fin 1 → Fin m)) : ι := e.symm (I.down 0)

theorem chartCoord_spec (I : ULift.{u} (Fin 1 → Fin m)) : I.down 0 = e (chartCoord e I) :=
  (e.apply_symm_apply _).symm

/-- The standard chart `D₊(Xᵢ)` as an open immersion into projective space. -/
abbrev chartAwayι (i : ι) :
    Spec (CommRingCat.of (coordinateRing R ι i)) ⟶ ProjectiveSpace R ι :=
  Proj.awayι (homogeneousSubmodule ι R) (X i) (isHomogeneous_X R i) Nat.zero_lt_one

theorem coordinateCover_f (i : ι) :
    (coordinateAffineOpenCover R ι).openCover.f i = chartAwayι R i :=
  rfl

/-- The coordinate ring `ChartRing R (coordinateTuple R I.down)` of the Grassmannian chart at
the coordinate tuple `I`. -/
abbrev grassmannianChartRing (I : ULift.{u} (Fin 1 → Fin m)) : Type u :=
  ChartRing R (coordinateTuple R I.down)

/-- Composition of `Spec` of ring maps. -/
private theorem specMap_comp_specMap {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (g : A →+* B) (f : C →+* A) :
    Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) =
      Spec.map (CommRingCat.ofHom (g.comp f)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

/-- Two algebra maps out of chart rings with the same chart point give the same map into the
Grassmannian. -/
theorem specMap_comp_ι_eq {I J : ULift.{u} (Fin 1 → Fin m)} {B : Type u} [CommRing B]
    [Algebra R B] (φ : grassmannianChartRing R I →ₐ[R] B) (φ' : grassmannianChartRing R J →ₐ[R] B)
    (h : ofChartSection (algHomToChartSection B _ φ) (algHomToChartSection_mem _ φ) =
      ofChartSection (algHomToChartSection B _ φ') (algHomToChartSection_mem _ φ')) :
    Spec.map (CommRingCat.ofHom (φ : grassmannianChartRing R I →+* B)) ≫
        (Grassmannian.glueData R 1 m).ι I =
      Spec.map (CommRingCat.ofHom (φ' : grassmannianChartRing R J →+* B)) ≫
        (Grassmannian.glueData R 1 m).ι J :=
  congrArg CommaMorphism.left ((Grassmannian.algSpec_comp_chartι_eq_iff I J
    (B := CommAlgCat.of R B) (CommAlgCat.ofHom φ) (CommAlgCat.ofHom φ')).mpr h)

/-- An algebra map between chart rings preserving the chart point is compatible with the chart
inclusions. -/
theorem specMap_comp_ι_eq_ι {I J : ULift.{u} (Fin 1 → Fin m)}
    (φ : grassmannianChartRing R I →ₐ[R] grassmannianChartRing R J)
    (h : ofChartSection (algHomToChartSection _ _ φ) (algHomToChartSection_mem _ φ) =
      ofChartSection (algHomToChartSection _ _ (AlgHom.id R (grassmannianChartRing R J)))
        (algHomToChartSection_mem _ _)) :
    Spec.map (CommRingCat.ofHom (φ : grassmannianChartRing R I →+* grassmannianChartRing R J)) ≫
        (Grassmannian.glueData R 1 m).ι I = (Grassmannian.glueData R 1 m).ι J :=
  (specMap_comp_ι_eq R φ (AlgHom.id R _) h).trans
    ((congrArg (· ≫ (Grassmannian.glueData R 1 m).ι J) (Spec.map_id _)).trans
      (Category.id_comp _))

/-! ### The map from projective space -/

/-- The algebra map from the Grassmannian chart at `e_{e i}` to the standard chart ring. -/
abbrev chartHom (i : ι) : Grassmannian.chartAlg R (chartIndex e i) ⟶ coordinateAlg R i :=
  CommAlgCat.ofHom (chartToCoordinate R e (chartIndex e i).down i rfl)

/-- The standard chart `D₊(Xᵢ)` maps to the Grassmannian chart at `e_{e i}`. -/
def toGrassmannianChart (i : ι) :
    Grassmannian.affineOver (coordinateAlg R i) ⟶ Grassmannian.schemeOver R 1 m :=
  (algSpec R).map (chartHom R e i).op ≫ Grassmannian.chartι (chartIndex e i)

theorem toGrassmannianChart_left (i : ι) :
    (toGrassmannianChart R e i).left =
      Spec.map (CommRingCat.ofHom (chartToCoordinate R e (chartIndex e i).down i rfl :
        grassmannianChartRing R (chartIndex e i) →+* coordinateRing R ι i)) ≫
        (Grassmannian.glueData R 1 m).ι (chartIndex e i) :=
  rfl

theorem toGrassmannian_glue (i l : ι) :
    pullback.fst ((coordinateAffineOpenCover R ι).openCover.f i)
        ((coordinateAffineOpenCover R ι).openCover.f l) ≫ (toGrassmannianChart R e i).left =
      pullback.snd ((coordinateAffineOpenCover R ι).openCover.f i)
        ((coordinateAffineOpenCover R ι).openCover.f l) ≫ (toGrassmannianChart R e l).left := by
  rw [coordinateCover_f, coordinateCover_f, ← cancel_epi (Proj.pullbackAwayιIso
    (homogeneousSubmodule ι R) (isHomogeneous_X R i) Nat.zero_lt_one (isHomogeneous_X R l)
    Nat.zero_lt_one rfl).inv, Proj.pullbackAwayιIso_inv_fst_assoc,
    Proj.pullbackAwayιIso_inv_snd_assoc, toGrassmannianChart_left, toGrassmannianChart_left,
    ← Category.assoc, ← Category.assoc, specMap_comp_specMap, specMap_comp_specMap]
  exact specMap_comp_ι_eq R (chartToOverlap R e i l (chartIndex e i).down rfl)
    ((overlapRight R i l).comp (chartToCoordinate R e (chartIndex e l).down l rfl))
    (ofChartSection_overlap R e i l _ _ rfl rfl)

/-- The map from projective space to the Grassmannian of rank-one quotients, glued from the
standard charts. -/
def toGrassmannian : ProjectiveSpace R ι ⟶ Grassmannian.scheme R 1 m :=
  (coordinateAffineOpenCover R ι).openCover.glueMorphisms
    (fun i ↦ (toGrassmannianChart R e i).left) (toGrassmannian_glue R e)

theorem chartAwayι_toGrassmannian (i : ι) :
    chartAwayι R i ≫ toGrassmannian R e = (toGrassmannianChart R e i).left :=
  Scheme.Cover.ι_glueMorphisms (coordinateAffineOpenCover R ι).openCover _ _ i

theorem chartAwayι_toGrassmannian_assoc (i : ι) {Z : Scheme.{u}}
    (h : Grassmannian.scheme R 1 m ⟶ Z) :
    chartAwayι R i ≫ toGrassmannian R e ≫ h = (toGrassmannianChart R e i).left ≫ h := by
  rw [← Category.assoc, chartAwayι_toGrassmannian]

/-! ### The map to projective space -/

/-- The Grassmannian chart `I` maps to the standard chart `D₊(Xᵢ)`, `i = e⁻¹ (I 0)`. -/
def ofGrassmannianChart (I : ULift.{u} (Fin 1 → Fin m)) :
    (Grassmannian.chartScheme R (coordinateTuple R I.down)).left ⟶ ProjectiveSpace R ι :=
  Spec.map (CommRingCat.ofHom (coordinateToChart R e I.down (chartCoord e I) :
    coordinateRing R ι (chartCoord e I) →+* grassmannianChartRing R I)) ≫
      chartAwayι R (chartCoord e I)

/-- The overlap of the Grassmannian charts `I`, `J` is the spectrum of `B_{il}`. -/
abbrev overlapSpecMap (I J : ULift.{u} (Fin 1 → Fin m)) :
    Spec (CommRingCat.of (coordinateOverlapRing R ι (chartCoord e I) (chartCoord e J))) ⟶
      (Grassmannian.chartOverlapScheme R (coordinateTuple R I.down)
        (coordinateTuple R J.down)).left :=
  Spec.map (CommRingCat.ofHom (overlapChartEquiv R e (chartCoord e I) (chartCoord e J) I.down
    J.down (chartCoord_spec e I) (chartCoord_spec e J)).toRingHom)

instance (I J : ULift.{u} (Fin 1 → Fin m)) : IsIso (overlapSpecMap R e I J) := by
  have : IsIso (CommRingCat.ofHom (overlapChartEquiv R e (chartCoord e I) (chartCoord e J) I.down
      J.down (chartCoord_spec e I) (chartCoord_spec e J)).toRingHom) :=
    (overlapChartEquiv R e _ _ _ _ (chartCoord_spec e I)
      (chartCoord_spec e J)).toCommRingCatIso.isIso_hom
  exact inferInstance

theorem overlapSpecMap_f (I J : ULift.{u} (Fin 1 → Fin m)) :
    overlapSpecMap R e I J ≫ (Grassmannian.chartOverlapToChart R (coordinateTuple R I.down)
        (coordinateTuple R J.down)).left =
      Spec.map (CommRingCat.ofHom (chartToOverlap R e (chartCoord e I) (chartCoord e J) I.down
        (chartCoord_spec e I) : grassmannianChartRing R I →+*
          coordinateOverlapRing R ι (chartCoord e I) (chartCoord e J))) := by
  have hring : (overlapChartEquiv R e (chartCoord e I) (chartCoord e J) I.down J.down
      (chartCoord_spec e I) (chartCoord_spec e J)).toRingHom.comp
        (algebraMap (grassmannianChartRing R I) (Localization.Away (chartTransitionDet
          (coordinateTuple R I.down) (coordinateTuple R J.down)))) =
      (chartToOverlap R e (chartCoord e I) (chartCoord e J) I.down (chartCoord_spec e I) :
        grassmannianChartRing R I →+*
          coordinateOverlapRing R ι (chartCoord e I) (chartCoord e J)) :=
    RingHom.ext fun z ↦ overlapChartToCoordinate_algebraMap R e _ _ _ _ (chartCoord_spec e I)
      (chartCoord_spec e J) z
  exact (specMap_comp_specMap _ _).trans
    (congrArg (fun φ ↦ Spec.map (CommRingCat.ofHom φ)) hring)

theorem overlapSpecMap_t_f (I J : ULift.{u} (Fin 1 → Fin m)) :
    overlapSpecMap R e I J ≫ (Grassmannian.chartOverlapIso R (coordinateTuple R I.down)
        (coordinateTuple R J.down)).hom.left ≫
        (Grassmannian.chartOverlapToChart R (coordinateTuple R J.down)
          (coordinateTuple R I.down)).left =
      Spec.map (CommRingCat.ofHom ((overlapRight R (chartCoord e I) (chartCoord e J)).comp
        (chartToCoordinate R e J.down (chartCoord e J) (chartCoord_spec e J)) :
          grassmannianChartRing R J →+*
            coordinateOverlapRing R ι (chartCoord e I) (chartCoord e J))) := by
  have hg : (Grassmannian.chartOverlapIso R (coordinateTuple R I.down)
      (coordinateTuple R J.down)).hom.left ≫ (Grassmannian.chartOverlapToChart R
        (coordinateTuple R J.down) (coordinateTuple R I.down)).left ≫
          (Grassmannian.glueData R 1 m).ι J =
      (Grassmannian.chartOverlapToChart R (coordinateTuple R I.down)
        (coordinateTuple R J.down)).left ≫ (Grassmannian.glueData R 1 m).ι I :=
    (Grassmannian.glueData R 1 m).glue_condition I J
  rw [← cancel_mono ((Grassmannian.glueData R 1 m).ι J)]
  simp only [Category.assoc]
  rw [hg, ← Category.assoc, overlapSpecMap_f]
  exact specMap_comp_ι_eq R _ _ (ofChartSection_overlap R e _ _ I.down J.down
    (chartCoord_spec e I) (chartCoord_spec e J))

theorem ofGrassmannian_glue (I J : ULift.{u} (Fin 1 → Fin m)) :
    (Grassmannian.chartOverlapToChart R (coordinateTuple R I.down)
        (coordinateTuple R J.down)).left ≫ ofGrassmannianChart R e I =
      ((Grassmannian.chartOverlapIso R (coordinateTuple R I.down)
        (coordinateTuple R J.down)).hom.left ≫ (Grassmannian.chartOverlapToChart R
          (coordinateTuple R J.down) (coordinateTuple R I.down)).left) ≫
        ofGrassmannianChart R e J := by
  rw [← cancel_epi (overlapSpecMap R e I J)]
  simp only [Category.assoc]
  rw [reassoc_of% overlapSpecMap_f, reassoc_of% overlapSpecMap_t_f, ofGrassmannianChart,
    ofGrassmannianChart, ← Category.assoc, ← Category.assoc, specMap_comp_specMap,
    specMap_comp_specMap]
  have h1 : (chartToOverlap R e (chartCoord e I) (chartCoord e J) I.down
      (chartCoord_spec e I) : grassmannianChartRing R I →+*
        coordinateOverlapRing R ι (chartCoord e I) (chartCoord e J)).comp
        (coordinateToChart R e I.down (chartCoord e I) :
          coordinateRing R ι (chartCoord e I) →+* grassmannianChartRing R I) =
        awayMap (homogeneousSubmodule ι R) (isHomogeneous_X R (chartCoord e J)) rfl := by
    refine RingHom.ext fun y ↦ ?_
    change overlapLeft R _ _ (chartToCoordinate R e _ _ (chartCoord_spec e I)
      (coordinateToChart R e _ _ y)) = _
    rw [chartToCoordinate_coordinateToChart]
    rfl
  have h2 : ((overlapRight R (chartCoord e I) (chartCoord e J)).comp
      (chartToCoordinate R e J.down (chartCoord e J) (chartCoord_spec e J)) :
        grassmannianChartRing R J →+*
          coordinateOverlapRing R ι (chartCoord e I) (chartCoord e J)).comp
        (coordinateToChart R e J.down (chartCoord e J) :
          coordinateRing R ι (chartCoord e J) →+* grassmannianChartRing R J) =
        awayMap (homogeneousSubmodule ι R) (isHomogeneous_X R (chartCoord e I))
          (mul_comm (X (chartCoord e I)) (X (chartCoord e J))) := by
    refine RingHom.ext fun y ↦ ?_
    change overlapRight R _ _ (chartToCoordinate R e _ _ (chartCoord_spec e J)
      (coordinateToChart R e _ _ y)) = _
    rw [chartToCoordinate_coordinateToChart]
    rfl
  rw [h1, h2]
  exact (Proj.SpecMap_awayMap_awayι _ _ _ _ _).trans (Proj.SpecMap_awayMap_awayι _ _ _ _ _).symm

/-- The map from the Grassmannian of rank-one quotients to projective space, glued from the
Grassmannian charts. -/
def ofGrassmannian : Grassmannian.scheme R 1 m ⟶ ProjectiveSpace R ι :=
  Multicoequalizer.desc _ _ (fun I ↦ ofGrassmannianChart R e I) (by
    rintro ⟨I, J⟩
    exact ofGrassmannian_glue R e I J)

theorem ι_ofGrassmannian (I : ULift.{u} (Fin 1 → Fin m)) :
    (Grassmannian.glueData R 1 m).ι I ≫ ofGrassmannian R e = ofGrassmannianChart R e I :=
  Multicoequalizer.π_desc _ _ _ _ _

theorem ι_ofGrassmannian_assoc (I : ULift.{u} (Fin 1 → Fin m)) {Z : Scheme.{u}}
    (h : ProjectiveSpace R ι ⟶ Z) :
    (Grassmannian.glueData R 1 m).ι I ≫ ofGrassmannian R e ≫ h =
      ofGrassmannianChart R e I ≫ h := by
  rw [← Category.assoc, ι_ofGrassmannian]

/-! ### The two composites -/

/-- A map between standard chart rings with equal indices which fixes the ratios is the identity
on the chart. -/
theorem specMap_comp_chartAwayι_of_eq {j i : ι} (h : j = i)
    (ρ : coordinateRing R ι j →ₐ[R] coordinateRing R ι i)
    (hρ : ∀ k, ρ (coordinateRatio R ι j k) = coordinateRatio R ι i k) :
    Spec.map (CommRingCat.ofHom (ρ : coordinateRing R ι j →+* coordinateRing R ι i)) ≫
      chartAwayι R j = chartAwayι R i := by
  subst h
  have hid : ρ = AlgHom.id R _ := coordinateRing_algHom_ext R fun k ↦ hρ k
  subst hid
  exact (congrArg (· ≫ chartAwayι R j) (Spec.map_id _)).trans (Category.id_comp _)

theorem toGrassmannian_ofGrassmannian :
    toGrassmannian R e ≫ ofGrassmannian R e = 𝟙 (ProjectiveSpace R ι) := by
  refine Scheme.Cover.hom_ext (coordinateAffineOpenCover R ι).openCover _ _ fun (i : ι) ↦ ?_
  rw [coordinateCover_f, chartAwayι_toGrassmannian_assoc, toGrassmannianChart_left,
    Category.assoc, ι_ofGrassmannian, ofGrassmannianChart, ← Category.assoc,
    specMap_comp_specMap, Category.comp_id]
  exact specMap_comp_chartAwayι_of_eq R (e.symm_apply_apply i)
    ((chartToCoordinate R e (chartIndex e i).down i rfl).comp
      (coordinateToChart R e (chartIndex e i).down (chartCoord e (chartIndex e i))))
    fun k ↦ by
      rw [AlgHom.comp_apply, coordinateToChart_ratio R e _ _ (chartCoord_spec e _),
        chartToCoordinate_coordinate, Equiv.symm_apply_apply]

theorem ofGrassmannian_toGrassmannian :
    ofGrassmannian R e ≫ toGrassmannian R e = 𝟙 (Grassmannian.scheme R 1 m) := by
  refine Scheme.Cover.hom_ext (Grassmannian.glueData R 1 m).openCover _ _
    fun (I : ULift.{u} (Fin 1 → Fin m)) ↦ ?_
  change (Grassmannian.glueData R 1 m).ι I ≫ _ = (Grassmannian.glueData R 1 m).ι I ≫ _
  rw [ι_ofGrassmannian_assoc, ofGrassmannianChart, Category.assoc, chartAwayι_toGrassmannian,
    toGrassmannianChart_left, ← Category.assoc, specMap_comp_specMap, Category.comp_id]
  refine specMap_comp_ι_eq_ι R ((coordinateToChart R e I.down (chartCoord e I)).comp
    (chartToCoordinate R e (chartIndex e (chartCoord e I)).down (chartCoord e I) rfl)) ?_
  refine Module.Grassmannian.ofChartSection_eq_of_smul _ _ 1 isUnit_one fun v ↦ ?_
  rw [one_smul]
  refine funext fun a ↦ ?_
  have ha : a = 0 := Subsingleton.elim _ _
  subst ha
  simp only [Module.Grassmannian.algHomToChartSection_apply, AlgHom.comp_apply,
    chartToCoordinate_coordinate,
    coordinateToChart_ratio R e I.down (chartCoord e I) (chartCoord_spec e I),
    Equiv.apply_symm_apply, AlgHom.id_apply]

/-- **Projective space is the Grassmannian of rank-one quotients**: the glued Grassmannian
`Gr(R^m, 1)` is isomorphic to `ProjectiveSpace R ι` for every labeling `e : ι ≃ Fin m`.

Source: Stacks, Tag 089V (Lemma 27.22.3), `G(n, n + 1) ≅ P^n_ℤ` (fetched 2026-10-19). Encoded
subset: any base ring `R` (Stacks works over `ℤ`); Stacks' `G(m - 1, m)`, the Grassmannian of
rank-one quotients of `O^m`, is Aglib's `Gr(R^m, 1)` (Mathlib's index is the quotient rank);
every `m` (Stacks assumes `n ≥ 1`). The proof glues the charts directly and does not use the
description of maps into projective space by invertible quotients (Stacks, Tag 01NE). -/
def grassmannianIso : Grassmannian.scheme R 1 m ≅ ProjectiveSpace R ι where
  hom := ofGrassmannian R e
  inv := toGrassmannian R e
  hom_inv_id := ofGrassmannian_toGrassmannian R e
  inv_hom_id := toGrassmannian_ofGrassmannian R e

theorem toGrassmannian_toBase :
    toGrassmannian R e ≫ Grassmannian.toBase R 1 m = toSpec R ι := by
  refine Scheme.Cover.hom_ext (coordinateAffineOpenCover R ι).openCover _ _ fun (i : ι) ↦ ?_
  rw [coordinateCover_f, chartAwayι_toGrassmannian_assoc, toGrassmannianChart_left,
    Category.assoc, Grassmannian.ι_toBase, chartAwayι, coordinateChart_toSpec]
  exact Over.w ((algSpec R).map (chartHom R e i).op)

theorem ofGrassmannian_toSpec :
    ofGrassmannian R e ≫ toSpec R ι = Grassmannian.toBase R 1 m := by
  rw [← toGrassmannian_toBase R e, ← Category.assoc, ofGrassmannian_toGrassmannian,
    Category.id_comp]

/-- **Projective space is the Grassmannian of rank-one quotients, over `Spec R`**: `grassmannianIso`
is compatible with the structure morphisms to `Spec R`. Source and encoded subset: Stacks,
Tag 089V (Lemma 27.22.3), as for `grassmannianIso`. -/
def grassmannianOverIso : Grassmannian.schemeOver R 1 m ≅ schemeOver R ι :=
  Over.isoMk (grassmannianIso R e) (ofGrassmannian_toSpec R e)

theorem grassmannianOverIso_hom_left :
    (grassmannianOverIso R e).hom.left = ofGrassmannian R e := rfl

theorem grassmannianOverIso_inv_left :
    (grassmannianOverIso R e).inv.left = toGrassmannian R e := rfl

end AlgebraicGeometry.ProjectiveSpace
