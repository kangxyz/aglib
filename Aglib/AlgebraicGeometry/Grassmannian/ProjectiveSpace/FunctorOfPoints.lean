/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Grassmannian.ProjectiveSpace.Comparison
public import Aglib.AlgebraicGeometry.Grassmannian.FunctorOfPoints

/-!
# The functor of points of projective space

Through the comparison `grassmannianOverIso e : Gr(R^m, 1) ≅ ProjectiveSpace R ι` over `Spec R`
(`e : ι ≃ Fin m`), the functor of points of the Grassmannian
(`Grassmannian.representableEquiv`, `Grassmannian.homEquivNatTrans`) becomes the functor of points
of projective space:

- on affine test schemes, maps `Spec A ⟶ P` over `Spec R` are the points of Mathlib's
  `G(1, A ⊗[R] (Fin m → R); A)`, the submodules of `A^m` whose quotient is finite projective of
  constant rank one, naturally in `A` (`representableEquiv`, `representableIso`);
- on every scheme `T` over `Spec R`, maps `T ⟶ P` are the natural transformations from the affine
  functor of points of `T` to Mathlib's Grassmannian functor (`homEquivNatTrans`), so projective
  space represents `Grassmannian.localFunctor R 1 m` (`localFunctorRepresentableBy`).

The identity of `P` corresponds to the transformation whose value on the standard chart
`D₊(Xᵢ)` is the coordinate quotient `B_i^m → B_i`, `e_j ↦ X_{e⁻¹ j} / X_i`
(`representableEquiv_chartOver`, `homEquivNatTrans_id_app_chartOver`). Transformations out of the
affine functor of points of `P` are determined by their values at the standard charts
(`natTrans_ext_of_chartOver`), so these chart values characterize the identity
(`eq_id_of_representableEquiv_chartOver`). Conversely, the map `Spec A ⟶ P` classifying the
quotient of a chart section factors through the corresponding standard chart
(`representableEquiv_symm_ofChartSection`).

Source: Stacks, Tag 089V (Lemma 27.22.3), through the comparison `grassmannianOverIso`. The
description of maps `T ⟶ P` from a nonaffine `T` by rank-one locally free quotients of `O_T^m`
(Stacks, Tags 089V and 01NE, Lemma 27.13.1) needs the corresponding sheaf-level description of the
Grassmannian (Stacks, Tag 089T), which is not proved here; this module gives the functor of
points in `Grassmannian.localFunctor` form.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite Limits MvPolynomial HomogeneousLocalization
open scoped Module.Grassmannian TensorProduct

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveSpace

variable (R : CommRingCat.{u}) {ι : Type u} {m : ℕ} (e : ι ≃ Fin m)

set_option hygiene false in
/-- Mathlib's Grassmannian functor of rank-one quotients of `R^m` on `R`-algebras. -/
local notation "𝐆" => Module.Grassmannian.functor.{u, u, u} (R := R) (M := Fin m → R) 1

/-- Maps into projective space are maps into the Grassmannian of rank-one quotients. -/
def homEquivGrassmannian (T : Over (Spec R)) :
    (T ⟶ schemeOver R ι) ≃ (T ⟶ Grassmannian.schemeOver R 1 m) where
  toFun g := g ≫ (grassmannianOverIso R e).inv
  invFun g := g ≫ (grassmannianOverIso R e).hom
  left_inv g := by simp
  right_inv g := by simp

theorem homEquivGrassmannian_comp {T' T : Over (Spec R)} (t : T' ⟶ T) (g : T ⟶ schemeOver R ι) :
    homEquivGrassmannian R e T' (t ≫ g) = t ≫ homEquivGrassmannian R e T g :=
  show (t ≫ g) ≫ (grassmannianOverIso R e).inv = t ≫ g ≫ (grassmannianOverIso R e).inv from
    Category.assoc _ _ _

/-- **Maps from any scheme over `Spec R` into projective space** are the natural transformations
from its functor of points on `R`-algebras to Mathlib's Grassmannian functor of rank-one
quotients of `R^m`.

Source: Stacks, Tag 089V (Lemma 27.22.3), through `grassmannianOverIso`, and
`Grassmannian.homEquivNatTrans`. -/
def homEquivNatTrans (T : Over (Spec R)) : (T ⟶ schemeOver R ι) ≃ (algSpecPoints T ⟶ 𝐆) :=
  (homEquivGrassmannian R e T).trans (Grassmannian.homEquivNatTrans 1 m T)

/-- Naturality of `homEquivNatTrans` in the test scheme. -/
theorem homEquivNatTrans_comp {T' T : Over (Spec R)} (t : T' ⟶ T) (g : T ⟶ schemeOver R ι) :
    homEquivNatTrans R e T' (t ≫ g) =
      Functor.whiskerLeft (algSpec R).rightOp (yoneda.map t) ≫ homEquivNatTrans R e T g := by
  rw [homEquivNatTrans, Equiv.trans_apply, homEquivGrassmannian_comp,
    Grassmannian.homEquivNatTrans_comp]
  rfl

/-- **Projective space represents the extension of Mathlib's Grassmannian functor of rank-one
quotients to all schemes over `Spec R`.** -/
def localFunctorRepresentableBy :
    (Grassmannian.localFunctor R 1 m).RepresentableBy (schemeOver R ι) where
  homEquiv {T} :=
    (homEquivGrassmannian R e T).trans (Grassmannian.localFunctorRepresentableBy R 1 m).homEquiv
  homEquiv_comp {T T'} f g := by
    simp only [Equiv.trans_apply, homEquivGrassmannian_comp]
    exact (Grassmannian.localFunctorRepresentableBy R 1 m).homEquiv_comp f _

/-- **Representability on affine test schemes**: maps `Spec A ⟶ P` over `Spec R` are the points
of `G(1, A ⊗[R] (Fin m → R); A)`, the submodules of `A ⊗[R] R^m` whose quotient is finite
projective of constant rank one.

Source: Stacks, Tag 089V (Lemma 27.22.3), through `grassmannianOverIso`, and
`Grassmannian.representableEquiv` (Nitsure, arXiv:math/0504590v1, §1, pp. 7–8; Stacks,
Tag 089T). -/
def representableEquiv (A : CommAlgCat.{u} R) :
    (Grassmannian.affineOver A ⟶ schemeOver R ι) ≃ G(1, A ⊗[R] (Fin m → R); A) :=
  (homEquivGrassmannian R e _).trans (Grassmannian.representableEquiv R 1 m A)

/-- Naturality of `representableEquiv`: precomposition with `Spec h` is base change along `h`. -/
theorem representableEquiv_comp {A B : CommAlgCat.{u} R} (h : A ⟶ B)
    (g : Grassmannian.affineOver A ⟶ schemeOver R ι) :
    representableEquiv R e B ((algSpec R).map h.op ≫ g) =
      Module.Grassmannian.map h.hom (representableEquiv R e A g) := by
  simp only [representableEquiv, Equiv.trans_apply, homEquivGrassmannian_comp]
  exact Grassmannian.homPoint_comp _ h

/-- **Projective space represents Mathlib's Grassmannian functor of rank-one quotients** on
`R`-algebras. -/
def representableIso : (algSpec R).rightOp ⋙ yoneda.obj (schemeOver R ι) ≅ 𝐆 :=
  NatIso.ofComponents (fun A ↦ (representableEquiv R e A).toIso) fun {A B} h ↦ by
    ext g
    exact representableEquiv_comp R e h g

/-- The transformation attached to `g : T ⟶ P` sends `v : Spec B ⟶ T` to the point of
`v ≫ g`. -/
theorem homEquivNatTrans_app (T : Over (Spec R)) (g : T ⟶ schemeOver R ι) (B : CommAlgCat.{u} R)
    (v : Grassmannian.affineOver B ⟶ T) :
    (homEquivNatTrans R e T g).app B v = representableEquiv R e B (v ≫ g) := by
  change Grassmannian.homPoint (v ≫ g ≫ (grassmannianOverIso R e).inv) =
    Grassmannian.homPoint ((v ≫ g) ≫ (grassmannianOverIso R e).inv)
  rw [Category.assoc]

/-! ### The universal point on the standard charts -/

/-- The point classified by an algebra map out of a chart ring is the chart section point. -/
theorem chartPt_eq (I : ULift.{u} (Fin 1 → Fin m)) {B : CommAlgCat.{u} R}
    (ψ : Grassmannian.chartAlg R I ⟶ B) :
    Grassmannian.chartPt I ψ =
      Module.Grassmannian.ofChartSection (Module.Grassmannian.algHomToChartSection _ _ ψ.hom)
        (Module.Grassmannian.algHomToChartSection_mem _ ψ.hom) :=
  rfl

/-- The standard chart `D₊(Xᵢ)` as a map of schemes over `Spec R`. -/
def chartOver (i : ι) : Grassmannian.affineOver (coordinateAlg R i) ⟶ schemeOver R ι :=
  Over.homMk (chartAwayι R i) (coordinateChart_toSpec R ι i)

theorem chartOver_left (i : ι) : (chartOver R i).left = chartAwayι R i := rfl

theorem chartOver_comp_inv (i : ι) :
    chartOver R i ≫ (grassmannianOverIso R e).inv = toGrassmannianChart R e i :=
  Over.OverMorphism.ext (chartAwayι_toGrassmannian R e i)

/-- **The point classified by a standard chart.** Under the comparison, the inclusion of the
standard chart `D₊(Xᵢ) = Spec B_i` into `P` classifies the rank-one quotient of `B_i ⊗[R] R^m`
cut out by the chart section `v ↦ Σ_j v_j X_{e⁻¹ j} / X_i`, the kernel of
`B_i ⊗[R] R^m → B_i`, `b ⊗ e_j ↦ b X_{e⁻¹ j} / X_i`. -/
theorem representableEquiv_chartOver (i : ι) :
    representableEquiv R e (coordinateAlg R i) (chartOver R i) =
      Module.Grassmannian.ofChartSection (chartRatioSection R e i)
        (chartRatioSection_mem R e (chartIndex e i).down i rfl) := by
  change Grassmannian.homPoint (chartOver R i ≫ (grassmannianOverIso R e).inv) = _
  rw [chartOver_comp_inv]
  have h := Grassmannian.map_homPoint_of_factor (toGrassmannianChart R e i)
    (f := 𝟙 (coordinateAlg R i)) (I := chartIndex e i) (ψ := chartHom R e i) (by
      rw [op_id, CategoryTheory.Functor.map_id, Category.id_comp]
      rfl)
  rw [CategoryTheory.Functor.map_id] at h
  have h' : Grassmannian.homPoint (toGrassmannianChart R e i) =
      Grassmannian.chartPt (chartIndex e i) (chartHom R e i) := h
  rw [h', chartPt_eq]
  exact Module.Grassmannian.ofChartSection_eq_of_smul _ _ 1 isUnit_one fun v ↦ by
    rw [one_smul, CommAlgCat.hom_ofHom, algHomToChartSection_chartToCoordinate]

/-- **The universal point.** The identity of projective space corresponds to the natural
transformation whose value on the standard chart `D₊(Xᵢ)` is the coordinate quotient
`b ⊗ e_j ↦ b X_{e⁻¹ j} / X_i` of `B_i ⊗[R] R^m`. -/
theorem homEquivNatTrans_id_app_chartOver (i : ι) :
    (homEquivNatTrans R e (schemeOver R ι) (𝟙 _)).app (coordinateAlg R i) (chartOver R i) =
      Module.Grassmannian.ofChartSection (chartRatioSection R e i)
        (chartRatioSection_mem R e (chartIndex e i).down i rfl) := by
  rw [homEquivNatTrans_app, Category.comp_id, representableEquiv_chartOver]

instance (i : ι) : IsOpenImmersion (chartOver R i).left :=
  inferInstanceAs (IsOpenImmersion (chartAwayι R i))

/-- Natural transformations from the affine functor of points of projective space to Mathlib's
Grassmannian functor are determined by their values at the standard charts: near every prime, an
affine point factors through a standard chart, and points of the Grassmannian functor are
determined by their restrictions to a Zariski cover. -/
theorem natTrans_ext_of_chartOver {α β : algSpecPoints (schemeOver R ι) ⟶ 𝐆}
    (h : ∀ i, α.app (coordinateAlg R i) (chartOver R i) =
      β.app (coordinateAlg R i) (chartOver R i)) :
    α = β := by
  ext B v
  have H : ∀ p : PrimeSpectrum B, ∃ (r : B) (_ : r ∉ p.asIdeal),
      Module.Grassmannian.map (IsScalarTower.toAlgHom R B (Localization.Away r)) (α.app B v) =
        Module.Grassmannian.map (IsScalarTower.toAlgHom R B (Localization.Away r))
          (β.app B v) := by
    intro p
    obtain ⟨r, hr, a, ha⟩ := AlgSpecPoints.exists_locAway_comp_eq
      (chartOver R ((coordinateAffineOpenCover R ι).idx (v.left p))) v p
      ((coordinateAffineOpenCover R ι).covers (v.left p))
    refine ⟨r, hr, ?_⟩
    obtain ⟨ψ, rfl⟩ : ∃ ψ : coordinateAlg R ((coordinateAffineOpenCover R ι).idx (v.left p)) ⟶
        CommAlgCat.of R (Localization.Away r), (algSpec R).map ψ.op = a :=
      ⟨((algSpec R).preimage a).unop, by rw [Quiver.Hom.op_unop, Functor.map_preimage]⟩
    change 𝐆.map (Grassmannian.locAway r) (α.app B v) = 𝐆.map (Grassmannian.locAway r) (β.app B v)
    rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply]
    change α.app _ ((algSpec R).map (Grassmannian.locAway r).op ≫ v) =
      β.app _ ((algSpec R).map (Grassmannian.locAway r).op ≫ v)
    rw [ha]
    change α.app _ ((algSpecPoints (schemeOver R ι)).map ψ (chartOver R _)) =
      β.app _ ((algSpecPoints (schemeOver R ι)).map ψ (chartOver R _))
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply]
    exact congrArg _ (h _)
  choose r hr H using H
  exact Module.Grassmannian.eq_of_map_localization_eq r
    (Grassmannian.span_range_eq_top_of_forall_notMem r hr) H

/-- **The identity is characterized by its chart points.** An endomorphism of projective space
over `Spec R` whose composite with each standard chart `D₊(Xᵢ)` classifies the coordinate quotient
`b ⊗ e_j ↦ b X_{e⁻¹ j} / X_i` is the identity. -/
theorem eq_id_of_representableEquiv_chartOver (g : schemeOver R ι ⟶ schemeOver R ι)
    (h : ∀ i, representableEquiv R e (coordinateAlg R i) (chartOver R i ≫ g) =
      Module.Grassmannian.ofChartSection (chartRatioSection R e i)
        (chartRatioSection_mem R e (chartIndex e i).down i rfl)) :
    g = 𝟙 _ := by
  apply (homEquivNatTrans R e _).injective
  refine natTrans_ext_of_chartOver R fun i ↦ ?_
  rw [homEquivNatTrans_app, homEquivNatTrans_app, h, Category.comp_id,
    representableEquiv_chartOver]

/-! ### Maps into projective space from chart sections -/

/-- The map `B_i → A` attached to a chart section `φ : R^m → A` at `e_{e i}` (so `φ e_{e i} = 1`):
`X_k / X_i ↦ φ e_{e k}`. -/
def chartSectionToCoordinate (i : ι) {A : CommAlgCat.{u} R}
    (φ : (Fin m → R) →ₗ[R] (Fin 1 → A))
    (hφ : φ ∈ Module.Grassmannian.chartSections R A
      (Module.Grassmannian.coordinateTuple R (chartIndex e i).down)) :
    coordinateAlg R i ⟶ A :=
  CommAlgCat.ofHom ((Module.Grassmannian.chartSectionToAlgHom φ hφ).comp
    (coordinateToChart R e (chartIndex e i).down i))

theorem chartSectionToCoordinate_ratio (i : ι) {A : CommAlgCat.{u} R}
    (φ : (Fin m → R) →ₗ[R] (Fin 1 → A))
    (hφ : φ ∈ Module.Grassmannian.chartSections R A
      (Module.Grassmannian.coordinateTuple R (chartIndex e i).down)) (k : ι) :
    (chartSectionToCoordinate R e i φ hφ).hom (coordinateRatio R ι i k) =
      φ (Pi.single (e k) 1) 0 := by
  change Module.Grassmannian.chartSectionToAlgHom φ hφ
    (coordinateToChart R e (chartIndex e i).down i (coordinateRatio R ι i k)) = _
  rw [coordinateToChart_ratio R e _ i rfl, Module.Grassmannian.chartSectionToAlgHom_coordinate]

/-- **Maps into projective space from chart sections.** The map `Spec A ⟶ P` classifying the
rank-one quotient of `A ⊗[R] R^m` cut out by a chart section `φ` at `e_{e i}` factors through the
standard chart `D₊(Xᵢ)`, by the algebra map `X_k / X_i ↦ φ e_{e k}`. -/
theorem representableEquiv_symm_ofChartSection (i : ι) {A : CommAlgCat.{u} R}
    (φ : (Fin m → R) →ₗ[R] (Fin 1 → A))
    (hφ : φ ∈ Module.Grassmannian.chartSections R A
      (Module.Grassmannian.coordinateTuple R (chartIndex e i).down)) :
    (representableEquiv R e A).symm (Module.Grassmannian.ofChartSection φ hφ) =
      (algSpec R).map (chartSectionToCoordinate R e i φ hφ).op ≫ chartOver R i := by
  apply (representableEquiv R e A).injective
  rw [Equiv.apply_symm_apply, representableEquiv_comp, representableEquiv_chartOver,
    Module.Grassmannian.map_ofChartSection]
  refine Module.Grassmannian.ofChartSection_eq_of_smul _ _ 1 isUnit_one fun v ↦ ?_
  rw [one_smul]
  refine funext fun a ↦ ?_
  have ha : a = 0 := Subsingleton.elim _ _
  subst ha
  rw [LinearMap.comp_apply, LinearMap.compLeft_apply, Function.comp_apply, AlgHom.toLinearMap_apply,
    chartRatioSection_apply, map_sum, Module.Grassmannian.linearMap_apply_eq_sum_single φ v,
    Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_mul, AlgHom.commutes, chartSectionToCoordinate_ratio, Equiv.apply_symm_apply,
    Pi.smul_apply, Algebra.smul_def]

end AlgebraicGeometry.ProjectiveSpace
