/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Grassmannian.Chart
public import Aglib.RingTheory.Grassmannian.ChartIntersection

/-!
# Overlaps of the affine charts of the Grassmannian over `Spec R`

For tuples `x y : Fin k → (Fin n → R)`, the overlap scheme `chartOverlapScheme R x y` is the
spectrum of the localization of `ChartRing R x` away from the transition determinant `P^x_y`.
It represents the intersection of the two chart functors on all schemes over `Spec R`, its map
to the chart at `x` is an open immersion onto the basic open set `D(P^x_y)`, and the transition
isomorphism `chartOverlapIso R x y` identifies it with the overlap computed from the chart at `y`.
These are the open sets `U^I_J` and the transition maps `θ_{I,J}` of Nitsure,
arXiv:math/0504590v1, §1, "Construction of Grassmannian", p. 8, over `Spec R`.

## Main definitions and results

- `AlgebraicGeometry.Grassmannian.chartOverlapScheme`, `chartOverlapToChart`, with
  `isOpenImmersion_chartOverlapToChart_left` and `isIso_chartOverlapToChart_self_left`.
- `AlgebraicGeometry.Grassmannian.chartOverlapRepresentableBy`: the overlap represents
  `(algΓ R).leftOp ⋙ (chartFunctor R x ⊓ chartFunctor R y).toFunctor`;
  `chartRepresentableBy_homEquiv_comp_chartOverlapToChart`: the inclusion into the chart at `x`
  does not change the classified point.
- `AlgebraicGeometry.Grassmannian.chartOverlapIso`: the transition isomorphism over `Spec R`;
  `chartOverlapRepresentableBy_homEquiv_comp_chartOverlapIso`: it does not change the classified
  point.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Grassmannian

variable (R : CommRingCat.{u}) {k n : ℕ}

/-- The overlap of the charts at `x` and `y`, as the basic open set `D(P^x_y)` of the chart at
`x`. -/
abbrev chartOverlapScheme (x y : Fin k → Fin n → R) : Over (Spec R) :=
  (algSpec R).obj (op (CommAlgCat.of R
    (Localization.Away (Module.Grassmannian.chartTransitionDet x y))))

/-- The inclusion of the overlap into the chart at `x`. -/
def chartOverlapToChart (x y : Fin k → Fin n → R) : chartOverlapScheme R x y ⟶ chartScheme R x :=
  (algSpec R).map (CommAlgCat.ofHom (IsScalarTower.toAlgHom R (Module.Grassmannian.ChartRing R x)
    (Localization.Away (Module.Grassmannian.chartTransitionDet x y)))).op

theorem isOpenImmersion_chartOverlapToChart_left (x y : Fin k → Fin n → R) :
    IsOpenImmersion (chartOverlapToChart R x y).left := by
  have h : (chartOverlapToChart R x y).left = Spec.map (CommRingCat.ofHom
      (algebraMap (Module.Grassmannian.ChartRing R x)
        (Localization.Away (Module.Grassmannian.chartTransitionDet x y)))) := rfl
  rw [h]
  exact IsOpenImmersion.of_isLocalization (Module.Grassmannian.chartTransitionDet x y)

/-- The overlap of a chart with itself is the whole chart. -/
theorem isIso_chartOverlapToChart_self_left (x : Fin k → Fin n → R) :
    IsIso (chartOverlapToChart R x x).left := by
  have h : (chartOverlapToChart R x x).left = Spec.map (CommRingCat.ofHom
      (algebraMap (Module.Grassmannian.ChartRing R x)
        (Localization.Away (Module.Grassmannian.chartTransitionDet x x)))) := rfl
  have hb : Function.Bijective (algebraMap (Module.Grassmannian.ChartRing R x)
      (Localization.Away (Module.Grassmannian.chartTransitionDet x x))) :=
    (IsLocalization.atUnits (Module.Grassmannian.ChartRing R x)
      (Submonoid.powers (Module.Grassmannian.chartTransitionDet x x))
      (S := Localization.Away (Module.Grassmannian.chartTransitionDet x x))
      (Submonoid.powers_le.mpr (Module.Grassmannian.isUnit_chartTransitionDet_self x))).bijective
  have : IsIso (CommRingCat.ofHom (algebraMap (Module.Grassmannian.ChartRing R x)
      (Localization.Away (Module.Grassmannian.chartTransitionDet x x)))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hb
  have hS : IsIso (Scheme.Spec.map (CommRingCat.ofHom (algebraMap
      (Module.Grassmannian.ChartRing R x)
      (Localization.Away (Module.Grassmannian.chartTransitionDet x x)))).op) := inferInstance
  rw [h]
  exact hS

/-- The overlap scheme represents the intersection of the two chart functors on all schemes over
`Spec R`. -/
def chartOverlapRepresentableBy [Module.Grassmannian.BaseChangeMkQFormula.{u, u, u} R (Fin n → R)]
    (x y : Fin k → Fin n → R) :
    ((algΓ R).leftOp ⋙
      (Module.Grassmannian.chartFunctor.{u, u, u} R x ⊓
        Module.Grassmannian.chartFunctor R y).toFunctor).RepresentableBy
      (chartOverlapScheme R x y) where
  homEquiv {T} :=
    ((algΓAlgSpecAdjunction R).homEquiv T _).symm.trans <|
      (opEquiv _ _).trans (Module.Grassmannian.chartInterCorepresentableBy R x y).homEquiv
  homEquiv_comp {T T'} f g := by
    change (Module.Grassmannian.chartInterCorepresentableBy R x y).homEquiv
        (((algΓAlgSpecAdjunction R).homEquiv T _).symm (f ≫ g)).unop = _
    rw [Adjunction.homEquiv_naturality_left_symm, unop_comp,
      Functor.CorepresentableBy.homEquiv_comp]
    rfl

/-- A map into the overlap and its composite with the inclusion into the chart at `x` classify
the same point of the Grassmannian. -/
theorem chartRepresentableBy_homEquiv_comp_chartOverlapToChart
    [Module.Grassmannian.BaseChangeMkQFormula.{u, u, u} R (Fin n → R)] (x y : Fin k → Fin n → R)
    {T : Over (Spec R)} (g : T ⟶ chartOverlapScheme R x y) :
    ((chartRepresentableBy R x).homEquiv (g ≫ chartOverlapToChart R x y)).1 =
      ((chartOverlapRepresentableBy R x y).homEquiv g).1 := by
  change ((Module.Grassmannian.chartFunctorCorepresentableBy R x).homEquiv
      (((algΓAlgSpecAdjunction R).homEquiv T _).symm
        (g ≫ (algSpec R).map (CommAlgCat.ofHom (IsScalarTower.toAlgHom R
          (Module.Grassmannian.ChartRing R x)
          (Localization.Away (Module.Grassmannian.chartTransitionDet x y)))).op)).unop).1 = _
  rw [Adjunction.homEquiv_naturality_right_symm, unop_comp]
  rfl

/-- The transition isomorphism between the overlap computed from the chart at `x` and the one
computed from the chart at `y` (Nitsure's `θ_{I,J}`). -/
def chartOverlapIso [Module.Grassmannian.BaseChangeMkQFormula.{u, u, u} R (Fin n → R)]
    (x y : Fin k → Fin n → R) :
    chartOverlapScheme R x y ≅ chartOverlapScheme R y x :=
  (algSpec R).mapIso (Module.Grassmannian.chartTransitionIso R x y).symm.op

/-- The transition isomorphism of overlaps does not change the classified point. -/
theorem chartOverlapRepresentableBy_homEquiv_comp_chartOverlapIso
    [Module.Grassmannian.BaseChangeMkQFormula.{u, u, u} R (Fin n → R)] (x y : Fin k → Fin n → R)
    {T : Over (Spec R)} (g : T ⟶ chartOverlapScheme R x y) :
    ((chartOverlapRepresentableBy R y x).homEquiv (g ≫ (chartOverlapIso R x y).hom)).1 =
      ((chartOverlapRepresentableBy R x y).homEquiv g).1 := by
  change ((Module.Grassmannian.chartInterCorepresentableBy R y x).homEquiv
      (((algΓAlgSpecAdjunction R).homEquiv T _).symm
        (g ≫ (algSpec R).map (Module.Grassmannian.chartTransitionIso R x y).inv.op)).unop).1 =
    ((Module.Grassmannian.chartInterCorepresentableBy R x y).homEquiv
      (((algΓAlgSpecAdjunction R).homEquiv T _).symm g).unop).1
  rw [Adjunction.homEquiv_naturality_right_symm, unop_comp, Quiver.Hom.unop_op]
  rw [← Module.Grassmannian.chartInterCorepresentableBy_homEquiv_transitionIso_hom x y,
    Iso.hom_inv_id_assoc]

end AlgebraicGeometry.Grassmannian
