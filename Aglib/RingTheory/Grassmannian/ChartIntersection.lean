/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Grassmannian.ChartRing
public import Aglib.RingTheory.Grassmannian.Overlap
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Intersections of charts of the Grassmannian of a free module

Let `M = Fin n → R` and `x y : Fin k → M`. On the chart at `x`, with coordinates `Φ`, the
universal transition matrix towards `y` has entries `Σ_j y b j • Φ a j`; its determinant is
`chartTransitionDet x y`. A point of the chart at `x` lies in the chart at `y` exactly when this
determinant becomes a unit. Hence the intersection of the two chart functors is corepresented by
the localization of `ChartRing R x` away from `chartTransitionDet x y`: the intersection of the
charts is the basic open subset `D(P^x_y)` of the chart at `x`, as in Nitsure,
arXiv:math/0504590v1, §1, "Construction of Grassmannian", p. 8, where
`U^I_J = Spec Z[X^I, 1/P^I_J]`.

## Main results

- `Module.Grassmannian.chartTransitionDet`: the determinant `P^x_y` on the chart at `x`.
- `Module.Grassmannian.ofChartSection_algHomToChartSection_mem_chart_iff`: the point attached to
  `ψ : ChartRing R x →ₐ[R] A` lies in the chart at `y` if and only if `ψ (P^x_y)` is a unit.
- `Module.Grassmannian.chartInterCorepresentableBy`: `chartFunctor R x ⊓ chartFunctor R y` is
  corepresented by `Localization.Away (chartTransitionDet x y)`.
- `Module.Grassmannian.chartTransitionIso`: the induced isomorphism between the localizations
  of the chart rings at `x` and at `y`;
  `chartInterCorepresentableBy_homEquiv_transitionIso_hom` shows that it is the identity on the
  underlying points.
- `Module.Grassmannian.chartFamilyInterCorepresentableBy`: the intersection of the chart at `x`
  with the charts at a finite family `y` is corepresented by
  `Localization.Away (chartTransitionDetProd x y)`; triple overlaps are the case of two tuples.
-/

@[expose] public section

noncomputable section

universe u w

open CategoryTheory TensorProduct

namespace Module.Grassmannian

variable {R : Type u} [CommRing R] {k n : ℕ}

/-- The universal transition matrix on the chart at `x` towards `y`, with entries
`Σ_j y b j • Φ a j`. -/
def chartTransitionMatrix (x y : Fin k → Fin n → R) : Matrix (Fin k) (Fin k) (ChartRing R x) :=
  Matrix.of fun a b ↦ ∑ j, y b j • chartCoordinate x a j

/-- The transition determinant `P^x_y` on the chart at `x`. -/
def chartTransitionDet (x y : Fin k → Fin n → R) : ChartRing R x :=
  (chartTransitionMatrix x y).det

/-- On the chart at `x`, the transition matrix towards `x` itself is the identity: these are
the chart relations `Φ X = 1`. -/
theorem chartTransitionMatrix_self (x : Fin k → Fin n → R) : chartTransitionMatrix x x = 1 := by
  ext a b
  have h : Ideal.Quotient.mkₐ R (chartIdeal R x) (chartRelation R x a b) = 0 := by
    rw [Ideal.Quotient.mkₐ_eq_mk]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (chartRelation_mem_chartIdeal x a b)
  rw [chartRelation, map_sub, sub_eq_zero, map_sum] at h
  simp only [map_smul] at h
  rw [chartTransitionMatrix, Matrix.of_apply, Matrix.one_apply]
  convert h using 1
  · simp [chartCoordinate, Ideal.Quotient.mkₐ_eq_mk]
  · split_ifs <;> simp

/-- The transition determinant of a chart with itself is a unit, so the overlap of a chart with
itself is the whole chart. -/
theorem isUnit_chartTransitionDet_self (x : Fin k → Fin n → R) :
    IsUnit (chartTransitionDet x x) := by
  rw [chartTransitionDet, chartTransitionMatrix_self, Matrix.det_one]
  exact isUnit_one

variable {A : Type w} [CommRing A] [Algebra R A]

theorem transitionMatrix_algHomToChartSection (x y : Fin k → Fin n → R)
    (ψ : ChartRing R x →ₐ[R] A) :
    transitionMatrix (algHomToChartSection A x ψ) y = ψ.mapMatrix (chartTransitionMatrix x y) := by
  ext a b
  simp [chartTransitionMatrix, map_sum]

/-- The point attached to `ψ : ChartRing R x →ₐ[R] A` lies in the chart at `y` if and only if
`ψ` sends the transition determinant to a unit. -/
theorem ofChartSection_algHomToChartSection_mem_chart_iff (x y : Fin k → Fin n → R)
    (ψ : ChartRing R x →ₐ[R] A) :
    ofChartSection (algHomToChartSection A x ψ) (algHomToChartSection_mem x ψ) ∈
        chart A (baseChangeTuple A y) ↔ IsUnit (ψ (chartTransitionDet x y)) := by
  rw [ofChartSection_mem_chart_iff, transitionMatrix_algHomToChartSection, chartTransitionDet,
    AlgHom.map_det]

theorem ofChartSection_congr {x : Fin k → Fin n → R} {φ φ' : (Fin n → R) →ₗ[R] (Fin k → A)}
    (h : φ = φ') (hφ : φ ∈ chartSections R A x) (hφ' : φ' ∈ chartSections R A x) :
    ofChartSection φ hφ = ofChartSection φ' hφ' := by
  subst h
  rfl

theorem chartSectionToAlgHom_congr {x : Fin k → Fin n → R}
    {φ φ' : (Fin n → R) →ₗ[R] (Fin k → A)} (h : φ = φ') (hφ : φ ∈ chartSections R A x)
    (hφ' : φ' ∈ chartSections R A x) :
    chartSectionToAlgHom φ hφ = chartSectionToAlgHom φ' hφ' := by
  subst h
  rfl

/-- The point of the Grassmannian attached to an algebra map out of the chart ring. -/
def ofChartAlgHom (x : Fin k → Fin n → R) (ψ : ChartRing R x →ₐ[R] A) :
    G(k, A ⊗[R] (Fin n → R); A) :=
  ofChartSection (algHomToChartSection A x ψ) (algHomToChartSection_mem x ψ)

theorem ofChartAlgHom_mem_chart (x : Fin k → Fin n → R) (ψ : ChartRing R x →ₐ[R] A) :
    ofChartAlgHom x ψ ∈ chart A (baseChangeTuple A x) :=
  ofChartSection_mem_chart _ _

/-- The algebra map out of the chart ring attached to a point of the chart. -/
def toChartAlgHom {x : Fin k → Fin n → R} {N : G(k, A ⊗[R] (Fin n → R); A)}
    (hN : N ∈ chart A (baseChangeTuple A x)) : ChartRing R x →ₐ[R] A :=
  chartSectionToAlgHom (toChartSection hN) (toChartSection_mem hN)

theorem ofChartAlgHom_toChartAlgHom {x : Fin k → Fin n → R} {N : G(k, A ⊗[R] (Fin n → R); A)}
    (hN : N ∈ chart A (baseChangeTuple A x)) : ofChartAlgHom x (toChartAlgHom hN) = N := by
  rw [ofChartAlgHom, toChartAlgHom,
    ofChartSection_congr (algHomToChartSection_chartSectionToAlgHom _ _) _ (toChartSection_mem hN),
    ofChartSection_toChartSection]

theorem toChartAlgHom_ofChartAlgHom (x : Fin k → Fin n → R) (ψ : ChartRing R x →ₐ[R] A) :
    toChartAlgHom (ofChartAlgHom_mem_chart x ψ) = ψ := by
  have h : toChartSection (ofChartAlgHom_mem_chart x ψ) = algHomToChartSection A x ψ :=
    toChartSection_ofChartSection _ _
  rw [toChartAlgHom, chartSectionToAlgHom_congr h _ (algHomToChartSection_mem x ψ),
    chartSectionToAlgHom_algHomToChartSection]

theorem isUnit_toChartAlgHom {x y : Fin k → Fin n → R} {N : G(k, A ⊗[R] (Fin n → R); A)}
    (hx : N ∈ chart A (baseChangeTuple A x)) (hy : N ∈ chart A (baseChangeTuple A y)) :
    IsUnit (toChartAlgHom hx (chartTransitionDet x y)) := by
  rw [← ofChartSection_algHomToChartSection_mem_chart_iff]
  change ofChartAlgHom x (toChartAlgHom hx) ∈ _
  rw [ofChartAlgHom_toChartAlgHom]
  exact hy

/-- The algebra map out of the localized chart ring attached to a point of both charts. -/
def interLift {x y : Fin k → Fin n → R} {N : G(k, A ⊗[R] (Fin n → R); A)}
    (hx : N ∈ chart A (baseChangeTuple A x)) (hy : N ∈ chart A (baseChangeTuple A y)) :
    Localization.Away (chartTransitionDet x y) →ₐ[R] A :=
  IsLocalization.liftAlgHom (M := Submonoid.powers (chartTransitionDet x y))
    (f := toChartAlgHom hx) (by
      rintro ⟨_, m, rfl⟩
      simpa using (isUnit_toChartAlgHom hx hy).pow m)

theorem interLift_comp {x y : Fin k → Fin n → R} {N : G(k, A ⊗[R] (Fin n → R); A)}
    (hx : N ∈ chart A (baseChangeTuple A x)) (hy : N ∈ chart A (baseChangeTuple A y)) :
    (interLift hx hy).comp (IsScalarTower.toAlgHom R (ChartRing R x) _) = toChartAlgHom hx := by
  ext c
  simp [interLift, IsLocalization.lift_eq]

theorem interLift_ofChartAlgHom_comp (x y : Fin k → Fin n → R)
    (Φ : Localization.Away (chartTransitionDet x y) →ₐ[R] A)
    (hy : ofChartAlgHom x (Φ.comp (IsScalarTower.toAlgHom R (ChartRing R x) _)) ∈
      chart A (baseChangeTuple A y)) :
    interLift (ofChartAlgHom_mem_chart x _) hy = Φ := by
  apply IsLocalization.algHom_ext (Submonoid.powers (chartTransitionDet x y))
  change (interLift _ hy).comp (IsScalarTower.toAlgHom R (ChartRing R x) _) =
    Φ.comp (IsScalarTower.toAlgHom R (ChartRing R x) _)
  rw [interLift_comp, toChartAlgHom_ofChartAlgHom]

theorem ofChartAlgHom_interLift_comp {x y : Fin k → Fin n → R}
    {N : G(k, A ⊗[R] (Fin n → R); A)} (hx : N ∈ chart A (baseChangeTuple A x))
    (hy : N ∈ chart A (baseChangeTuple A y)) :
    ofChartAlgHom x ((interLift hx hy).comp (IsScalarTower.toAlgHom R (ChartRing R x) _)) = N := by
  rw [interLift_comp, ofChartAlgHom_toChartAlgHom]

variable (R) in
/-- The intersection of the charts at `x` and `y` is corepresented by the localization of the
chart ring at `x` away from the transition determinant. -/
def chartInterCorepresentableBy [BaseChangeMkQFormula.{u, u, u} R (Fin n → R)]
    (x y : Fin k → Fin n → R) :
    (chartFunctor.{u, u, u} R x ⊓ chartFunctor R y).toFunctor.CorepresentableBy
      (CommAlgCat.of R (Localization.Away (chartTransitionDet x y))) where
  homEquiv {A} :=
    { toFun f :=
        ⟨ofChartAlgHom x (f.hom.comp (IsScalarTower.toAlgHom R (ChartRing R x) _)),
          ofChartAlgHom_mem_chart _ _,
          (ofChartSection_algHomToChartSection_mem_chart_iff x y _).mpr
            ((IsLocalization.Away.algebraMap_isUnit (chartTransitionDet x y)).map f.hom)⟩
      invFun N := CommAlgCat.ofHom (interLift N.2.1 N.2.2)
      left_inv f := by
        apply CommAlgCat.hom_ext
        dsimp only
        exact interLift_ofChartAlgHom_comp x y f.hom
          ((ofChartSection_algHomToChartSection_mem_chart_iff x y _).mpr
            ((IsLocalization.Away.algebraMap_isUnit (chartTransitionDet x y)).map f.hom))
      right_inv N := Subtype.ext (ofChartAlgHom_interLift_comp N.2.1 N.2.2) }
  homEquiv_comp {Y Y'} g f := by
    apply Subtype.ext
    change ofChartAlgHom x ((f ≫ g).hom.comp (IsScalarTower.toAlgHom R (ChartRing R x) _)) =
      map g.hom (ofChartAlgHom x (f.hom.comp (IsScalarTower.toAlgHom R (ChartRing R x) _)))
    rw [CommAlgCat.hom_comp, AlgHom.comp_assoc, ofChartAlgHom, ofChartAlgHom,
      map_ofChartSection_algHomToChartSection]

/-- The two intersection subfunctors of the charts at `x` and `y` agree; this isomorphism is the
identity on underlying points. -/
def interSwapIso [BaseChangeMkQFormula.{u, u, u} R (Fin n → R)]
    (x y : Fin k → Fin n → R) :
    (chartFunctor.{u, u, u} R y ⊓ chartFunctor R x).toFunctor ≅
      (chartFunctor.{u, u, u} R x ⊓ chartFunctor R y).toFunctor :=
  NatIso.ofComponents (fun _ ↦ (Equiv.subtypeEquivRight fun _ ↦ and_comm).toIso)
    (by intros; rfl)

variable (R) in
/-- The transition isomorphism between the two coordinate rings of the intersection of the charts
at `x` and `y`: both localizations corepresent the same subfunctor. Since
`chartTransitionDet x y` lives on the chart at `x`, the source is the coordinate ring of Nitsure's
`U^x_y` and the target that of `U^y_x`; so the `hom` is the ring map of Nitsure's
`θ_{y,x} : U^y_x → U^x_y` (with `I = y`, `J = x`; arXiv:math/0504590v1, §1, p. 8), and the
`inv` is that of `θ_{x,y}`. -/
def chartTransitionIso [BaseChangeMkQFormula.{u, u, u} R (Fin n → R)]
    (x y : Fin k → Fin n → R) :
    CommAlgCat.of R (Localization.Away (chartTransitionDet x y)) ≅
      CommAlgCat.of R (Localization.Away (chartTransitionDet y x)) :=
  (chartInterCorepresentableBy R x y).uniqueUpToIso
    ((chartInterCorepresentableBy R y x).ofIso (interSwapIso x y))

/-- The transition isomorphism is the identity on points: composing with it does not change the
underlying point of the Grassmannian. -/
theorem chartInterCorepresentableBy_homEquiv_transitionIso_hom
    [BaseChangeMkQFormula.{u, u, u} R (Fin n → R)] (x y : Fin k → Fin n → R)
    {A : CommAlgCat.{u} R}
    (Φ : CommAlgCat.of R (Localization.Away (chartTransitionDet y x)) ⟶ A) :
    ((chartInterCorepresentableBy R x y).homEquiv ((chartTransitionIso R x y).hom ≫ Φ)).1 =
      ((chartInterCorepresentableBy R y x).homEquiv Φ).1 := by
  rw [Functor.CorepresentableBy.homEquiv_comp]
  have h : (chartInterCorepresentableBy R x y).homEquiv (chartTransitionIso R x y).hom =
      ((chartInterCorepresentableBy R y x).ofIso (interSwapIso x y)).homEquiv (𝟙 _) := by
    change (chartInterCorepresentableBy R x y).homEquiv
      ((chartInterCorepresentableBy R x y).homEquiv.symm
        (((chartInterCorepresentableBy R y x).ofIso (interSwapIso x y)).homEquiv (𝟙 _))) = _
    exact Equiv.apply_symm_apply _ _
  rw [h, ← Functor.CorepresentableBy.homEquiv_comp, Category.id_comp]
  rfl

/-- The transition isomorphism of a chart with itself is the identity. -/
theorem chartTransitionIso_self_hom [BaseChangeMkQFormula.{u, u, u} R (Fin n → R)]
    (x : Fin k → Fin n → R) :
    (chartTransitionIso R x x).hom = 𝟙 _ := by
  apply (chartInterCorepresentableBy R x x).homEquiv.injective
  apply Subtype.ext
  conv_lhs => rw [← Category.comp_id (chartTransitionIso R x x).hom]
  exact chartInterCorepresentableBy_homEquiv_transitionIso_hom x x (𝟙 _)

theorem chartTransitionIso_self [BaseChangeMkQFormula.{u, u, u} R (Fin n → R)]
    (x : Fin k → Fin n → R) :
    chartTransitionIso R x x = Iso.refl _ :=
  Iso.ext (chartTransitionIso_self_hom x)

section Family

variable {ι : Type*} [Fintype ι]

/-- The product of the transition determinants from the chart at `x` towards a finite family of
tuples `y`. -/
def chartTransitionDetProd (x : Fin k → Fin n → R) (y : ι → Fin k → Fin n → R) :
    ChartRing R x :=
  ∏ i, chartTransitionDet x (y i)

theorem forall_ofChartAlgHom_mem_chart_iff (x : Fin k → Fin n → R)
    (y : ι → Fin k → Fin n → R) (ψ : ChartRing R x →ₐ[R] A) :
    (∀ i, ofChartAlgHom x ψ ∈ chart A (baseChangeTuple A (y i))) ↔
      IsUnit (ψ (chartTransitionDetProd x y)) := by
  rw [chartTransitionDetProd, map_prod, IsUnit.prod_univ_iff]
  exact forall_congr' fun i ↦ ofChartSection_algHomToChartSection_mem_chart_iff x (y i) ψ

/-- The algebra map out of the localized chart ring attached to a point of the chart at `x` and of
all charts at `y i`. -/
def interLiftFamily {x : Fin k → Fin n → R} {y : ι → Fin k → Fin n → R}
    {N : G(k, A ⊗[R] (Fin n → R); A)} (hx : N ∈ chart A (baseChangeTuple A x))
    (hy : ∀ i, N ∈ chart A (baseChangeTuple A (y i))) :
    Localization.Away (chartTransitionDetProd x y) →ₐ[R] A :=
  IsLocalization.liftAlgHom (M := Submonoid.powers (chartTransitionDetProd x y))
    (f := toChartAlgHom hx) (by
      have hu : IsUnit (toChartAlgHom hx (chartTransitionDetProd x y)) := by
        rw [← forall_ofChartAlgHom_mem_chart_iff]
        intro i
        rw [ofChartAlgHom_toChartAlgHom]
        exact hy i
      rintro ⟨_, m, rfl⟩
      simpa using hu.pow m)

theorem interLiftFamily_comp {x : Fin k → Fin n → R} {y : ι → Fin k → Fin n → R}
    {N : G(k, A ⊗[R] (Fin n → R); A)} (hx : N ∈ chart A (baseChangeTuple A x))
    (hy : ∀ i, N ∈ chart A (baseChangeTuple A (y i))) :
    (interLiftFamily hx hy).comp (IsScalarTower.toAlgHom R (ChartRing R x) _) =
      toChartAlgHom hx := by
  ext c
  simp [interLiftFamily, IsLocalization.lift_eq]

theorem interLiftFamily_ofChartAlgHom_comp (x : Fin k → Fin n → R) (y : ι → Fin k → Fin n → R)
    (Φ : Localization.Away (chartTransitionDetProd x y) →ₐ[R] A)
    (hy : ∀ i, ofChartAlgHom x (Φ.comp (IsScalarTower.toAlgHom R (ChartRing R x) _)) ∈
      chart A (baseChangeTuple A (y i))) :
    interLiftFamily (ofChartAlgHom_mem_chart x _) hy = Φ := by
  apply IsLocalization.algHom_ext (Submonoid.powers (chartTransitionDetProd x y))
  change (interLiftFamily _ hy).comp (IsScalarTower.toAlgHom R (ChartRing R x) _) =
    Φ.comp (IsScalarTower.toAlgHom R (ChartRing R x) _)
  rw [interLiftFamily_comp, toChartAlgHom_ofChartAlgHom]

theorem ofChartAlgHom_interLiftFamily_comp {x : Fin k → Fin n → R}
    {y : ι → Fin k → Fin n → R} {N : G(k, A ⊗[R] (Fin n → R); A)}
    (hx : N ∈ chart A (baseChangeTuple A x)) (hy : ∀ i, N ∈ chart A (baseChangeTuple A (y i))) :
    ofChartAlgHom x ((interLiftFamily hx hy).comp
      (IsScalarTower.toAlgHom R (ChartRing R x) _)) = N := by
  rw [interLiftFamily_comp, ofChartAlgHom_toChartAlgHom]

omit [Fintype ι] in
theorem mem_chartFamilyInter_iff [BaseChangeMkQFormula.{u, u, u} R (Fin n → R)]
    (x : Fin k → Fin n → R) (y : ι → Fin k → Fin n → R)
    {A : CommAlgCat.{u} R} (N : (functor.{u, u, u} (R := R) (M := Fin n → R) k).obj A) :
    N ∈ (chartFunctor.{u, u, u} R x ⊓ ⨅ i, chartFunctor R (y i)).obj A ↔
      N ∈ chart A (baseChangeTuple A x) ∧ ∀ i, N ∈ chart A (baseChangeTuple A (y i)) := by
  simp [Subfunctor.iInf_obj, Set.mem_iInter]

variable (R) in
/-- The intersection of the chart at `x` with the charts at a finite family of tuples `y` is
corepresented by the localization of the chart ring at `x` away from the product of the
transition determinants. -/
def chartFamilyInterCorepresentableBy [BaseChangeMkQFormula.{u, u, u} R (Fin n → R)]
    (x : Fin k → Fin n → R) (y : ι → Fin k → Fin n → R) :
    (chartFunctor.{u, u, u} R x ⊓ ⨅ i, chartFunctor R (y i)).toFunctor.CorepresentableBy
      (CommAlgCat.of R (Localization.Away (chartTransitionDetProd x y))) where
  homEquiv {A} :=
    { toFun f :=
        ⟨ofChartAlgHom x (f.hom.comp (IsScalarTower.toAlgHom R (ChartRing R x) _)),
          (mem_chartFamilyInter_iff x y _).mpr ⟨ofChartAlgHom_mem_chart _ _,
            (forall_ofChartAlgHom_mem_chart_iff x y _).mpr
              ((IsLocalization.Away.algebraMap_isUnit (chartTransitionDetProd x y)).map f.hom)⟩⟩
      invFun N := CommAlgCat.ofHom (interLiftFamily ((mem_chartFamilyInter_iff x y N.1).mp N.2).1
        ((mem_chartFamilyInter_iff x y N.1).mp N.2).2)
      left_inv f := by
        apply CommAlgCat.hom_ext
        dsimp only
        exact interLiftFamily_ofChartAlgHom_comp x y f.hom
          ((forall_ofChartAlgHom_mem_chart_iff x y _).mpr
            ((IsLocalization.Away.algebraMap_isUnit (chartTransitionDetProd x y)).map f.hom))
      right_inv N := Subtype.ext (ofChartAlgHom_interLiftFamily_comp
        ((mem_chartFamilyInter_iff x y N.1).mp N.2).1
        ((mem_chartFamilyInter_iff x y N.1).mp N.2).2) }
  homEquiv_comp {Y Y'} g f := by
    apply Subtype.ext
    change ofChartAlgHom x ((f ≫ g).hom.comp (IsScalarTower.toAlgHom R (ChartRing R x) _)) =
      map g.hom (ofChartAlgHom x (f.hom.comp (IsScalarTower.toAlgHom R (ChartRing R x) _)))
    rw [CommAlgCat.hom_comp, AlgHom.comp_assoc, ofChartAlgHom, ofChartAlgHom,
      map_ofChartSection_algHomToChartSection]

end Family

end Module.Grassmannian
