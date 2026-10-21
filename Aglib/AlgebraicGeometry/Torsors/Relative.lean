/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.TorsorAction.Basic
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# Actual torsor actions under change of slice

Change of slice constructs an actual relative torsor action, including literal
coefficient-pullback points and arbitrary-test naturality.

Source: `R5Lab.Aglib.AlgebraicGeometry.Torsors.Relative`, frozen R5
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`e00d373fa5a44693487c50cba0a21fcac92dc0c20478ed8e15f2123c119fa9dd`. Selected lines: [[65, 299]].
The actual objects, canonical maps, universes and stated premises are retained.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj CategoryTheory.Obj
open _root_.CategoryTheory

namespace AlgebraicGeometry.Scheme.Torsors.Relative
universe u

attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Scheme.{u}} (E : Over S) (A : Grp (Over S)) (X : Over E.left)

/-- The actual group-scheme pullback along the structural morphism of `E`. -/
abbrev pullbackGroup : Grp (Over E.left) := (Over.pullback E.hom).mapGrp.obj A

/-- The actual total scheme `X` over `S`, with its composite structural map. -/
abbrev totalSpace : Over S := (Over.map E.hom).obj X

/-- The same structural morphism `X.hom`, viewed as a morphism over `S`. -/
def relativeMap : totalSpace E X ⟶ E := Over.homMk X.hom rfl

@[simp] theorem totalSpace_hom : (totalSpace E X).hom = X.hom ≫ E.hom := rfl

@[simp] theorem relativeMap_left : (relativeMap E X).left = X.hom := rfl

/-- A supplied point makes its whole test scheme an object over `E`. -/
abbrev relativeTest {Y : Over S} (x : Y ⟶ totalSpace E X) : Over E.left :=
  Over.mk (x.left ≫ X.hom)

/-- The supplied total-space point, viewed over its actual map to the relative base. -/
def relativePoint {Y : Over S} (x : Y ⟶ totalSpace E X) : relativeTest E X x ⟶ X :=
  Over.homMk x.left rfl

/-- The total relative test scheme is canonically the original test scheme over the base. -/
def pointBaseIso {Y : Over S} (x : Y ⟶ totalSpace E X) :
    (Over.map E.hom).obj (relativeTest E X x) ≅ Y :=
  Over.isoMk (Iso.refl Y.left) (by
    change 𝟙 Y.left ≫ Y.hom = (x.left ≫ X.hom) ≫ E.hom
    simpa only [totalSpace, Over.map_obj_hom, Category.id_comp, Category.assoc]
      using (Over.w x).symm)

/-- Precomposition by an actual source isomorphism preserves the group law on points. -/
def precomposeMulEquiv {U V : Over S} (e : U ≅ V) :
    (V ⟶ A.X) ≃* (U ⟶ A.X) where
  toFun f := e.hom ≫ f
  invFun f := e.inv ≫ f
  left_inv f := by simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  right_inv f := by simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  map_mul' f g := MonObj.comp_mul _ _ _

/-- The actual slice pullback adjunction preserves the group law on points. -/
def pullbackHomMulEquiv (U : Over E.left) :
    ((Over.map E.hom).obj U ⟶ A.X) ≃* (U ⟶ (pullbackGroup E A).X) where
  __ := (Over.mapPullbackAdj E.hom).homEquiv U A.X
  map_mul' p q := by
    let : GrpObj ((Over.pullback E.hom).obj A.X) := (pullbackGroup E A).grp
    change (Over.mapPullbackAdj E.hom).unit.app U ≫ (Over.pullback E.hom).map (p * q) =
      ((Over.mapPullbackAdj E.hom).unit.app U ≫ (Over.pullback E.hom).map p) *
        ((Over.mapPullbackAdj E.hom).unit.app U ≫ (Over.pullback E.hom).map q)
    rw [(Over.pullback E.hom).map_mul, MonObj.comp_mul]

/-- Coefficient points over `S` and over the base point of `x` are
multiplicatively equivalent on every test scheme. -/
def coefficientPoints {Y : Over S} (x : Y ⟶ totalSpace E X) :
    (Y ⟶ A.X) ≃* (relativeTest E X x ⟶ (pullbackGroup E A).X) :=
  (precomposeMulEquiv A (pointBaseIso E X x)).trans
    (pullbackHomMulEquiv E A (relativeTest E X x))

@[simp] theorem coefficientPoints_fst {Y : Over S} (x : Y ⟶ totalSpace E X) (a : Y ⟶ A.X) :
    (coefficientPoints E A X x a).left ≫ pullback.fst A.X.hom E.hom = a.left := by
  simp [coefficientPoints, precomposeMulEquiv, pullbackHomMulEquiv, Over.mapPullbackAdj,
    Adjunction.mkOfHomEquiv_homEquiv, pointBaseIso, Over.comp_left, Category.id_comp]

@[simp] theorem coefficientPoints_snd {Y : Over S} (x : Y ⟶ totalSpace E X) (a : Y ⟶ A.X) :
    (coefficientPoints E A X x a).left ≫ pullback.snd A.X.hom E.hom = x.left ≫ X.hom :=
  Over.w _

@[simp] theorem coefficientPoints_symm_left {Y : Over S} (x : Y ⟶ totalSpace E X)
    (a : relativeTest E X x ⟶ (pullbackGroup E A).X) :
    ((coefficientPoints E A X x).symm a).left = a.left ≫ pullback.fst A.X.hom E.hom := by
  simp [coefficientPoints, precomposeMulEquiv, pullbackHomMulEquiv, Over.mapPullbackAdj,
    Adjunction.mkOfHomEquiv_homEquiv, pointBaseIso, Over.comp_left]

/-- The coefficient and relative-base maps satisfy the literal pullback compatibility. -/
theorem liftCondition {Y : Over S} (x : Y ⟶ totalSpace E X) (a : Y ⟶ A.X) :
    a.left ≫ A.X.hom = (x.left ≫ X.hom) ≫ E.hom := by
  calc
    a.left ≫ A.X.hom = Y.hom := Over.w a
    _ = (x.left ≫ X.hom) ≫ E.hom := by
      simpa only [totalSpace, Over.map_obj_hom, Category.assoc] using (Over.w x).symm

/-- The coefficient lift is precisely the actual pullback universal morphism. -/
theorem coefficientPoints_left {Y : Over S} (x : Y ⟶ totalSpace E X) (a : Y ⟶ A.X) :
    (coefficientPoints E A X x a).left =
      pullback.lift a.left (x.left ≫ X.hom) (liftCondition E A X x a) := by
  apply pullback.hom_ext
  · simpa only [pullback.lift_fst] using coefficientPoints_fst E A X x a
  · simpa only [pullback.lift_snd] using coefficientPoints_snd E A X x a

/-- Construct the coefficient point by the actual scheme pullback universal property. -/
def liftCoefficient {Y : Over S} (x : Y ⟶ totalSpace E X) (a : Y ⟶ A.X) :
    relativeTest E X x ⟶ (pullbackGroup E A).X :=
  Over.homMk (pullback.lift a.left (x.left ≫ X.hom) (liftCondition E A X x a))
    (pullback.lift_snd _ _ _)

theorem liftCoefficient_eq {Y : Over S} (x : Y ⟶ totalSpace E X) (a : Y ⟶ A.X) :
    liftCoefficient E A X x a = coefficientPoints E A X x a :=
  Over.OverMorphism.ext (coefficientPoints_left E A X x a).symm

variable (τ : TorsorAction (pullbackGroup E A) (toUnit X))

/-- Return the relative action point as an actual point over `S`. -/
def action {Y : Over S} (a : Y ⟶ A.X) (x : Y ⟶ totalSpace E X) : Y ⟶ totalSpace E X :=
  Over.homMk (τ.act (coefficientPoints E A X x a) (relativePoint E X x)).left (by
    change (τ.act (coefficientPoints E A X x a) (relativePoint E X x)).left ≫
      (X.hom ≫ E.hom) = Y.hom
    rw [← Category.assoc, Over.w]
    change (x.left ≫ X.hom) ≫ E.hom = Y.hom
    simpa only [totalSpace, Over.map_obj_hom, Category.assoc] using Over.w x)

theorem action_over {Y : Over S} (a : Y ⟶ A.X) (x : Y ⟶ totalSpace E X) :
    action E A X τ a x ≫ relativeMap E X = x ≫ relativeMap E X := by
  apply Over.OverMorphism.ext
  exact Over.w (τ.act (coefficientPoints E A X x a) (relativePoint E X x))

/-- Any actual lifts with the same projections give the same action point. -/
theorem action_left_of_lifts {Y : Over S} (a : Y ⟶ A.X) (x : Y ⟶ totalSpace E X)
    {e : Y.left ⟶ E.left} (aE : Over.mk e ⟶ (pullbackGroup E A).X)
    (xE : Over.mk e ⟶ X)
    (ha : aE.left ≫ pullback.fst A.X.hom E.hom = a.left) (hx : xE.left = x.left) :
    (action E A X τ a x).left = (τ.act aE xE).left := by
  have he : x.left ≫ X.hom = e := by
    rw [← hx]
    exact Over.w xE
  subst e
  have hcoeff : coefficientPoints E A X x a = aE := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact (coefficientPoints_fst E A X x a).trans ha.symm
    · exact (Over.w _).trans (Over.w aE).symm
  have hpoint : relativePoint E X x = xE := Over.OverMorphism.ext hx.symm
  change (τ.act (coefficientPoints E A X x a) (relativePoint E X x)).left = _
  rw [hcoeff, hpoint]

theorem action_naturality {Y Z : Over S} (f : Y ⟶ Z) (a : Z ⟶ A.X)
    (x : Z ⟶ totalSpace E X) :
    f ≫ action E A X τ a x = action E A X τ (f ≫ a) (f ≫ x) := by
  let fE : relativeTest E X (f ≫ x) ⟶ relativeTest E X x := Over.homMk f.left (by
    change f.left ≫ (x.left ≫ X.hom) = (f.left ≫ x.left) ≫ X.hom
    exact (Category.assoc _ _ _).symm)
  have hn := congrArg Over.Hom.left
    (τ.naturality fE (coefficientPoints E A X x a) (relativePoint E X x))
  have ha : (fE ≫ coefficientPoints E A X x a).left ≫ pullback.fst A.X.hom E.hom =
      (f ≫ a).left := by
    change (f.left ≫ (coefficientPoints E A X x a).left) ≫ pullback.fst A.X.hom E.hom =
      f.left ≫ a.left
    rw [Category.assoc, coefficientPoints_fst]
  have hc := action_left_of_lifts E A X τ (f ≫ a) (f ≫ x)
    (fE ≫ coefficientPoints E A X x a) (fE ≫ relativePoint E X x) ha rfl
  apply Over.OverMorphism.ext
  exact hn.trans hc.symm

theorem action_one {Y : Over S} (x : Y ⟶ totalSpace E X) :
    action E A X τ 1 x = x := by
  apply Over.OverMorphism.ext
  change (τ.act (coefficientPoints E A X x 1) (relativePoint E X x)).left = x.left
  rw [map_one, τ.one_act]
  rfl

theorem action_mul {Y : Over S} (a b : Y ⟶ A.X) (x : Y ⟶ totalSpace E X) :
    action E A X τ (a * b) x = action E A X τ a (action E A X τ b x) := by
  have hc := action_left_of_lifts E A X τ a (action E A X τ b x)
    (coefficientPoints E A X x a)
    (τ.act (coefficientPoints E A X x b) (relativePoint E X x))
    (coefficientPoints_fst E A X x a) rfl
  apply Over.OverMorphism.ext
  change (τ.act (coefficientPoints E A X x (a * b)) (relativePoint E X x)).left = _
  rw [map_mul, τ.mul_act]
  exact hc.symm

/-- Relative unique transport transfers to every test object over `S`. -/
theorem action_transport {Y : Over S} (x y : Y ⟶ totalSpace E X)
    (h : x ≫ relativeMap E X = y ≫ relativeMap E X) :
    ∃! a : Y ⟶ A.X, action E A X τ a x = y := by
  let yE : relativeTest E X x ⟶ X := Over.homMk y.left (by
    have hh := congrArg Over.Hom.left h
    change x.left ≫ X.hom = y.left ≫ X.hom at hh
    exact hh.symm)
  obtain ⟨aE, haE, huE⟩ := τ.transport (relativePoint E X x) yE (toUnit_unique _ _)
  refine ⟨(coefficientPoints E A X x).symm aE, ?_, ?_⟩
  · apply Over.OverMorphism.ext
    change (τ.act (coefficientPoints E A X x ((coefficientPoints E A X x).symm aE))
      (relativePoint E X x)).left = y.left
    rw [MulEquiv.apply_symm_apply, haE]
    rfl
  · intro a ha
    have ha' : τ.act (coefficientPoints E A X x a) (relativePoint E X x) = yE :=
      Over.OverMorphism.ext (congrArg (fun f : Y ⟶ totalSpace E X => f.left) ha)
    apply (coefficientPoints E A X x).injective
    rw [MulEquiv.apply_symm_apply]
    exact huE _ ha'

/-- Change from the slice over `E.left` to the original scheme category
over `S`, retaining the actual group `A` and relative structural map. -/
def relativeTorsorAction : TorsorAction A (relativeMap E X) where
  act := action E A X τ
  naturality := action_naturality E A X τ
  one_act := action_one E A X τ
  mul_act := action_mul E A X τ
  over := action_over E A X τ
  transport := action_transport E A X τ

/-- The point-action formula uses the actual coefficient pullback lift. -/
theorem relativeTorsorAction_point {Y : Over S} (a : Y ⟶ A.X) (x : Y ⟶ totalSpace E X) :
    ((relativeTorsorAction E A X τ).act a x).left =
      (τ.act (liftCoefficient E A X x a) (relativePoint E X x)).left := by
  change (τ.act (coefficientPoints E A X x a) (relativePoint E X x)).left = _
  rw [liftCoefficient_eq]

/-- Transport an existing torsor action through an actual coefficient-group
isomorphism, using its inverse for unique transport. -/
def changeCoefficient {P Q : Grp (Over S)} {Y Z : Over S} {p : Y ⟶ Z}
    (e : P ≅ Q) (σ : TorsorAction Q p) : TorsorAction P p := by
  let j : P.X ≅ Q.X := (Grp.forget (Over S)).mapIso e
  letI : IsMonHom j.hom := by
    change IsMonHom e.hom.hom.hom
    infer_instance
  refine
    { act := fun a x => σ.act (a ≫ j.hom) x
      naturality := ?_
      one_act := ?_
      mul_act := ?_
      over := fun a x => σ.over (a ≫ j.hom) x
      transport := ?_ }
  · intro T U f a x
    simp only [σ.naturality, Category.assoc]
  · intro T x
    rw [MonObj.one_comp]
    exact σ.one_act x
  · intro T a b x
    rw [MonObj.mul_comp, σ.mul_act]
  · intro T x y h
    obtain ⟨a, ha, hu⟩ := σ.transport x y h
    refine ⟨a ≫ j.inv, ?_, ?_⟩
    · simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using ha
    · intro b hb
      have hh := congrArg (fun a : T ⟶ Q.X => a ≫ j.inv) (hu (b ≫ j.hom) hb)
      simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hh

theorem changeCoefficient_act {P Q : Grp (Over S)} {Y Z : Over S} {p : Y ⟶ Z}
    (e : P ≅ Q) (σ : TorsorAction Q p) {T : Over S} (a : T ⟶ P.X) (x : T ⟶ Y) :
    (changeCoefficient e σ).act a x = σ.act (a ≫ e.hom.hom.hom) x := rfl

end AlgebraicGeometry.Scheme.Torsors.Relative
