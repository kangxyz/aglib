/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Torsors.Relative

/-!
# Restriction of actual torsor actions to a relative slice

The inverse relative-slice restriction, flatten/restriction equalities, actual changeSource and
canonical total-space isomorphism.

Source: `R5Lab.Aglib.AlgebraicGeometry.Torsors.Restriction`, frozen R5
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`2de5dc6372016cc0d12632409ad579861218540dacbac53ba11ef6275876fb37`. Selected lines: [[64, 265]].
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
open AlgebraicGeometry.Scheme.Torsors.Relative

namespace AlgebraicGeometry.Scheme.Torsors.Restriction
universe u

attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Scheme.{u}} (E : Over S) (A : Grp (Over S)) (X : Over E.left)

/-- The inverse actual coefficient-point equivalence, on the whole test scheme. -/
def globalCoefficient {U : Over E.left} (a : U ⟶ (pullbackGroup E A).X) :
    (Over.map E.hom).obj U ⟶ A.X := (pullbackHomMulEquiv E A U).symm a

@[simp] theorem globalCoefficient_left {U : Over E.left} (a : U ⟶ (pullbackGroup E A).X) :
    (globalCoefficient E A a).left = a.left ≫ pullback.fst A.X.hom E.hom := by
  simp [globalCoefficient, pullbackHomMulEquiv, Over.mapPullbackAdj,
    Adjunction.mkOfHomEquiv_homEquiv]

theorem globalCoefficient_naturality {U V : Over E.left} (f : U ⟶ V)
    (a : V ⟶ (pullbackGroup E A).X) :
    globalCoefficient E A (f ≫ a) = (Over.map E.hom).map f ≫ globalCoefficient E A a := by
  apply Over.OverMorphism.ext
  simp only [globalCoefficient_left, Over.comp_left, Over.map_map_left, Category.assoc]

variable (τ : TorsorAction A (relativeMap E X))

/-- The global action point lies over `E` by the given actual torsor over law. -/
def action {U : Over E.left} (a : U ⟶ (pullbackGroup E A).X) (x : U ⟶ X) : U ⟶ X :=
  Over.homMk (τ.act (globalCoefficient E A a) ((Over.map E.hom).map x)).left (by
    have h := congrArg Over.Hom.left (τ.over (globalCoefficient E A a) ((Over.map E.hom).map x))
    change (τ.act (globalCoefficient E A a) ((Over.map E.hom).map x)).left ≫ X.hom =
      x.left ≫ X.hom at h
    exact h.trans (Over.w x))

theorem action_naturality {U V : Over E.left} (f : U ⟶ V)
    (a : V ⟶ (pullbackGroup E A).X) (x : V ⟶ X) :
    f ≫ action E A X τ a x = action E A X τ (f ≫ a) (f ≫ x) := by
  apply Over.OverMorphism.ext
  have h := τ.naturality ((Over.map E.hom).map f) (globalCoefficient E A a) ((Over.map E.hom).map x)
  rw [← globalCoefficient_naturality, ← Functor.map_comp] at h
  exact congrArg (fun f : (Over.map E.hom).obj U ⟶ totalSpace E X => f.left) h

theorem action_one {U : Over E.left} (x : U ⟶ X) : action E A X τ 1 x = x := by
  apply Over.OverMorphism.ext
  change (τ.act ((pullbackHomMulEquiv E A U).symm 1) ((Over.map E.hom).map x)).left = x.left
  rw [map_one, τ.one_act]
  rfl

theorem action_mul {U : Over E.left} (a b : U ⟶ (pullbackGroup E A).X) (x : U ⟶ X) :
    action E A X τ (a * b) x = action E A X τ a (action E A X τ b x) := by
  apply Over.OverMorphism.ext
  have h := τ.mul_act (globalCoefficient E A a) (globalCoefficient E A b) ((Over.map E.hom).map x)
  change (τ.act ((pullbackHomMulEquiv E A U).symm (a * b)) ((Over.map E.hom).map x)).left = _
  rw [map_mul]
  have hx : (Over.map E.hom).map (action E A X τ b x) =
      τ.act (globalCoefficient E A b) ((Over.map E.hom).map x) := by
    apply Over.OverMorphism.ext
    rfl
  change (τ.act (globalCoefficient E A a * globalCoefficient E A b) ((Over.map E.hom).map x)).left =
    (τ.act (globalCoefficient E A a) ((Over.map E.hom).map (action E A X τ b x))).left
  rw [hx]
  exact congrArg (fun f : (Over.map E.hom).obj U ⟶ totalSpace E X => f.left) h

/-- Global unique transport transfers back through the coefficient-point equivalence. -/
theorem action_transport {U : Over E.left} (x y : U ⟶ X) :
    ∃! a : U ⟶ (pullbackGroup E A).X, action E A X τ a x = y := by
  have h : (Over.map E.hom).map x ≫ relativeMap E X =
      (Over.map E.hom).map y ≫ relativeMap E X := by
    apply Over.OverMorphism.ext
    exact (Over.w x).trans (Over.w y).symm
  obtain ⟨a, ha, hu⟩ := τ.transport ((Over.map E.hom).map x) ((Over.map E.hom).map y) h
  refine ⟨pullbackHomMulEquiv E A U a, ?_, ?_⟩
  · apply Over.OverMorphism.ext
    change (τ.act ((pullbackHomMulEquiv E A U).symm (pullbackHomMulEquiv E A U a))
      ((Over.map E.hom).map x)).left = y.left
    rw [MulEquiv.symm_apply_apply]
    exact congrArg Over.Hom.left ha
  · intro b hb
    have hb' : τ.act (globalCoefficient E A b) ((Over.map E.hom).map x) =
        (Over.map E.hom).map y := by
      apply Over.OverMorphism.ext
      exact congrArg (fun f : U ⟶ X => f.left) hb
    apply (pullbackHomMulEquiv E A U).symm.injective
    rw [MulEquiv.symm_apply_apply]
    exact hu _ hb'

/-- Restrict the original actual torsor-action interface to `Over E.left`. -/
def relativeTorsorRestriction : TorsorAction (pullbackGroup E A) (toUnit X) where
  act := action E A X τ
  naturality := action_naturality E A X τ
  one_act := action_one E A X τ
  mul_act := action_mul E A X τ
  over := fun _ _ => toUnit_unique _ _
  transport := fun x y _ => action_transport E A X τ x y

/-- The relative point action is the original global action on the pushed points. -/
theorem relativeTorsorRestriction_point {U : Over E.left}
    (a : U ⟶ (pullbackGroup E A).X) (x : U ⟶ X) :
    ((relativeTorsorRestriction E A X τ).act a x).left =
      (τ.act (globalCoefficient E A a) ((Over.map E.hom).map x)).left := rfl

/-- Restriction recovers every actual torsor action over `E`. -/
theorem restriction_flatten (σ : TorsorAction (pullbackGroup E A) (toUnit X)) :
    relativeTorsorRestriction E A X (relativeTorsorAction E A X σ) = σ := by
  apply _root_.CategoryTheory.TorsorAction.ext
  intro U a x
  apply Over.OverMorphism.ext
  change (Relative.action E A X σ (globalCoefficient E A a) ((Over.map E.hom).map x)).left =
    (σ.act a x).left
  exact Relative.action_left_of_lifts E A X σ (globalCoefficient E A a) ((Over.map E.hom).map x)
    a x (globalCoefficient_left E A a).symm rfl

/-- Flattening the restriction recovers the original actual torsor action over `S`. -/
theorem flatten_restriction :
    relativeTorsorAction E A X (relativeTorsorRestriction E A X τ) = τ := by
  apply _root_.CategoryTheory.TorsorAction.ext
  intro Y a x
  let j := pointBaseIso E X x
  have hc : globalCoefficient E A (coefficientPoints E A X x a) = j.hom ≫ a := by
    apply Over.OverMorphism.ext
    simp only [globalCoefficient_left, coefficientPoints_fst, Over.comp_left]
    change a.left = 𝟙 Y.left ≫ a.left
    exact (Category.id_comp _).symm
  have hx : (Over.map E.hom).map (relativePoint E X x) = j.hom ≫ x := by
    apply Over.OverMorphism.ext
    change x.left = 𝟙 Y.left ≫ x.left
    exact (Category.id_comp _).symm
  have hn := congrArg
    (fun f : (Over.map E.hom).obj (relativeTest E X x) ⟶ totalSpace E X => f.left)
    (τ.naturality j.hom a x)
  have hj : j.hom.left = 𝟙 Y.left := rfl
  simp only [Over.comp_left, hj] at hn
  apply Over.OverMorphism.ext
  change (τ.act (globalCoefficient E A (coefficientPoints E A X x a))
    ((Over.map E.hom).map (relativePoint E X x))).left = (τ.act a x).left
  rw [hc, hx]
  exact hn.symm

/-- Move an existing torsor action along an actual source isomorphism. -/
def changeSource {P : Grp (Over S)} {Y Y' Z : Over S} {p : Y ⟶ Z}
    (i : Y' ≅ Y) (σ : TorsorAction P p) : TorsorAction P (i.hom ≫ p) where
  act a x := σ.act a (x ≫ i.hom) ≫ i.inv
  naturality f a x := by
    simpa only [Category.assoc] using
      congrArg (fun y => y ≫ i.inv) (σ.naturality f a (x ≫ i.hom))
  one_act x := by
    rw [σ.one_act]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  mul_act a b x := by
    rw [σ.mul_act]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  over a x := by
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using σ.over a (x ≫ i.hom)
  transport x y h := by
    have h' : (x ≫ i.hom) ≫ p = (y ≫ i.hom) ≫ p := by
      simpa only [Category.assoc] using h
    obtain ⟨a, ha, hu⟩ := σ.transport (x ≫ i.hom) (y ≫ i.hom) h'
    refine ⟨a, ?_, ?_⟩
    · simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
        congrArg (fun z => z ≫ i.inv) ha
    · intro b hb
      apply hu b
      simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
        congrArg (fun z => z ≫ i.hom) hb

theorem changeSource_act {P : Grp (Over S)} {Y Y' Z : Over S} {p : Y ⟶ Z}
    (i : Y' ≅ Y) (σ : TorsorAction P p) {U : Over S} (a : U ⟶ P.X) (x : U ⟶ Y') :
    (changeSource i σ).act a x = σ.act a (x ≫ i.hom) ≫ i.inv := rfl

/-- The actual scheme underlying an arbitrary cover map, viewed over `E.left`. -/
abbrev canonicalRelativeSpace {Y : Over S} (f : Y ⟶ E) : Over E.left := Over.mk f.left

/-- The original structural-map equality gives a canonical actual source isomorphism. -/
def canonicalTotalIso {Y : Over S} (f : Y ⟶ E) :
    totalSpace E (canonicalRelativeSpace E f) ≅ Y :=
  Over.isoMk (Iso.refl Y.left) (by
    change 𝟙 Y.left ≫ Y.hom = f.left ≫ E.hom
    simpa only [Category.id_comp] using (Over.w f).symm)

theorem canonicalTotalIso_comp {Y : Over S} (f : Y ⟶ E) :
    (canonicalTotalIso E f).hom ≫ f = relativeMap E (canonicalRelativeSpace E f) := by
  apply Over.OverMorphism.ext
  change 𝟙 Y.left ≫ f.left = f.left
  exact Category.id_comp _

/-- Restrict an actual torsor cover whose source was given as an arbitrary
object over `S`, using only its structural morphism and canonical source isomorphism. -/
def relativeTorsorRestrictionOfMap {Y : Over S} (f : Y ⟶ E) (σ : TorsorAction A f) :
    TorsorAction (pullbackGroup E A) (toUnit (canonicalRelativeSpace E f)) :=
  relativeTorsorRestriction E A (canonicalRelativeSpace E f)
    ((canonicalTotalIso_comp E f) ▸ changeSource (canonicalTotalIso E f) σ)

private theorem torsorAction_cast_act {P : Grp (Over S)} {Y Z : Over S} {p q : Y ⟶ Z}
    (h : p = q) (σ : TorsorAction P p) {U : Over S} (a : U ⟶ P.X) (x : U ⟶ Y) :
    (h ▸ σ).act a x = σ.act a x := by
  cases h
  rfl

/-- The arbitrary-cover wrapper retains the original scheme-valued point action. -/
theorem relativeTorsorRestrictionOfMap_point {Y : Over S} (f : Y ⟶ E) (σ : TorsorAction A f)
    {U : Over E.left} (a : U ⟶ (pullbackGroup E A).X) (x : U ⟶ canonicalRelativeSpace E f) :
    ((relativeTorsorRestrictionOfMap E A f σ).act a x).left =
      (σ.act (globalCoefficient E A a)
        ((Over.map E.hom).map x ≫ (canonicalTotalIso E f).hom)).left := by
  unfold relativeTorsorRestrictionOfMap
  rw [relativeTorsorRestriction_point]
  have hact := torsorAction_cast_act (canonicalTotalIso_comp E f)
    (changeSource (canonicalTotalIso E f) σ) (globalCoefficient E A a) ((Over.map E.hom).map x)
  rw [hact, changeSource_act]
  change (σ.act (globalCoefficient E A a)
    ((Over.map E.hom).map x ≫ (canonicalTotalIso E f).hom)).left ≫ 𝟙 Y.left = _
  exact Category.comp_id _

end AlgebraicGeometry.Scheme.Torsors.Restriction
