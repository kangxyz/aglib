/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Basic
public import Aglib.AlgebraicGeometry.Morphisms.Finite.PointLifts
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.FintypeCat

/-!
# Actual point fibres of finite etale schemes

Fibres consist of actual morphisms over the base and their maps are postcomposition.
Every field-valued fibre is finite. The site-point comparison and surjectivity onto
the topological fibre additionally require a separably closed field. No injectivity
of the point-to-topological-fibre map or faithfulness of the fibre functor is asserted.

Source: R5Lab/AlgebraicGeometry/FiniteEtale/Fiber.lean
at R5 revision 2f9ca464b192cff865858dda70b2d8e5dca8b3df.
SHA256: 2ea7277dcd82b233b4ecada3e0aa91cd6099a8e7704248b807eb140af8f12355
Selection: actual point lifts, fibre functors and geometric-point comparison; finite-only lemmas
are in PointLifts.
Actual objects, maps, universes and hypotheses are retained.
-/
@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u

namespace AlgebraicGeometry.Scheme.FiniteEtale

/-- Lifts of the field-valued point `x` through the cover `Y`, as `Over` morphisms. -/
abbrev Fiber {X : Scheme.{u}} {K : Type u} [Field K]
    (x : Spec (CommRingCat.of K) ⟶ X) (Y : FiniteEtale X) :=
  Over.mk x ⟶ Y.obj

/-- The Types-valued fibre functor, represented in `Over X` by `x`. -/
def fiber {X : Scheme.{u}} {K : Type u} [Field K]
    (x : Spec (CommRingCat.of K) ⟶ X) : FiniteEtale X ⥤ Type u :=
  forget X ⋙ coyoneda.obj (op (Over.mk x))

/-- For a separably closed field, the fibre is the restriction of mathlib's
geometric point on the small étale site. -/
def smallEtaleFiberIso {X : Scheme.{u}} {K : Type u} [Field K] [IsSepClosed K]
    (x : Spec (CommRingCat.of K) ⟶ X) :
    toEtale X ⋙ (Scheme.pointSmallEtale x).fiber ≅ fiber x := Iso.refl _

@[simp] theorem fiber_obj {X : Scheme.{u}} {K : Type u} [Field K]
    (x : Spec (CommRingCat.of K) ⟶ X) (Y : FiniteEtale X) :
    (fiber x).obj Y = Fiber x Y := rfl

theorem fiber_map {X : Scheme.{u}} {K : Type u} [Field K]
    (x : Spec (CommRingCat.of K) ⟶ X) {Y Z : FiniteEtale X}
    (f : Y ⟶ Z) (p : Fiber x Y) : (fiber x).map f p = p ≫ f.hom := rfl

theorem fiber_map_left {X : Scheme.{u}} {K : Type u} [Field K]
    (x : Spec (CommRingCat.of K) ⟶ X) {Y Z : FiniteEtale X}
    (f : Y ⟶ Z) (p : Fiber x Y) : ((fiber x).map f p).left = p.left ≫ f.hom.left := rfl

theorem fiber_map_id {X : Scheme.{u}} {K : Type u} [Field K]
    (x : Spec (CommRingCat.of K) ⟶ X) (Y : FiniteEtale X) (p : Fiber x Y) :
    (fiber x).map (𝟙 Y) p = p := by
  change p ≫ 𝟙 Y.obj = p
  exact Category.comp_id p

theorem fiber_map_comp {X : Scheme.{u}} {K : Type u} [Field K]
    (x : Spec (CommRingCat.of K) ⟶ X) {Y Z W : FiniteEtale X}
    (f : Y ⟶ Z) (g : Z ⟶ W) (p : Fiber x Y) :
    (fiber x).map (f ≫ g) p = (fiber x).map g ((fiber x).map f p) := by
  change p ≫ (f.hom ≫ g.hom) = (p ≫ f.hom) ≫ g.hom
  exact (Category.assoc _ _ _).symm


/-- A point lift determines a point of the structural morphism's topological fibre. -/
def pointToPreimage {X : Scheme.{u}} {K : Type u} [Field K]
    (x : Spec (CommRingCat.of K) ⟶ X) (Y : FiniteEtale X) (p : Fiber x Y) :
    Y.obj.hom ⁻¹' {x default} :=
  ⟨p.left (default : Spec (CommRingCat.of K)),
    congrArg (fun f : Spec (CommRingCat.of K) ⟶ X => f default) (Over.w p)⟩

theorem pointToPreimage_map {X : Scheme.{u}} {K : Type u} [Field K]
    (x : Spec (CommRingCat.of K) ⟶ X) {Y Z : FiniteEtale X} (f : Y ⟶ Z) (p : Fiber x Y) :
    (pointToPreimage x Z ((fiber x).map f p)).1 =
      f.hom.left (pointToPreimage x Y p).1 := rfl

/-- Over a separably closed field, every point of the topological fibre
admits a lift. This asserts surjectivity, without identifying distinct lifts. -/
theorem pointToPreimage_surjective {X : Scheme.{u}} {K : Type u}
    [Field K] [IsSepClosed K] (x : Spec (CommRingCat.of K) ⟶ X) (Y : FiniteEtale X) :
    Function.Surjective (pointToPreimage x Y) := by
  intro p
  obtain ⟨l, hl, hpoint⟩ :=
    Scheme.exists_fac_of_etale_of_isSepClosed Y.obj.hom x p.1 p.2
  exact ⟨Over.homMk l hl, Subtype.ext hpoint⟩

instance finiteFiber {X : Scheme.{u}} {K : Type u} [Field K]
    (x : Spec (CommRingCat.of K) ⟶ X) (Y : FiniteEtale X) : Finite (Fiber x Y) :=
  Finite.finite_hom_over_point Y.obj.hom x

/-- The fibre functor valued in finite types, using the proved finiteness of point lifts. -/
def fiberToFinite {X : Scheme.{u}} {K : Type u} [Field K]
    (x : Spec (CommRingCat.of K) ⟶ X) : FiniteEtale X ⥤ FintypeCat.{u} :=
  ObjectProperty.lift (Finite : ObjectProperty (Type u)) (fiber x) (fun Y => finiteFiber x Y)

/-- Forgetting finiteness recovers the Types-valued point fibre functor. -/
def fiberToFiniteForgetIso {X : Scheme.{u}} {K : Type u} [Field K]
    (x : Spec (CommRingCat.of K) ⟶ X) :
    fiberToFinite x ⋙ FintypeCat.incl ≅ fiber x := Iso.refl _

@[simp] theorem fiberToFinite_map {X : Scheme.{u}} {K : Type u} [Field K]
    (x : Spec (CommRingCat.of K) ⟶ X) {Y Z : FiniteEtale X} (f : Y ⟶ Z) (p : Fiber x Y) :
    (fiberToFinite x).map f p = p ≫ f.hom := rfl

end AlgebraicGeometry.Scheme.FiniteEtale
