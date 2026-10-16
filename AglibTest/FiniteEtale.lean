/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange

/-! # Strict clients of the actual finite etale category and point fibres -/
@[expose] public section

set_option autoImplicit false
set_option warningAsError true
set_option linter.mathlibStandardSet true

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.FiniteEtale
universe u

namespace AglibTest.FiniteEtale

/-- The ordinary constructor imposes finite etaleness and no surjectivity premise. -/
def actualObject {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Etale f] :
    Scheme.FiniteEtale X := mk f

/-- The empty scheme is an admitted object over every base. -/
def emptyObject (X : Scheme.{u}) : Scheme.FiniteEtale X := mk (Scheme.emptyTo X)

/-- No lift of a field-valued point to the empty object is manufactured. -/
example {X : Scheme.{u}} {K : Type u} [Field K]
    (x : Spec (CommRingCat.of K) ⟶ X) : IsEmpty (Fiber x (emptyObject X)) := by
  change IsEmpty (Over.mk x ⟶ Over.mk (Scheme.emptyTo X))
  refine ⟨fun p => ?_⟩
  have z : (∅ : Scheme.{u}) := p.left (default : Spec (CommRingCat.of K))
  exact isEmptyElim z

/-- Finiteness of point lifts needs a finite map, with no etale or closed-field premise. -/
example {X Y : Scheme.{u}} {K : Type u} [Field K]
    (f : Y ⟶ X) [IsFinite f] (x : Spec (CommRingCat.of K) ⟶ X) :
    Finite (Over.mk x ⟶ Over.mk f) := Scheme.Finite.finite_hom_over_point f x

example {X : Scheme.{u}} {K : Type u} [Field K]
    (x : Spec (CommRingCat.of K) ⟶ X) {Y Z : Scheme.FiniteEtale X}
    (f : Y ⟶ Z) (p : Fiber x Y) : ((fiber x).map f p).left = p.left ≫ f.hom.left :=
  fiber_map_left x f p

example {X S : Scheme.{u}} (f : S ⟶ X) (Y : Scheme.FiniteEtale X) :
    ((baseChange f).obj Y).obj.hom = pullback.snd Y.obj.hom f := baseChange_obj_hom f Y

example {X S : Scheme.{u}} {K : Type u} [Field K]
    (f : S ⟶ X) (x : Spec (CommRingCat.of K) ⟶ S) (Y : Scheme.FiniteEtale X)
    (p : Fiber (x ≫ f) Y) :
    (fiberBaseChangeEquiv f x Y p).left = pullback.lift p.left x (Over.w p) :=
  fiberBaseChangeEquiv_left f x Y p

example {X S : Scheme.{u}} {K : Type u} [Field K]
    (f : S ⟶ X) (x : Spec (CommRingCat.of K) ⟶ S) (Y : Scheme.FiniteEtale X)
    (p : Fiber x ((baseChange f).obj Y)) :
    ((fiberBaseChangeEquiv f x Y).symm p).left = p.left ≫ pullback.fst Y.obj.hom f :=
  fiberBaseChangeEquiv_symm_left f x Y p

example (X : Scheme.{u}) : baseChange (𝟙 X) ≅ 𝟭 (Scheme.FiniteEtale X) := baseChangeId X

example {X S T : Scheme.{u}} (f : S ⟶ X) (g : T ⟶ S) :
    baseChange (g ≫ f) ≅ baseChange f ⋙ baseChange g := baseChangeComp f g

example {X : Scheme.{u}} {K : Type u} [Field K] [IsSepClosed K]
    (x : Spec (CommRingCat.of K) ⟶ X) :
    toEtale X ⋙ (Scheme.pointSmallEtale x).fiber ≅ fiber x := smallEtaleFiberIso x

example {X : Scheme.{u}} {K : Type u} [Field K] [IsSepClosed K]
    (x : Spec (CommRingCat.of K) ⟶ X) (Y : Scheme.FiniteEtale X) :
    Function.Surjective (pointToPreimage x Y) := pointToPreimage_surjective x Y

end AglibTest.FiniteEtale
