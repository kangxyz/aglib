/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.TorsorAction.Basic
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# The actual kernel group of a group-scheme morphism

The kernel is the literal pullback over the actual unit. Its marking has
the universal property on every test scheme. The construction works over
any base scheme; finiteness and etaleness are used only for their own instances.

Source: `R5Lab.Aglib.AlgebraicGeometry.Group.Kernel.PrimeDegree`
at R5 `f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`46287e1784c368df3403d8949bdf4d6c66c251691a48579ec8ab9a9f4481c665`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.Group.Kernel

universe u
attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Scheme.{u}} {G E : Grp (Over S)} (p : G ⟶ E)

/-- The group-object identity section, from the genuine terminal group scheme. -/
def identityHom : Grp.trivial (Over S) ⟶ E := Grp.homMk η[E.X]

/-- The actual group-scheme kernel, constructed as a pullback in group objects. -/
def group : Grp (Over S) := pullback p (identityHom (E := E))

/-- The actual group-scheme kernel inclusion. -/
def inclusion : group p ⟶ G := pullback.fst p (identityHom (E := E))

/-- Forgetting the group law preserves the actual kernel pullback. -/
theorem square :
    IsPullback (inclusion p).hom.hom (toUnit (group p).X) p.hom.hom η[E.X] := by
  have h := (IsPullback.of_hasPullback p (identityHom (E := E))).map
    (Grp.forget (Over S))
  change IsPullback (inclusion p).hom.hom
    (pullback.snd p (identityHom (E := E))).hom.hom p.hom.hom η[E.X] at h
  rwa [toUnit_unique (pullback.snd p (identityHom (E := E))).hom.hom
    (toUnit (group p).X)] at h

/-- The actual inclusion has the kernel universal property on every test scheme. -/
def marking : KernelMarking (group p) G E p where
  inclusion := inclusion p
  «over» := (square p).w
  unique_lift k hk := by
    refine ⟨(square p).lift k (toUnit _) hk, (square p).lift_fst _ _ _, ?_⟩
    intro a ha
    apply (square p).hom_ext
    · exact ha.trans ((square p).lift_fst _ _ _).symm
    · exact toUnit_unique _ _

/-- The kernel structure map is the scheme pullback of the original group map. -/
theorem schemeSquare :
    IsPullback (inclusion p).hom.hom.left (group p).X.hom
      p.hom.hom.left (η[E.X]).left :=
  (square p).map (Over.forget (S))

instance finite [IsFinite p.hom.hom.left] : IsFinite (group p).X.hom :=
  MorphismProperty.of_isPullback (schemeSquare p) inferInstance
instance etale [Etale p.hom.hom.left] : Etale (group p).X.hom :=
  MorphismProperty.of_isPullback (schemeSquare p) inferInstance

/-- Representable kernel points are exactly the fibre above the group identity. -/
def pointsEquiv (T : Over S) :
    (T ⟶ (group p).X) ≃ {x : T ⟶ G.X // x ≫ p.hom.hom = 1} where
  toFun a := ⟨a ≫ (inclusion p).hom.hom, by
    have hp : (inclusion p).hom.hom ≫ p.hom.hom = 1 := (square p).w
    rw [Category.assoc, hp, MonObj.comp_one]⟩
  invFun x := (square p).lift x.val (toUnit _) x.property
  left_inv a := by
    apply (square p).hom_ext
    · exact (square p).lift_fst _ _ _
    · exact toUnit_unique _ _
  right_inv x := by
    apply Subtype.ext
    exact (square p).lift_fst _ _ _

end AlgebraicGeometry.Scheme.Group.Kernel
