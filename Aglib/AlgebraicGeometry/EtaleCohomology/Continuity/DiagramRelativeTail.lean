/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramConeSquares
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.SchemeSystemColimits

/-! # The actual relative scheme tail and its original cone legs -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u uI vI
attribute [local instance] hasSheafifyLarge
variable {I : Type uI} [Category.{vI} I] (X : I ⥤ Scheme.{u}ᵒᵖ) (c : Cocone X)

/-- The native relative tail, using the library's under/over opposite equivalence. -/
def relativeSchemeTail (i : I) : Under i ⥤ (Over (X.obj i).unop)ᵒᵖ :=
  Under.post X ⋙ (Under.opEquivOpOver (X.obj i).unop).functor

/-- The original cone to the inverse system gives the original relative tail cocone. -/
def relativeSchemeTailCocone (i : I) : Cocone (relativeSchemeTail X i) where
  pt := op (Over.mk (c.ι.app i).unop)
  ι.app a := (Over.homMk (c.ι.app a.right).unop (coneSquare X c a.hom)).op
  ι.naturality a b m := by
    apply Quiver.Hom.unop_inj
    apply Over.OverMorphism.ext
    exact coneSquare X c m.right

/-- The native cone form expected by the fixed-coefficient scheme-limit theorem. -/
def relativeSchemeTailCone (i : I) : Cone (relativeSchemeTail X i).leftOp :=
  coneLeftOpOfCocone (relativeSchemeTailCocone X c i)

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
