/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramRelativeTail
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Opposites

/-! # The original inverse scheme limit remains a limit on every relative tail -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u uI vI
variable {I : Type uI} [Category.{vI} I] [IsFiltered I]
  (X : I ⥤ Scheme.{u}ᵒᵖ) (c : Cocone X) (hc : IsColimit c) (i : I)

/-- Forgetting the actual relative tail yields the original final under-tail. -/
def isColimitRelativeSchemeTailUnderlying :
    IsColimit ((Over.forget (X.obj i).unop).op.mapCocone
      (relativeSchemeTailCocone X c i)) :=
  (Functor.Final.isColimitWhiskerEquiv (Under.forget i) c).symm hc

/-- The native limit certificate required by fixed-coefficient scheme-tail continuity. -/
def isLimitRelativeSchemeTailUnderlying :
    IsLimit ((Over.forget (X.obj i).unop).mapCone (relativeSchemeTailCone X c i)) :=
  isLimitConeLeftOpOfCocone _ (isColimitRelativeSchemeTailUnderlying X c hc i)

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
