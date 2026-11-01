/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.TripleCompositionFirst

/-! # Cartesian comparison squares from the actual triple-tower pullback isomorphisms -/

@[expose] public noncomputable section
open CategoryTheory Limits
universe u
namespace AlgebraicGeometry.Scheme.Hom.TripleCompactifiedComposition
variable {X Y Z W : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
  [QuasiCompact h] (T : TripleCompactifiedComposition f g h)

/-- The original intermediate pullback comparison is Cartesian over the unchanged total ambient. -/
theorem isPullback_leftIntermediateComparison :
    IsPullback T.leftIntermediateIso.hom T.innerToFirst T.leftOuter.middleOpen
      (𝟙 T.first.Xbar) := by
  exact @IsPullback.of_horiz_isIso Scheme inferInstance
    T.leftInner.composite.Xbar T.leftOuter.first.Xbar T.first.Xbar T.first.Xbar
    T.leftIntermediateIso.hom T.innerToFirst T.leftOuter.middleOpen (𝟙 T.first.Xbar)
    (inferInstanceAs (IsIso T.leftIntermediateIso.hom))
    (inferInstanceAs (IsIso (𝟙 T.first.Xbar)))
    ⟨T.leftIntermediateIso_hom_middleOpen.trans (Category.comp_id T.innerToFirst).symm⟩

variable [QuasiCompact g]

/-- The original first pullback comparison is Cartesian over the unchanged total ambient. -/
theorem isPullback_firstComparison :
    IsPullback T.firstIso.hom (T.leftInner.middleOpen ≫ T.innerToFirst)
      T.rightOuter.middleOpen (𝟙 T.first.Xbar) := by
  exact @IsPullback.of_horiz_isIso Scheme inferInstance
    T.leftInner.first.Xbar T.rightOuter.first.Xbar T.first.Xbar T.first.Xbar
    T.firstIso.hom (T.leftInner.middleOpen ≫ T.innerToFirst)
    T.rightOuter.middleOpen (𝟙 T.first.Xbar)
    (inferInstanceAs (IsIso T.firstIso.hom))
    (inferInstanceAs (IsIso (𝟙 T.first.Xbar)))
    ⟨T.firstIso_hom_middleOpen.trans
      (Category.comp_id (T.leftInner.middleOpen ≫ T.innerToFirst)).symm⟩

end AlgebraicGeometry.Scheme.Hom.TripleCompactifiedComposition
