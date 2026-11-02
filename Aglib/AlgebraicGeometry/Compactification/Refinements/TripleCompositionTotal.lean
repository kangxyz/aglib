/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.TripleComposition
public import Aglib.AlgebraicGeometry.Compactification.Refinements.SourceIso

/-! # Original total target transport for triple composition -/

@[expose] public noncomputable section
open CategoryTheory
universe u
namespace AlgebraicGeometry.Scheme.Hom.TripleCompactifiedComposition

variable {X Y Z W : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
  (T : TripleCompactifiedComposition f g h)

/-- The right-associated total target transported by the literal identity of the source. -/
def rightTotalTransport : DenseCompactification ((f ≫ g) ≫ h) :=
  DenseCompactification.ofSourceIso ((f ≫ g) ≫ h) (Iso.refl X)
    (by simpa only [Iso.refl_hom, Category.id_comp] using (Category.assoc f g h).symm)
    T.rightOuter.composite

/-- The total comparison is the original identity of the top ambient scheme. -/
def totalRefinement : T.leftOuter.composite ⟶ T.rightTotalTransport where
  hom := 𝟙 T.first.Xbar
  isProper_hom := inferInstanceAs (IsProper (𝟙 T.first.Xbar))
  open_fac := by
    change T.first.j ≫ 𝟙 T.first.Xbar = (𝟙 X) ≫ T.first.j
    simp only [Category.comp_id, Category.id_comp]
  base_fac := by
    change (𝟙 T.first.Xbar) ≫ (T.first.p ≫ T.middle.p ≫ T.last.p) =
      (T.first.p ≫ T.middle.p) ≫ T.last.p
    simp only [Category.id_comp, Category.assoc]

end AlgebraicGeometry.Scheme.Hom.TripleCompactifiedComposition
