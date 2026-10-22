/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.IdealPowers.IdealSheaf

/-! # Original generated ideals under extension of the affine base ring

These equalities identify the defining ideal after passage to a completion
without replacing the native ideal-sheaf model or its quotient units.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules
universe u
variable {R S : CommRingCat.{u}} (g : R ⟶ S) {X : Scheme.{u}}
  (f : X ⟶ Spec S)

/-- The scalar map of the original composite is extension along the given ring map. -/
theorem idealThickeningBaseScalar_comp_specMap :
    idealThickeningBaseScalar (f ≫ Spec.map g) =
      (idealThickeningBaseScalar f).comp g.hom := by
  change ((Scheme.ΓSpecIso R).inv ≫ (f ≫ Spec.map g).appTop).hom =
    (g ≫ (Scheme.ΓSpecIso S).inv ≫ f.appTop).hom
  simp only [Scheme.Hom.comp_appTop, ← Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality]

/-- The original ideal generated from the old base equals the ideal generated
from its actual extension in the new base ring. -/
theorem idealThickeningIdealSheaf_comp_specMap (I : Ideal R) :
    idealThickeningIdealSheaf (f ≫ Spec.map g) I =
      idealThickeningIdealSheaf f (I.map g.hom) := by
  simp only [idealThickeningIdealSheaf, idealThickeningBaseScalar_comp_specMap,
    Ideal.map_map]

/-- On the new affine base itself this is the native extended ideal. -/
theorem idealThickeningIdealSheaf_specMap (I : Ideal R) :
    idealThickeningIdealSheaf (Spec.map g) I =
      idealThickeningIdealSheaf (𝟙 (Spec S)) (I.map g.hom) := by
  simpa only [Category.id_comp] using
    idealThickeningIdealSheaf_comp_specMap g (𝟙 (Spec S)) I

end AlgebraicGeometry.Scheme.Modules
