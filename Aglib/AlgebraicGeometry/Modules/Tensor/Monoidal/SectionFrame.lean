/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Pairing
public import Aglib.AlgebraicGeometry.Modules.Tensor.Section


/-!
# Original section insertion in a tensor frame

The original positive-section tensor transformation is scalar insertion
followed by the actual tensor frame when the original section has that
frame coefficient. This is a native tensor/unitor identity; the exceptional
coefficient itself is supplied by the proved original ideal-frame equation.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

private theorem unit_frame_composite {C : Type*} [Category C] {A B D E : C}
    (u : A ≅ B) (a : A ⟶ A) (b : A ⟶ D) (c : D ⟶ E) :
    (u.inv ≫ a ≫ u.hom) ≫ (u.inv ≫ b ≫ c) = u.inv ≫ (a ≫ b) ≫ c := by
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual positive-section insertion, in the actual tensor frame,
retains exactly the supplied original scalar coefficient. -/
theorem positiveSection_tensorFrame {X : Scheme.{u}} (M N : X.Modules)
    (e : SheafOfModules.unit X.ringCatSheaf ≅ N)
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ N)
    (r : (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶
      SheafOfModules.unit X.ringCatSheaf) (hs : s = r ≫ e.hom) :
    (positiveCartierTensorSection X N s).app M ≫ (tensorSheafBraiding X N M).hom =
      ((tensorSheafLeftUnit X M).inv ≫ (moduleTensorCoefficientMap X r).app M ≫
        (tensorSheafLeftUnit X M).hom) ≫
      ((tensorSheafLeftUnit X M).symm ≪≫ tensorSheafIso X e (Iso.refl M) ≪≫
        tensorSheafBraiding X N M).hom := by
  have ht : tensorSheafMap X r (𝟙 M) ≫ tensorSheafMap X e.hom (𝟙 M) =
      tensorSheafMap X s (𝟙 M) := by
    rw [tensorSheafMap_comp, Category.id_comp, ← hs]
  have hc := unit_frame_composite (tensorSheafLeftUnit X M)
    (tensorSheafMap X r (𝟙 M)) (tensorSheafMap X e.hom (𝟙 M))
    (tensorSheafBraiding X N M).hom
  exact (congrArg (fun t => (tensorSheafLeftUnit X M).inv ≫ t ≫
    (tensorSheafBraiding X N M).hom) ht.symm).trans hc.symm

end AlgebraicGeometry.Scheme.Modules
