/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.TransposeEvaluation

public import Aglib.AlgebraicGeometry.Modules.Invertible.PullbackTensor.Frame
public import Aglib.AlgebraicGeometry.Modules.Tensor.Monoidal.Symmetric


/-!
# Original coefficient in the native dual pullback frame

The pulled transpose has the original coefficient evaluated on the original
frame as its coordinate in the native dual frame. This identifies the
exceptional positive section's actual denominator coefficient without
assuming a normalized frame equation.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory BraidedCategory
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible

universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible

private theorem frame_pairing_swap {C : Type*} [Category C] [MonoidalCategory C]
    [BraidedCategory C] {D N : C} (s : 𝟙_ C ⟶ D) (e : 𝟙_ C ⟶ N) :
    s ≫ (λ_ D).inv ≫ (e ⊗ₘ 𝟙 D) ≫ (β_ N D).hom =
      e ≫ (λ_ N).inv ≫ (s ⊗ₘ 𝟙 N) := by
  simp only [leftUnitor_inv_naturality_assoc, ← id_tensorHom,
    tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id]
  rw [braiding_naturality, braiding_tensorUnit_left]
  have hu : (λ_ (𝟙_ C)).inv = (ρ_ (𝟙_ C)).inv :=
    congrArg Iso.inv (Iso.ext (unitors_equal (C := C)))
  simp only [← hu, Category.assoc, Iso.inv_hom_id_assoc, tensorHom_comp_tensorHom,
    Category.id_comp, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original pulled transpose has the original coefficient in the
native dual frame, with the original structural unit on both sides. -/
theorem dualPullbackFrame_transpose_coordinate {X Y : Scheme.{u}}
    (f : X ⟶ Y) (L : LineBundle Y)
    (e : SheafOfModules.unit X.ringCatSheaf ≅ (pullback f).obj L.val)
    (φ : L.val ⟶ SheafOfModules.unit Y.ringCatSheaf) :
    ((pullbackUnitIso f).inv ≫ (pullback f).map (InternalHom.transpose Y φ)) ≫
        (dualPullbackFrame f L e).inv =
      e.hom ≫ (pullback f).map φ ≫ (pullbackUnitIso f).hom := by
  let s := (pullbackUnitIso f).inv ≫ (pullback f).map (InternalHom.transpose Y φ)
  let D := (pullback f).obj (dualLineBundle Y L).val
  let N := (pullback f).obj L.val
  let ε := pullbackPairing f (dualEvaluationIso Y L).hom
  have hs : s ≫ (tensorSheafLeftUnit X D).inv ≫
      tensorSheafMap X e.hom (𝟙 D) ≫ (tensorSheafBraiding X N D).hom =
      e.hom ≫ (tensorSheafLeftUnit X N).inv ≫ tensorSheafMap X s (𝟙 N) :=
    frame_pairing_swap s e.hom
  have he : tensorSheafMap X s (𝟙 N) ≫ ε =
      (tensorSheafLeftUnit X N).hom ≫ (pullback f).map φ ≫ (pullbackUnitIso f).hom :=
    pullback_transpose_dualEvaluation f L φ
  change s ≫ (tensorSheafLeftUnit X D).inv ≫ tensorSheafMap X e.hom (𝟙 D) ≫
    (tensorSheafBraiding X N D).hom ≫ ε = _
  rw [reassoc_of% hs, he]
  simp only [Iso.inv_hom_id_assoc]

end AlgebraicGeometry.Scheme.Modules.Invertible
