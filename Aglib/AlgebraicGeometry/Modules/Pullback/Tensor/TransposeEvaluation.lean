/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Pairing
public import Aglib.AlgebraicGeometry.Modules.InternalHom.HomSection

/-!
# Original pulled-back transpose evaluation

The transpose of an original line-to-structure coefficient is pulled back
with the original structural unit. Evaluation against the original pulled
line recovers exactly the original coefficient, through the canonical
unit and tensor comparisons. No normalized trace or frame equation is an
input. This is the unit compatibility needed by the one-pole chart frame.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u

namespace AlgebraicGeometry.Scheme.Modules

private theorem evaluation_comparison
    {C : Type*} [Category C] {A B D E F G H J : C}
    (a : A ⟶ B) (b : B ⟶ D) (p : B ⟶ E) (q : D ⟶ F)
    (t : E ⟶ F) (ε : F ⟶ G) (l : E ⟶ H) (v : H ⟶ G)
    (u : G ⟶ J) (h : A ⟶ D) (k : A ⟶ H)
    (hh : h = a ≫ b) (hn : b ≫ q = p ≫ t)
    (he : t ≫ ε = l ≫ v) (hu : a ≫ p ≫ l = k) :
    h ≫ q ≫ ε ≫ u = k ≫ v ≫ u := by
  rw [hh, Category.assoc, ← Category.assoc b q, hn]
  simp only [Category.assoc]
  rw [← Category.assoc t ε, he]
  simp only [Category.assoc]
  rw [← reassoc_of% hu]

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (L : LineBundle Y)
  (φ : L.val ⟶ SheafOfModules.unit Y.ringCatSheaf)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Original transpose evaluation survives pullback with the original unit. -/
theorem pullback_transpose_dualEvaluation :
    tensorSheafMap X
        ((pullbackUnitIso f).inv ≫ (pullback f).map (InternalHom.transpose Y φ))
        (𝟙 ((pullback f).obj L.val)) ≫
      pullbackPairing f (dualEvaluationIso Y L).hom =
    (tensorSheafLeftUnit X ((pullback f).obj L.val)).hom ≫
      (pullback f).map φ ≫ (pullbackUnitIso f).hom := by
  let Q := pullbackTensorMapIso f (SheafOfModules.unit Y.ringCatSheaf) L.val ≪≫
    tensorSheafIso X (pullbackUnitIso f) (Iso.refl ((pullback f).obj L.val))
  have hu : Q.inv ≫ (pullback f).map (tensorSheafLeftUnit Y L.val).hom =
      (tensorSheafLeftUnit X ((pullback f).obj L.val)).hom := by
    rw [Iso.inv_comp_eq]
    exact (pullbackTensorMap_leftUnit f L.val).symm
  have hn := (pullbackTensorMapIso_inv_naturality f
    (InternalHom.transpose Y φ) (𝟙 L.val)).trans
      (congrArg (fun v => tensorSheafMap X
        ((pullback f).map (InternalHom.transpose Y φ)) v ≫
          (pullbackTensorMapIso f (dualLineBundle Y L).val L.val).inv)
        ((pullback f).map_id L.val))
  have hs : tensorSheafMap X
      ((pullbackUnitIso f).inv ≫ (pullback f).map (InternalHom.transpose Y φ))
      (𝟙 ((pullback f).obj L.val)) =
      tensorSheafMap X (pullbackUnitIso f).inv (𝟙 ((pullback f).obj L.val)) ≫
        tensorSheafMap X ((pullback f).map (InternalHom.transpose Y φ))
          (𝟙 ((pullback f).obj L.val)) := by
    rw [tensorSheafMap_comp, Category.id_comp]
  have he := ((pullback f).map_comp
      (tensorSheafMap Y (InternalHom.transpose Y φ) (𝟙 L.val))
      (dualEvaluationIso Y L).hom).symm.trans
    ((congrArg (fun z => (pullback f).map z)
      (InternalHom.transpose_dualEvaluation Y L φ)).trans
      ((pullback f).map_comp (tensorSheafLeftUnit Y L.val).hom φ))
  have hu' : tensorSheafMap X (pullbackUnitIso f).inv
        (𝟙 ((pullback f).obj L.val)) ≫
      (pullbackTensorMapIso f (SheafOfModules.unit Y.ringCatSheaf) L.val).inv ≫
        (pullback f).map (tensorSheafLeftUnit Y L.val).hom =
      (tensorSheafLeftUnit X ((pullback f).obj L.val)).hom :=
    (Category.assoc _ _ _).symm.trans hu
  exact evaluation_comparison _ _ _ _ _ _ _ _ _ _ _ hs hn.symm he hu'

end AlgebraicGeometry.Scheme.Modules
