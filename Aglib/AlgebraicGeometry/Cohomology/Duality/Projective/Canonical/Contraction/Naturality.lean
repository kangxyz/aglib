/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Contraction

/-!
# Naturality of the original normal determinant contraction

The original tensor associator and dual evaluation are natural transformations.
Consequently an actual commuting normal-first determinant square gives the
same commuting square after contraction by the original inverse normal line.
-/

@[expose] public section
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- Contracting an actual normal-first determinant square preserves its actual arrows. -/
theorem normalDeterminantContractionIso_naturality {Z : Scheme.{u}} (C : LineBundle Z)
    (eC : C.val ≅ SheafOfModules.unit Z.ringCatSheaf)
    (eD : (dualLineBundle Z C).val ≅ SheafOfModules.unit Z.ringCatSheaf)
    {Q Q' P P' : Z.Modules}
    (Δ : tensorSheaf Z C.val Q ≅ P) (Δ' : tensorSheaf Z C.val Q' ≅ P')
    (a : Q ⟶ Q') (b : P ⟶ P')
    (h : Δ.hom ≫ b = (moduleTensorLeftFunctor Z C.val).map a ≫ Δ'.hom) :
    (moduleTensorLeftFunctor Z (dualLineBundle Z C).val).map b ≫
        (normalDeterminantContractionIso C eC eD Δ').hom =
      (normalDeterminantContractionIso C eC eD Δ).hom ≫ a := by
  let T := moduleTensorLeftFunctor Z (dualLineBundle Z C).val
  let S := moduleTensorLeftFunctor Z C.val
  let K : S ⋙ T ⟶ 𝟭 Z.Modules :=
    (normalDeterminantTensorAssociator C eC eD).hom ≫
      tensorToUnit (dualEvaluationIso Z C).hom
  have hi : b ≫ Δ'.inv = Δ.inv ≫ S.map a := by
    apply (cancel_epi Δ.hom).mp
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
      Category.comp_id] using congrArg (fun f => f ≫ Δ'.inv) h
  have hK := K.naturality a
  change T.map b ≫ T.map Δ'.inv ≫ K.app Q' = T.map Δ.inv ≫ K.app Q ≫ a
  rw [← T.map_comp_assoc, hi, T.map_comp, Category.assoc]
  exact congrArg (fun f => T.map Δ.inv ≫ f) hK

end AlgebraicGeometry.Scheme.Modules
