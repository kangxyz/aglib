/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.InverseImageTorsionCoherence
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.OpenComparisonCube

/-! # Native torsion inclusions retain the original inverse-image compositor -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u wX wS wT
variable (Λ : Type (u + 1)) [Ring Λ]
  {X S T : Scheme.{u}} (f : S ⟶ X) (g : T ⟶ S)
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]

/-- Forgetting native torsion properties commutes with the unchanged original
inverse-image compositor, as a whole open-comparison pasting equation. -/
theorem moduleDerivedInverseImageTorsionForgetIso_pasting :
    LeftComparisonPastingEquation
      (moduleDerivedInverseImageTorsionForgetIso f Λ).symm
      (moduleDerivedInverseImageTorsionForgetIso g Λ).symm
      (moduleDerivedInverseImageTorsionForgetIso (g ≫ f) Λ).symm
      (moduleDerivedInverseImageTorsionCompIso Λ f g)
      (moduleDerivedInverseImageCompIso Λ f g) := by
  intro K
  change (moduleDerivedInverseImageCompIso Λ f g).hom.app K.obj ≫
      (moduleDerivedInverseImage Λ g).map (𝟙 _) ≫ 𝟙 _ =
    (𝟙 _) ≫ (moduleDerivedInverseImageCompIso Λ f g).hom.app K.obj
  simp only [Category.comp_id, Category.id_comp]
  exact (congrArg (fun z => (moduleDerivedInverseImageCompIso Λ f g).hom.app K.obj ≫ z)
    ((moduleDerivedInverseImage Λ g).map_id
      ((moduleDerivedInverseImage Λ f).obj K.obj))).trans
    (Category.comp_id ((moduleDerivedInverseImageCompIso Λ f g).hom.app K.obj))

end AlgebraicGeometry.Scheme.EtaleCohomology
