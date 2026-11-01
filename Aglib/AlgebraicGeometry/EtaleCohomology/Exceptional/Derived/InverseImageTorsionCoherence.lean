/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.InverseImageTorsion
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.Composition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.FullSubcategory

/-!
# Original inverse-image compositors on the native torsion subcategories

The original identity and composition isomorphisms are lifted without changing
their underlying maps. Models at all three schemes remain independent.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u wX wS wT
variable (Λ : Type (u + 1)) [Ring Λ]

section Identity
variable (X : Scheme.{u}) [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]

/-- The original inverse-image identity comparison on native torsion objects. -/
def moduleDerivedInverseImageTorsionIdIso :
    moduleDerivedInverseImageTorsion (𝟙 X) Λ ≅
      𝟭 (moduleTorsionCohomologyPlus X Λ).FullSubcategory :=
  (moduleTorsionCohomologyPlus X Λ).liftFunctorIso
    ((moduleTorsionCohomologyPlus X Λ).ι ⋙ moduleDerivedInverseImage Λ (𝟙 X))
    (moduleTorsionCohomologyPlus X Λ).ι
    (fun K => ((moduleDerivedInverseImageTorsion (𝟙 X) Λ).obj K).property)
    (fun K => K.property)
    (Functor.isoWhiskerLeft (moduleTorsionCohomologyPlus X Λ).ι
        (moduleDerivedInverseImageIdIso Λ X) ≪≫
      Functor.rightUnitor (moduleTorsionCohomologyPlus X Λ).ι)

end Identity

section Composition
variable {X S T : Scheme.{u}} (f : S ⟶ X) (g : T ⟶ S)
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]

/-- The original inverse-image compositor on native torsion objects. -/
def moduleDerivedInverseImageTorsionCompIso :
    moduleDerivedInverseImageTorsion (g ≫ f) Λ ≅
      moduleDerivedInverseImageTorsion f Λ ⋙ moduleDerivedInverseImageTorsion g Λ :=
  (moduleTorsionCohomologyPlus T Λ).liftFunctorIso
    ((moduleTorsionCohomologyPlus X Λ).ι ⋙ moduleDerivedInverseImage Λ (g ≫ f))
    ((moduleTorsionCohomologyPlus X Λ).ι ⋙
      (moduleDerivedInverseImage Λ f ⋙ moduleDerivedInverseImage Λ g))
    (fun K => ((moduleDerivedInverseImageTorsion (g ≫ f) Λ).obj K).property)
    (fun K => ((moduleDerivedInverseImageTorsion f Λ ⋙
      moduleDerivedInverseImageTorsion g Λ).obj K).property)
    (Functor.isoWhiskerLeft (moduleTorsionCohomologyPlus X Λ).ι
      (moduleDerivedInverseImageCompIso Λ f g))

/-- The lifted compositor has the unchanged original map. -/
theorem moduleDerivedInverseImageTorsionCompIso_hom_app
    (K : (moduleTorsionCohomologyPlus X Λ).FullSubcategory) :
    ((moduleDerivedInverseImageTorsionCompIso Λ f g).hom.app K).hom =
      (moduleDerivedInverseImageCompIso Λ f g).hom.app K.obj := rfl

end Composition
end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
