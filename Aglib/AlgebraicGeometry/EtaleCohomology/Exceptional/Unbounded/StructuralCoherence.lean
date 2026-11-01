/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.StructuralComparisons
public import Aglib.CategoryTheory.Adjunction.ConjugateStructuralCoherence
public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.ExactCompositeUnit
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleInverseImageCoherence
/-! # Coherence of the original unbounded structural image comparisons
The exact inverse-image compositors retain their original localized coherence.
Conjugacy under the installed unbounded adjunctions transfers these equations to
the actual right-derived images, without any bounded-below argument.
-/
@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS wT wV
variable (Λ : Type (u + 1)) [Ring Λ]
/-- Equality transport has precisely the reversed original direct-image mate. -/
theorem conjugateEquiv_moduleUnboundedDerivedInverseImage_eqToHom
    {X S : Scheme.{u}} {f g : S ⟶ X} (e : f = g)
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)] :
    conjugateEquiv (moduleUnboundedDerivedAdjunction Λ g)
        (moduleUnboundedDerivedAdjunction Λ f)
        (eqToHom (congrArg (fun k : S ⟶ X => moduleUnboundedDerivedInverseImage Λ k) e)) =
      eqToHom (congrArg (fun k : S ⟶ X => moduleUnboundedDerivedDirectImage Λ k) e.symm) :=
  conjugateEquiv_eqToHom_of_family
    (fun k : S ⟶ X => moduleUnboundedDerivedInverseImage Λ k)
    (fun k : S ⟶ X => moduleUnboundedDerivedDirectImage Λ k)
    (fun k => moduleUnboundedDerivedAdjunction Λ k) e

/-- The original exact inverse-image compositor retains associativity after localization. -/
theorem moduleUnboundedDerivedInverseImageCompIso_assoc {X S T V : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) (h : V ⟶ T)
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
    [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]
    [HasDerivedCategory.{wV} (ModuleSheaf V Λ)] :
    moduleUnboundedDerivedInverseImageCompIso Λ f (h ≫ g) ≪≫
        Functor.isoWhiskerLeft (moduleUnboundedDerivedInverseImage Λ f)
        (moduleUnboundedDerivedInverseImageCompIso Λ g h) =
      eqToIso (congrArg (fun k : V ⟶ X => moduleUnboundedDerivedInverseImage Λ k)
        (Category.assoc h g f)) ≪≫
        moduleUnboundedDerivedInverseImageCompIso Λ (g ≫ f) h ≪≫
        Functor.isoWhiskerRight (moduleUnboundedDerivedInverseImageCompIso Λ f g)
        (moduleUnboundedDerivedInverseImage Λ h) ≪≫
        Functor.associator (moduleUnboundedDerivedInverseImage Λ f)
          (moduleUnboundedDerivedInverseImage Λ g) (moduleUnboundedDerivedInverseImage Λ h) := by
  have hnorm :=
    Functor.mapDerivedCategoryCompositeIso_assoc
      (moduleInverseImage f Λ) (moduleInverseImage g Λ) (moduleInverseImage h Λ)
      (moduleInverseImage (g ≫ f) Λ) (moduleInverseImage (h ≫ g) Λ)
      (moduleInverseImage ((h ≫ g) ≫ f) Λ)
      (moduleInverseImageCompIso Λ f g)
      (eqToIso (congrArg (fun k : V ⟶ X => moduleInverseImage k Λ)
        (Category.assoc h g f)) ≪≫ moduleInverseImageCompIso Λ (g ≫ f) h)
      (moduleInverseImageCompIso Λ f (h ≫ g)) (moduleInverseImageCompIso Λ g h)
      (moduleInverseImageCompIso_assoc Λ f g h)
  simp only [Functor.mapDerivedCategoryCompositeIso,
    Functor.mapDerivedCategoryOriginalIso_trans,
    Functor.mapDerivedCategoryOriginalIso_eqToIso, Iso.trans_assoc] at hnorm
  simpa only [moduleUnboundedDerivedInverseImageCompIso,
    Functor.mapDerivedCategoryOriginalIso, Iso.trans_assoc] using hnorm
/-- The original localized inverse-image compositor retains its unit normalization. -/
theorem moduleUnboundedDerivedInverseImageCompIso_comp_id {X S : Scheme.{u}} (f : S ⟶ X)
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)] :
    moduleUnboundedDerivedInverseImageCompIso Λ f (𝟙 S) ≪≫
        Functor.isoWhiskerLeft (moduleUnboundedDerivedInverseImage Λ f)
        (moduleUnboundedDerivedInverseImageIdIso Λ S) ≪≫
        Functor.rightUnitor (moduleUnboundedDerivedInverseImage Λ f) =
      eqToIso (congrArg (fun k : S ⟶ X => moduleUnboundedDerivedInverseImage Λ k)
        (Category.id_comp f)) := by
  have hnorm :=
    Functor.mapDerivedCategoryCompositeIso_right_unit
      (moduleInverseImage f Λ) (moduleInverseImage (𝟙 S) Λ) (moduleInverseImage (𝟙 S ≫ f) Λ)
      (moduleInverseImageCompIso Λ f (𝟙 S)) (moduleInverseImageIdIso Λ S)
      (eqToIso (congrArg (fun k : S ⟶ X => moduleInverseImage k Λ) (Category.id_comp f)))
      (moduleInverseImageCompIso_comp_id Λ f)
  simp only [Functor.mapDerivedCategoryCompositeIso,
    Functor.mapDerivedCategoryOriginalIso_eqToIso] at hnorm
  simpa only [moduleUnboundedDerivedInverseImageCompIso,
    moduleUnboundedDerivedInverseImageIdIso, Functor.mapDerivedCategoryOriginalIso] using hnorm
/-- The original localized inverse-image compositor retains its unit normalization. -/
theorem moduleUnboundedDerivedInverseImageCompIso_id_comp {X S : Scheme.{u}} (f : S ⟶ X)
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)] :
    moduleUnboundedDerivedInverseImageCompIso Λ (𝟙 X) f ≪≫
        Functor.isoWhiskerRight (moduleUnboundedDerivedInverseImageIdIso Λ X)
        (moduleUnboundedDerivedInverseImage Λ f) ≪≫
        Functor.leftUnitor (moduleUnboundedDerivedInverseImage Λ f) =
      eqToIso (congrArg (fun k : S ⟶ X => moduleUnboundedDerivedInverseImage Λ k)
        (Category.comp_id f)) := by
  have hnorm :=
    Functor.mapDerivedCategoryCompositeIso_left_unit
      (moduleInverseImage (𝟙 X) Λ) (moduleInverseImage f Λ) (moduleInverseImage (f ≫ 𝟙 X) Λ)
      (moduleInverseImageCompIso Λ (𝟙 X) f) (moduleInverseImageIdIso Λ X)
      (eqToIso (congrArg (fun k : S ⟶ X => moduleInverseImage k Λ) (Category.comp_id f)))
      (moduleInverseImageCompIso_id_comp Λ f)
  simp only [Functor.mapDerivedCategoryCompositeIso,
    Functor.mapDerivedCategoryOriginalIso_eqToIso] at hnorm
  simpa only [moduleUnboundedDerivedInverseImageCompIso,
    moduleUnboundedDerivedInverseImageIdIso, Functor.mapDerivedCategoryOriginalIso] using hnorm
/-- The actual unbounded direct-image compositor retains the original unit. -/
theorem moduleUnboundedDerivedDirectImageCompIso_comp_id {X S : Scheme.{u}} (f : S ⟶ X)
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)] :
    moduleUnboundedDerivedDirectImageCompIso Λ f (𝟙 S) ≪≫
        Functor.isoWhiskerRight (moduleUnboundedDerivedDirectImageIdIso Λ S)
          (moduleUnboundedDerivedDirectImage Λ f) ≪≫
        Functor.leftUnitor (moduleUnboundedDerivedDirectImage Λ f) =
      eqToIso (congrArg (fun k : S ⟶ X => moduleUnboundedDerivedDirectImage Λ k)
        (Category.id_comp f)) :=
  conjugateStructural_right_unit
    (moduleUnboundedDerivedAdjunction Λ f)
    (moduleUnboundedDerivedAdjunction Λ (𝟙 S))
    (moduleUnboundedDerivedAdjunction Λ (𝟙 S ≫ f))
    (moduleUnboundedDerivedInverseImageCompIso Λ f (𝟙 S))
    (moduleUnboundedDerivedDirectImageCompIso Λ f (𝟙 S))
    (moduleUnboundedDerivedInverseImageIdIso Λ S)
    (moduleUnboundedDerivedDirectImageIdIso Λ S)
    (eqToIso (congrArg (fun k : S ⟶ X => moduleUnboundedDerivedInverseImage Λ k)
      (Category.id_comp f)))
    (eqToIso (congrArg (fun k : S ⟶ X => moduleUnboundedDerivedDirectImage Λ k)
      (Category.id_comp f)))
    (conjugateEquiv_moduleUnboundedDerivedInverseImageCompIso_hom Λ f (𝟙 S))
    (conjugateEquiv_moduleUnboundedDerivedInverseImageIdIso_hom Λ S)
    (conjugateEquiv_moduleUnboundedDerivedInverseImage_eqToHom Λ (Category.id_comp f))
    (moduleUnboundedDerivedInverseImageCompIso_comp_id Λ f)

/-- The actual unbounded direct-image compositor retains the original unit. -/
theorem moduleUnboundedDerivedDirectImageCompIso_id_comp {X S : Scheme.{u}} (f : S ⟶ X)
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)] :
    moduleUnboundedDerivedDirectImageCompIso Λ (𝟙 X) f ≪≫
        Functor.isoWhiskerLeft (moduleUnboundedDerivedDirectImage Λ f)
          (moduleUnboundedDerivedDirectImageIdIso Λ X) ≪≫
        Functor.rightUnitor (moduleUnboundedDerivedDirectImage Λ f) =
      eqToIso (congrArg (fun k : S ⟶ X => moduleUnboundedDerivedDirectImage Λ k)
        (Category.comp_id f)) :=
  conjugateStructural_left_unit
    (moduleUnboundedDerivedAdjunction Λ f)
    (moduleUnboundedDerivedAdjunction Λ (𝟙 X))
    (moduleUnboundedDerivedAdjunction Λ (f ≫ 𝟙 X))
    (moduleUnboundedDerivedInverseImageCompIso Λ (𝟙 X) f)
    (moduleUnboundedDerivedDirectImageCompIso Λ (𝟙 X) f)
    (moduleUnboundedDerivedInverseImageIdIso Λ X)
    (moduleUnboundedDerivedDirectImageIdIso Λ X)
    (eqToIso (congrArg (fun k : S ⟶ X => moduleUnboundedDerivedInverseImage Λ k)
      (Category.comp_id f)))
    (eqToIso (congrArg (fun k : S ⟶ X => moduleUnboundedDerivedDirectImage Λ k)
      (Category.comp_id f)))
    (conjugateEquiv_moduleUnboundedDerivedInverseImageCompIso_hom Λ (𝟙 X) f)
    (conjugateEquiv_moduleUnboundedDerivedInverseImageIdIso_hom Λ X)
    (conjugateEquiv_moduleUnboundedDerivedInverseImage_eqToHom Λ (Category.comp_id f))
    (moduleUnboundedDerivedInverseImageCompIso_id_comp Λ f)

/-- The actual right-derived structural compositors satisfy original associativity. -/
theorem moduleUnboundedDerivedDirectImageCompIso_assoc {X S T V : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) (h : V ⟶ T)
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
    [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]
    [HasDerivedCategory.{wV} (ModuleSheaf V Λ)] :
    moduleUnboundedDerivedDirectImageCompIso Λ (g ≫ f) h ≪≫
        Functor.isoWhiskerLeft (moduleUnboundedDerivedDirectImage Λ h)
          (moduleUnboundedDerivedDirectImageCompIso Λ f g) =
      eqToIso (congrArg (fun k : V ⟶ X => moduleUnboundedDerivedDirectImage Λ k)
          (Category.assoc h g f).symm) ≪≫
        moduleUnboundedDerivedDirectImageCompIso Λ f (h ≫ g) ≪≫
        Functor.isoWhiskerRight (moduleUnboundedDerivedDirectImageCompIso Λ g h)
          (moduleUnboundedDerivedDirectImage Λ f) ≪≫
        Functor.associator (moduleUnboundedDerivedDirectImage Λ h)
          (moduleUnboundedDerivedDirectImage Λ g) (moduleUnboundedDerivedDirectImage Λ f) :=
  conjugateStructural_assoc
    (moduleUnboundedDerivedAdjunction Λ f)
    (moduleUnboundedDerivedAdjunction Λ g)
    (moduleUnboundedDerivedAdjunction Λ h)
    (moduleUnboundedDerivedAdjunction Λ (g ≫ f))
    (moduleUnboundedDerivedAdjunction Λ (h ≫ g))
    (moduleUnboundedDerivedAdjunction Λ ((h ≫ g) ≫ f))
    (moduleUnboundedDerivedAdjunction Λ (h ≫ (g ≫ f)))
    (moduleUnboundedDerivedInverseImageCompIso Λ f g)
    (moduleUnboundedDerivedInverseImageCompIso Λ g h)
    (moduleUnboundedDerivedInverseImageCompIso Λ f (h ≫ g))
    (moduleUnboundedDerivedInverseImageCompIso Λ (g ≫ f) h)
    (moduleUnboundedDerivedDirectImageCompIso Λ f g)
    (moduleUnboundedDerivedDirectImageCompIso Λ g h)
    (moduleUnboundedDerivedDirectImageCompIso Λ f (h ≫ g))
    (moduleUnboundedDerivedDirectImageCompIso Λ (g ≫ f) h)
    (eqToIso (congrArg (fun k : V ⟶ X => moduleUnboundedDerivedInverseImage Λ k)
      (Category.assoc h g f)))
    (eqToIso (congrArg (fun k : V ⟶ X => moduleUnboundedDerivedDirectImage Λ k)
      (Category.assoc h g f).symm))
    (conjugateEquiv_moduleUnboundedDerivedInverseImageCompIso_hom Λ f g)
    (conjugateEquiv_moduleUnboundedDerivedInverseImageCompIso_hom Λ g h)
    (conjugateEquiv_moduleUnboundedDerivedInverseImageCompIso_hom Λ f (h ≫ g))
    (conjugateEquiv_moduleUnboundedDerivedInverseImageCompIso_hom Λ (g ≫ f) h)
    (conjugateEquiv_moduleUnboundedDerivedInverseImage_eqToHom Λ (Category.assoc h g f))
    (moduleUnboundedDerivedInverseImageCompIso_assoc Λ f g h)

end AlgebraicGeometry.Scheme.EtaleCohomology
