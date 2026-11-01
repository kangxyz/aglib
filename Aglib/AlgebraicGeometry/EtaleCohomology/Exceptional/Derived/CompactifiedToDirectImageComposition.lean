/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.OpenToDirectImageOverComposition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.DirectImageStructuralSquare
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.ToDirectImageNaturality
public import Aglib.CategoryTheory.Functor.ImageCompositionToTarget
public import Aglib.CategoryTheory.NatTrans.StructuralTriangleComponents

/-! # The original raw compactified-composition map preserves the same canonical comparison -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wM wY wL wN wZ
variable (Λ : Type (u + 1)) [Ring Λ] {X M Y L N Z : Scheme.{u}}
  (j : X ⟶ M) (p : M ⟶ Y) (i : Y ⟶ N) (q : N ⟶ Z)
  (k : M ⟶ L) (r : L ⟶ N) (l : X ⟶ L)
  (f : X ⟶ Y) (g : Y ⟶ Z)
  (hj : j ≫ k = l) (hf : j ≫ p = f) (hg : i ≫ q = g)
  (ht : l ≫ (r ≫ q) = f ≫ g) (sq : IsPullback p k i r)
  [IsOpenImmersion j] [IsOpenImmersion i] [IsOpenImmersion k] [IsOpenImmersion l]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wM} (ModuleSheaf M Λ)]
  [HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [HasDerivedCategory.{wL} (ModuleSheaf L Λ)]
  [HasDerivedCategory.{wN} (ModuleSheaf N Λ)]
  [HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)]

/-- All arrows are the original mixed mate, lower-shriek compositor and structural R*
comparisons. This equality is independent of the torsion invertibility argument. -/
theorem moduleCompactifiedComposition_toDirectImage :
    ImageCompositionToTargetEquation
      (moduleDerivedLowerShriekToDirectImage Λ j)
      (moduleDerivedLowerShriekToDirectImage Λ i)
      (moduleDerivedLowerShriekToDirectImage Λ l)
      (moduleProperOpenMate Λ i k p r sq)
      ((moduleDerivedLowerShriekCompIso Λ k j).symm ≪≫
        eqToIso (moduleDerivedLowerShriek_congr Λ hj))
      (moduleDerivedDirectImageCompIso Λ q r).symm
      (moduleDerivedDirectImageOverIso Λ (f ≫ g) (r ≫ q) l ht)
      (moduleDerivedDirectImageOverIso Λ g q i hg)
      (moduleDerivedDirectImageOverIso Λ f p j hf)
      (moduleDerivedDirectImageCompIso Λ g f).symm := by
  have hmid : k ≫ (r ≫ q) = p ≫ g := by
    rw [← Category.assoc, ← sq.w, Category.assoc, hg]
  have hjtotal : j ≫ (p ≫ g) = f ≫ g := by rw [← Category.assoc, hf]
  apply imageComposition_toTarget
    (moduleDerivedLowerShriekToDirectImage Λ j)
    (moduleDerivedLowerShriekToDirectImage Λ i)
    (moduleDerivedLowerShriekToDirectImage Λ k)
    (moduleDerivedLowerShriekToDirectImage Λ l)
    (moduleProperOpenMate Λ i k p r sq)
    ((moduleDerivedLowerShriekCompIso Λ k j).symm ≪≫
      eqToIso (moduleDerivedLowerShriek_congr Λ hj))
    (moduleDerivedDirectImageCompIso Λ q r).symm
    (moduleDerivedDirectImageSquareIso Λ r p i k sq.w)
    (moduleDerivedDirectImageOverIso Λ l k j hj)
    (moduleDerivedDirectImageOverIso Λ (f ≫ g) (r ≫ q) l ht)
    (moduleDerivedDirectImageOverIso Λ (p ≫ g) (r ≫ q) k hmid)
    (moduleDerivedDirectImageOverIso Λ (f ≫ g) (p ≫ g) j hjtotal)
    (moduleDerivedDirectImageOverIso Λ g q i hg)
    (moduleDerivedDirectImageOverIso Λ (p ≫ g) g p rfl)
    (moduleDerivedDirectImageOverIso Λ f p j hf)
    (moduleDerivedDirectImageCompIso Λ g f).symm
  · exact moduleDerivedLowerShriekToDirectImage_over_comp Λ j k l hj
  · exact moduleProperOpenMate_toDirectImageSquare Λ i k p r sq
  · have h := moduleDerivedDirectImageOverIso_square Λ k i p r (r ≫ q) q g (p ≫ g)
      sq.w rfl hg hmid rfl
    rw [moduleDerivedDirectImageOverIso_rfl Λ r q] at h
    exact h
  · exact structuralTriangle_components _ _ _ _
      (moduleDerivedDirectImageOverIso_triangle Λ (f ≫ g) j l k (p ≫ g) (r ≫ q)
        hj hmid hjtotal ht)
  · have h := structuralTriangle_components _ _ _ _
      (moduleDerivedDirectImageOverIso_triangle Λ (f ≫ g) j f p (p ≫ g) g
        hf rfl hjtotal rfl)
    simpa only [moduleDerivedDirectImageOverIso_rfl] using h
end AlgebraicGeometry.Scheme.EtaleCohomology
