/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.OpenToDirectImageOverComposition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.DirectImageStructuralSquare
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ToDirectImageNaturality
public import Aglib.CategoryTheory.Functor.ImageCompositionToTargetFaces
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
theorem moduleUnboundedCompactifiedComposition_toDirectImage :
    ImageCompositionToTargetEquation
      (moduleUnboundedLowerShriekToDirectImage Λ j)
      (moduleUnboundedLowerShriekToDirectImage Λ i)
      (moduleUnboundedLowerShriekToDirectImage Λ l)
      (moduleUnboundedProperOpenMate p k i r sq Λ)
      ((moduleUnboundedDerivedLowerShriekCompIso Λ k j).symm ≪≫
        eqToIso (moduleUnboundedDerivedLowerShriek_congr Λ hj))
      (moduleUnboundedDerivedDirectImageCompIso Λ q r).symm
      (moduleUnboundedDerivedDirectImageOverIso Λ (f ≫ g) (r ≫ q) l ht)
      (moduleUnboundedDerivedDirectImageOverIso Λ g q i hg)
      (moduleUnboundedDerivedDirectImageOverIso Λ f p j hf)
      (moduleUnboundedDerivedDirectImageCompIso Λ g f).symm := by
  have hmid : k ≫ (r ≫ q) = p ≫ g := by
    rw [← Category.assoc, ← sq.w, Category.assoc, hg]
  have hjtotal : j ≫ (p ≫ g) = f ≫ g := by rw [← Category.assoc, hf]
  apply imageComposition_toTarget_faces
    (moduleUnboundedLowerShriekToDirectImage Λ j)
    (moduleUnboundedLowerShriekToDirectImage Λ i)
    (moduleUnboundedLowerShriekToDirectImage Λ k)
    (moduleUnboundedLowerShriekToDirectImage Λ l)
    (moduleUnboundedProperOpenMate p k i r sq Λ)
    ((moduleUnboundedDerivedLowerShriekCompIso Λ k j).symm ≪≫
      eqToIso (moduleUnboundedDerivedLowerShriek_congr Λ hj))
    (moduleUnboundedDerivedDirectImageCompIso Λ q r).symm
    (moduleUnboundedDerivedDirectImageSquareIso Λ r p i k sq.w)
    (moduleUnboundedDerivedDirectImageOverIso Λ l k j hj)
    (moduleUnboundedDerivedDirectImageOverIso Λ (f ≫ g) (r ≫ q) l ht)
    (moduleUnboundedDerivedDirectImageOverIso Λ (p ≫ g) (r ≫ q) k hmid)
    (moduleUnboundedDerivedDirectImageOverIso Λ (f ≫ g) (p ≫ g) j hjtotal)
    (moduleUnboundedDerivedDirectImageOverIso Λ g q i hg)
    (moduleUnboundedDerivedDirectImageOverIso Λ (p ≫ g) g p rfl)
    (moduleUnboundedDerivedDirectImageOverIso Λ f p j hf)
    (moduleUnboundedDerivedDirectImageCompIso Λ g f).symm
    (moduleUnboundedDerivedDirectImageOverIso Λ (r ≫ q) q r rfl)
    (moduleUnboundedDerivedDirectImageOverIso Λ (f ≫ g) g f rfl)
    (moduleUnboundedDerivedDirectImageOverIso_rfl Λ r q)
    (moduleUnboundedDerivedDirectImageOverIso_rfl Λ f g)
  · exact moduleUnboundedLowerShriekToDirectImage_over_comp Λ j k l hj
  · exact moduleUnboundedProperOpenMate_toDirectImageSquare p k i r sq Λ
  · exact moduleUnboundedDerivedDirectImageOverIso_square
      Λ k i p r (r ≫ q) q g (p ≫ g) sq.w rfl hg hmid rfl
  · exact moduleUnboundedDerivedDirectImageOverIso_triangle
      Λ (f ≫ g) j l k (p ≫ g) (r ≫ q) hj hmid hjtotal ht
  · exact moduleUnboundedDerivedDirectImageOverIso_triangle
      Λ (f ≫ g) j f p (p ≫ g) g hf rfl hjtotal rfl
end AlgebraicGeometry.Scheme.EtaleCohomology
