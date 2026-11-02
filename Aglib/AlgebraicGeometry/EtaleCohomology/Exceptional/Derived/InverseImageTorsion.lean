/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Torsion.InverseImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.UnderlyingTorsion

/-!
# Original inverse image on the torsion derived range

Exact inverse image and the original homology comparisons preserve internal
locally torsion cohomology along every scheme morphism. Scalar forgetting
transports the statement to genuine module sheaves. Restriction to the native
torsion full subcategories retains the original functor and all its maps.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u wX wS wMX wMS

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (f : X ⟶ S)

section Abelian

variable [HasDerivedCategory.{wX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{wS} (AbelianSheaf.{u, u + 1} S)]

/-- Original derived inverse image preserves internally torsion homology along
an arbitrary scheme morphism, through the exact homology comparison. -/
theorem derivedInverseImage_isTorsion_homology
    (K : DerivedCategory.Plus (AbelianSheaf.{u, u + 1} S))
    (hK : ∀ i : ℤ, IsTorsion S
      ((DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S) i).obj K))
    (n : ℤ) : IsTorsion X
      ((DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} X) n).obj
        ((derivedInverseImage f).obj K)) := by
  let e := (Functor.rightDerivedFunctorPlusHomologyIso (inverseImage f) n).app K
  exact ((hK n).inverseImage f).of_mono e.hom

end Abelian

namespace Coefficients

variable (Λ : Type (u + 1)) [Ring Λ]

/-- The original ordinary inverse image of genuine module sheaves preserves
internal torsion, via the existing scalar-forgetting isomorphism. -/
theorem moduleInverseImage_preservesTorsion
    (M : ModuleSheaf S Λ) (hM : moduleIsTorsion S Λ M) :
    moduleIsTorsion X Λ ((moduleInverseImage f Λ).obj M) := by
  let e := (moduleInverseImageUnderlyingIso Λ f).app M
  let mono : Mono e.hom := @IsIso.mono_of_iso _ _ _ _ _ e.isIso_hom
  exact @Sheaf.IsTorsion.of_mono _ _ _ _ _ _
    (IsTorsion.inverseImage f hM) e.hom mono

variable [HasDerivedCategory.{wMX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wMS} (ModuleSheaf S Λ)]

/-- The original module-derived inverse image preserves internal torsion in every
homology degree, using only its actual source and target module realizations. -/
theorem moduleDerivedInverseImage_preservesTorsionCohomology
    (K : DerivedCategory.Plus (ModuleSheaf S Λ))
    (hK : moduleTorsionCohomologyPlus S Λ K) :
    moduleTorsionCohomologyPlus X Λ ((moduleDerivedInverseImage Λ f).obj K) := by
  intro n
  exact moduleIsTorsion_of_iso X Λ
    (((moduleInverseImage f Λ).rightDerivedFunctorPlusHomologyIso n).app K)
    (moduleInverseImage_preservesTorsion f Λ _ (hK n))

/-- Original derived inverse image restricted to the native torsion source and target. -/
def moduleDerivedInverseImageTorsion :
    (moduleTorsionCohomologyPlus S Λ).FullSubcategory ⥤
      (moduleTorsionCohomologyPlus X Λ).FullSubcategory :=
  (moduleTorsionCohomologyPlus X Λ).lift
    ((moduleTorsionCohomologyPlus S Λ).ι ⋙ moduleDerivedInverseImage Λ f)
    (fun K => moduleDerivedInverseImage_preservesTorsionCohomology f Λ K.obj K.property)

/-- Forgetting the target torsion property recovers exactly the original inverse image. -/
def moduleDerivedInverseImageTorsionForgetIso :
    moduleDerivedInverseImageTorsion f Λ ⋙ (moduleTorsionCohomologyPlus X Λ).ι ≅
      (moduleTorsionCohomologyPlus S Λ).ι ⋙ moduleDerivedInverseImage Λ f :=
  Iso.refl _

/-- The restricted inverse image has exactly the original map on native underlying objects. -/
theorem moduleDerivedInverseImageTorsion_map
    {K L : (moduleTorsionCohomologyPlus S Λ).FullSubcategory} (φ : K ⟶ L) :
    ((moduleDerivedInverseImageTorsion f Λ).map φ).hom =
      (moduleDerivedInverseImage Λ f).map φ.hom := rfl

end Coefficients

end AlgebraicGeometry.Scheme.EtaleCohomology
