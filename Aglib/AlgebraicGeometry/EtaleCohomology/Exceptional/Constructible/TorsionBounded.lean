/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Constructible.TorsionDerived
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Constructible.CohomologyProperty
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.Torsion
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.TorsionCompactificationAmplitude

/-! # Original bounded constructible torsion exceptional images

The actual internally torsion bounded constructible full subcategories retain
the original native objects and maps. Global constructibility and the geometric
upper amplitude supply both output properties without a common annihilator.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u wX wM wS
attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyRingStandard
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyAbStandard
  CategoryTheory.TorsionZMod.Ringed.ringWEqualsLocallyBijectiveStandard
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

/-- The intersection of the original bounded constructible and internal-torsion
properties, without choosing representatives or cohomological bounds. -/
def moduleBoundedConstructibleTorsionPlus (X : Scheme.{u})
    (Λ : Type (u + 1)) [Ring Λ]
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)] :
    ObjectProperty (DerivedCategory.Plus (ModuleSheaf X Λ)) :=
  fun K => moduleTorsionCohomologyPlus X Λ K ∧
    moduleBoundedConstructibleCohomologyPlus X Λ K

/-- The unchanged original-object inclusion into the native torsion range. -/
def moduleBoundedConstructibleTorsionInclusion (X : Scheme.{u})
    (Λ : Type (u + 1)) [Ring Λ]
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)] :
    (moduleBoundedConstructibleTorsionPlus X Λ).FullSubcategory ⥤
      (moduleTorsionCohomologyPlus X Λ).FullSubcategory :=
  ObjectProperty.lift (moduleTorsionCohomologyPlus X Λ)
    (moduleBoundedConstructibleTorsionPlus X Λ).ι (fun K => K.property.1)

variable {X S : Scheme.{u}} [IsNoetherian S]
    (f : X ⟶ S) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (Λ : Type (u + 1)) [Ring Λ] [IsNoetherianRing Λ]
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
    [HasDerivedCategory.{wM} (ModuleSheaf (moduleExceptionalCompactification f).Xbar Λ)]

/-- The actual exceptional image retains bounded constructible internal torsion
for the original coefficient complex over any left-Noetherian ring. -/
theorem moduleExceptional_torsion_boundedConstructible
    (K : (moduleTorsionCohomologyPlus X Λ).FullSubcategory)
    (hK : moduleBoundedConstructibleCohomologyPlus X Λ K.obj) :
    moduleBoundedConstructibleTorsionPlus S Λ
      ((moduleExceptionalDirectImagePlus f Λ).obj K) := by
  refine ⟨((moduleExceptionalDirectImagePlusTorsion f Λ).obj K).property,
    moduleExceptionalHomology_torsion_isConstructible f Λ K hK.1, ?_⟩
  obtain ⟨a, b, ha, hb⟩ := hK.2
  let : K.obj.IsGE a := ha
  let : K.obj.IsLE b := hb
  let C := (moduleExceptionalCompactification f).toCompactification
  obtain ⟨d, hd⟩ := exists_moduleCompactification_torsion_upperAmplitude C Λ
  refine ⟨a, (d : ℤ) + b, ?_, hd K.obj a b K.property ha hb⟩
  let : ((moduleDerivedLowerShriek C.j Λ).obj K.obj).IsGE a :=
    (moduleLowerShriek C.j Λ).rightDerivedFunctorPlus_isGE K.obj a
  change ((moduleDerivedDirectImage Λ C.p).obj
    ((moduleDerivedLowerShriek C.j Λ).obj K.obj)).IsGE a
  exact (moduleDirectImage C.p Λ).rightDerivedFunctorPlus_isGE _ a

/-- The original exceptional functor on bounded constructible internally torsion
full subcategories. All maps are the original exceptional maps. -/
def moduleExceptionalBoundedConstructibleTorsion :
    (moduleBoundedConstructibleTorsionPlus X Λ).FullSubcategory ⥤
      (moduleBoundedConstructibleTorsionPlus S Λ).FullSubcategory :=
  ObjectProperty.lift (moduleBoundedConstructibleTorsionPlus S Λ)
    (moduleBoundedConstructibleTorsionInclusion X Λ ⋙ moduleExceptionalDirectImagePlus f Λ)
    (fun K => moduleExceptional_torsion_boundedConstructible f Λ
      ((moduleBoundedConstructibleTorsionInclusion X Λ).obj K) K.property.2)

/-- Forgetting output properties recovers precisely the original functor. -/
def moduleExceptionalBoundedConstructibleTorsionForgetIso :
    moduleExceptionalBoundedConstructibleTorsion f Λ ⋙
        (moduleBoundedConstructibleTorsionPlus S Λ).ι ≅
      moduleBoundedConstructibleTorsionInclusion X Λ ⋙ moduleExceptionalDirectImagePlus f Λ :=
  Iso.refl _

end AlgebraicGeometry.Scheme.EtaleCohomology
