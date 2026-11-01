/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.DirectImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.FullSubcategory
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.TorsionPreservation

/-!
# The actual torsion-valued bounded-below exceptional functor

Original open extension and qcqs proper derived direct image preserve internal
torsion homology. Hence the already choice-independent exceptional functor
factors through the native full torsion subcategory at the target. Its canonical
comparisons lift with unchanged underlying maps and retain their cocycle.
No new cohomological or dimension bound is assumed here.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wX wS wM

variable {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]

section Value

variable (C : Hom.DenseCompactification f)
  [HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]

omit [QuasiCompact f] in
/-- Every original compactification functor lands in internal torsion homology. -/
theorem moduleCompactificationFunctor_torsion
    (K : (moduleTorsionCohomologyPlus X Λ).FullSubcategory) :
    moduleTorsionCohomologyPlus S Λ ((moduleCompactificationFunctor f Λ C).obj K) := by
  exact moduleDerivedDirectImage_preservesTorsionCohomology C.p Λ
    ((moduleDerivedLowerShriek C.j Λ).obj K.obj)
    (moduleDerivedLowerShriek_preservesTorsionCohomology C.j Λ K.property)

/-- The same compactification construction with native torsion source and target. -/
def moduleCompactificationTorsionFunctor :
    (moduleTorsionCohomologyPlus X Λ).FullSubcategory ⥤
      (moduleTorsionCohomologyPlus S Λ).FullSubcategory :=
  (moduleTorsionCohomologyPlus S Λ).lift (moduleCompactificationFunctor f Λ C)
    (moduleCompactificationFunctor_torsion f Λ C)

/-- Forgetting the target property recovers the original ambient functor. -/
def moduleCompactificationTorsionForgetIso :
    moduleCompactificationTorsionFunctor f Λ C ⋙ (moduleTorsionCohomologyPlus S Λ).ι ≅
      moduleCompactificationFunctor f Λ C :=
  (moduleTorsionCohomologyPlus S Λ).liftCompιIso (moduleCompactificationFunctor f Λ C)
    (moduleCompactificationFunctor_torsion f Λ C)

end Value

section Comparison

variable [middleModels : ∀ C : Hom.DenseCompactification f,
  HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]

/-- The canonical compactification comparison lifts with its exact underlying maps. -/
def moduleCompactificationTorsionComparison (C D : Hom.DenseCompactification f) :
    moduleCompactificationTorsionFunctor f Λ C ≅ moduleCompactificationTorsionFunctor f Λ D :=
  (moduleTorsionCohomologyPlus S Λ).liftFunctorIso
    (moduleCompactificationFunctor f Λ C) (moduleCompactificationFunctor f Λ D)
    (moduleCompactificationFunctor_torsion f Λ C) (moduleCompactificationFunctor_torsion f Λ D)
    (moduleCompactificationComparison f Λ C D)

/-- Lifted comparison components remain the same original ambient components. -/
theorem moduleCompactificationTorsionComparison_hom_app
    (C D : Hom.DenseCompactification f)
    (K : (moduleTorsionCohomologyPlus X Λ).FullSubcategory) :
    ((moduleCompactificationTorsionComparison f Λ C D).hom.app K).hom =
      (moduleCompactificationComparison f Λ C D).hom.app K := rfl

/-- The torsion-valued canonical comparisons retain the original cocycle. -/
@[simp]
theorem moduleCompactificationTorsionComparison_trans (C D E : Hom.DenseCompactification f) :
    moduleCompactificationTorsionComparison f Λ C D ≪≫
        moduleCompactificationTorsionComparison f Λ D E =
      moduleCompactificationTorsionComparison f Λ C E := by
  unfold moduleCompactificationTorsionComparison moduleCompactificationTorsionFunctor
  rw [ObjectProperty.liftFunctorIso_trans, moduleCompactificationComparison_trans]

/-- The torsion-valued canonical self-comparison is the identity. -/
@[simp]
theorem moduleCompactificationTorsionComparison_self (C : Hom.DenseCompactification f) :
    moduleCompactificationTorsionComparison f Λ C C = Iso.refl _ := by
  unfold moduleCompactificationTorsionComparison moduleCompactificationTorsionFunctor
  rw [moduleCompactificationComparison_self, ObjectProperty.liftFunctorIso_refl]

end Comparison

variable [CompactSpace S] [QuasiSeparatedSpace S] [IsSeparated f] [LocallyOfFiniteType f]

section ChosenValue

variable [HasDerivedCategory.{wM}
  (ModuleSheaf (moduleExceptionalCompactification f).Xbar Λ)]

/-- The choice-independent original exceptional functor on the native D+ torsion categories. -/
def moduleExceptionalDirectImagePlusTorsion :
    (moduleTorsionCohomologyPlus X Λ).FullSubcategory ⥤
      (moduleTorsionCohomologyPlus S Λ).FullSubcategory :=
  moduleCompactificationTorsionFunctor f Λ (moduleExceptionalCompactification f)

/-- Forgetting target torsion recovers exactly the previously constructed ambient Rf!. -/
def moduleExceptionalDirectImagePlusTorsionForgetIso :
    moduleExceptionalDirectImagePlusTorsion f Λ ⋙ (moduleTorsionCohomologyPlus S Λ).ι ≅
      moduleExceptionalDirectImagePlus f Λ :=
  moduleCompactificationTorsionForgetIso f Λ (moduleExceptionalCompactification f)

end ChosenValue

variable [middleModels : ∀ C : Hom.DenseCompactification f,
  HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]

/-- Canonical comparison with every compactification in the actual torsion target. -/
def moduleExceptionalDirectImagePlusTorsionIso (C : Hom.DenseCompactification f) :
    moduleExceptionalDirectImagePlusTorsion f Λ ≅ moduleCompactificationTorsionFunctor f Λ C :=
  moduleCompactificationTorsionComparison f Λ (moduleExceptionalCompactification f) C

/-- The chosen torsion-valued functor retains the canonical comparison cocycle. -/
theorem moduleExceptionalDirectImagePlusTorsionIso_trans (C D : Hom.DenseCompactification f) :
    moduleExceptionalDirectImagePlusTorsionIso f Λ C ≪≫
        moduleCompactificationTorsionComparison f Λ C D =
      moduleExceptionalDirectImagePlusTorsionIso f Λ D :=
  moduleCompactificationTorsionComparison_trans f Λ (moduleExceptionalCompactification f) C D

/-- The target restriction does not change the canonical original comparison map. -/
theorem moduleExceptionalDirectImagePlusTorsionIso_hom_app (C : Hom.DenseCompactification f)
    (K : (moduleTorsionCohomologyPlus X Λ).FullSubcategory) :
    ((moduleExceptionalDirectImagePlusTorsionIso f Λ C).hom.app K).hom =
      (moduleExceptionalDirectImagePlusIso f Λ C).hom.app K := rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
