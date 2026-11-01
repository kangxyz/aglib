/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.Single
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.Torsion

/-! # Higher exceptional images of original single coefficients

These are actual native homology sheaves of the chosen bounded-below exceptional
functor. Functoriality is in morphisms of coefficients over the fixed ring;
compatibility with change of coefficient ring is a separate statement.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wX wS wM

variable {X S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
  (f : X ⟶ S) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]

section Value

variable [HasDerivedCategory.{wM}
  (ModuleSheaf (moduleExceptionalCompactification f).Xbar Λ)]

/-- The actual `R^q f_!` functor on internally torsion single coefficients. -/
def moduleHigherExceptionalDirectImage (q : ℤ) :
    (moduleTorsionCoefficients X Λ).FullSubcategory ⥤ ModuleSheaf S Λ :=
  moduleTorsionSingle X Λ 0 ⋙ moduleExceptionalDirectImagePlusTorsion f Λ ⋙
    (moduleTorsionCohomologyPlus S Λ).ι ⋙
      DerivedCategory.Plus.homologyFunctor (ModuleSheaf S Λ) q

/-- Each higher exceptional image is internally torsion, without a common exponent. -/
theorem moduleHigherExceptionalDirectImage_torsion (q : ℤ)
    (M : (moduleTorsionCoefficients X Λ).FullSubcategory) :
    moduleIsTorsion S Λ ((moduleHigherExceptionalDirectImage f Λ q).obj M) :=
  ((moduleExceptionalDirectImagePlusTorsion f Λ).obj
    ((moduleTorsionSingle X Λ 0).obj M)).property q

end Value

variable [middleModels : ∀ C : Hom.DenseCompactification f,
  HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]

/-- The canonical comparison with any actual compactification on single coefficients. -/
def moduleHigherExceptionalDirectImageIso (q : ℤ) (C : Hom.DenseCompactification f) :
    moduleHigherExceptionalDirectImage f Λ q ≅
      moduleTorsionSingle X Λ 0 ⋙ moduleCompactificationTorsionFunctor f Λ C ⋙
        (moduleTorsionCohomologyPlus S Λ).ι ⋙
          DerivedCategory.Plus.homologyFunctor (ModuleSheaf S Λ) q :=
  Functor.isoWhiskerLeft (moduleTorsionSingle X Λ 0)
    (Functor.isoWhiskerRight (moduleExceptionalDirectImagePlusTorsionIso f Λ C)
      ((moduleTorsionCohomologyPlus S Λ).ι ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleSheaf S Λ) q))

/-- The same comparison is natural in the original coefficient morphism. -/
theorem moduleHigherExceptionalDirectImageIso_naturality (q : ℤ)
    (C : Hom.DenseCompactification f)
    {M N : (moduleTorsionCoefficients X Λ).FullSubcategory} (φ : M ⟶ N) :
    (moduleHigherExceptionalDirectImage f Λ q).map φ ≫
        (moduleHigherExceptionalDirectImageIso f Λ q C).hom.app N =
      (moduleHigherExceptionalDirectImageIso f Λ q C).hom.app M ≫
        (moduleTorsionSingle X Λ 0 ⋙ moduleCompactificationTorsionFunctor f Λ C ⋙
          (moduleTorsionCohomologyPlus S Λ).ι ⋙
            DerivedCategory.Plus.homologyFunctor (ModuleSheaf S Λ) q).map φ :=
  (moduleHigherExceptionalDirectImageIso f Λ q C).hom.naturality φ

end AlgebraicGeometry.Scheme.EtaleCohomology
