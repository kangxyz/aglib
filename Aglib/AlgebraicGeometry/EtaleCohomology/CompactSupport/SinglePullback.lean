/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.Single
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.InverseImageTorsion
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.SingleHomology

/-! # Original single coefficients under native inverse image

The comparison is the installed exact-single derived-unit comparison, lifted
with its unchanged maps to the native torsion full subcategory.
-/

@[expose] public noncomputable section


open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u wX wS

variable {X S : Scheme.{u}} (f : X ⟶ S) (Λ : Type (u + 1)) [Ring Λ]

/-- Original inverse image restricted to internally torsion single coefficients. -/
def moduleTorsionCoefficientInverseImage :
    (moduleTorsionCoefficients S Λ).FullSubcategory ⥤
      (moduleTorsionCoefficients X Λ).FullSubcategory :=
  (moduleTorsionCoefficients X Λ).lift
    ((moduleTorsionCoefficients S Λ).ι ⋙ moduleInverseImage f Λ)
    (fun M => moduleInverseImage_preservesTorsion f Λ M.obj M.property)

variable [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]

/-- Exact native pullback carries the original single to the single of ordinary pullback. -/
def moduleTorsionSingleInverseImageIso (i : ℤ) :
    moduleTorsionSingle S Λ i ⋙ moduleDerivedInverseImageTorsion f Λ ≅
      moduleTorsionCoefficientInverseImage f Λ ⋙ moduleTorsionSingle X Λ i :=
  NatIso.ofComponents
    (fun M => (moduleTorsionCohomologyPlus X Λ).isoMk
      ((Functor.rightDerivedFunctorPlusSingleIso (moduleInverseImage f Λ) i).app M.obj))
    (by
      intro M N φ
      apply ObjectProperty.hom_ext
      exact (Functor.rightDerivedFunctorPlusSingleIso (moduleInverseImage f Λ) i).hom.naturality
        φ.hom)

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
