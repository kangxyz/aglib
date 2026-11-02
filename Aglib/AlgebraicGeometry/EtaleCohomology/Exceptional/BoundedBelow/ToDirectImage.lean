/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.DirectImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.ProperOpen.ToDirectImage

/-! # The original map from exceptional to ordinary direct image

The map is the actual native outer-adjoint comparison on the open part, pushed
through the proper part and the original structural direct-image compositor.
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
  [middleModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]

/-- The original outer-adjoint comparison pushed through an actual compactification. -/
def moduleCompactificationToDirectImage (C : Hom.DenseCompactification f) :
    moduleCompactificationFunctor f Λ C ⟶
      (moduleTorsionCohomologyPlus X Λ).ι ⋙ moduleDerivedDirectImage Λ f :=
  Functor.whiskerLeft (moduleTorsionCohomologyPlus X Λ).ι
    (Functor.whiskerRight (moduleDerivedLowerShriekToDirectImage Λ C.j)
      (moduleDerivedDirectImage Λ C.p) ≫
      (moduleDerivedDirectImageOverIso Λ f C.p C.j C.fac).hom)

omit [QuasiCompact f] in
/-- The component uses the canonical triple map and the actual structural triangle. -/
theorem moduleCompactificationToDirectImage_app (C : Hom.DenseCompactification f)
    (K : (moduleTorsionCohomologyPlus X Λ).FullSubcategory) :
    (moduleCompactificationToDirectImage f Λ C).app K =
      (moduleDerivedDirectImage Λ C.p).map
        ((moduleDerivedLowerShriekToDirectImage Λ C.j).app K.obj) ≫
      (moduleDerivedDirectImageOverIso Λ f C.p C.j C.fac).hom.app K.obj := rfl

variable [CompactSpace S] [QuasiSeparatedSpace S] [IsSeparated f] [LocallyOfFiniteType f]

/-- The selected exceptional map uses the canonical comparison on its original model. -/
def moduleExceptionalToDirectImage :
    moduleExceptionalDirectImagePlus f Λ ⟶
      (moduleTorsionCohomologyPlus X Λ).ι ⋙ moduleDerivedDirectImage Λ f :=
  moduleCompactificationToDirectImage f Λ (moduleExceptionalCompactification f)

end AlgebraicGeometry.Scheme.EtaleCohomology
