/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.DirectImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.OpenToDirectImage

/-! # The actual unbounded exceptional-to-ordinary direct-image map -/
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

/-- Push the original triple map through the actual proper factor and structural triangle. -/
def moduleUnboundedCompactificationToDirectImage (C : Hom.DenseCompactification f) :
    moduleUnboundedCompactificationFunctor f Λ C ⟶ moduleUnboundedDerivedDirectImage Λ f :=
  Functor.whiskerRight (moduleUnboundedLowerShriekToDirectImage Λ C.j)
      (moduleUnboundedDerivedDirectImage Λ C.p) ≫
    (moduleUnboundedDerivedDirectImageOverIso Λ f C.p C.j C.fac).hom

omit [QuasiCompact f] in
/-- Each component is the same canonical outer-adjoint map and native compositor. -/
theorem moduleUnboundedCompactificationToDirectImage_app (C : Hom.DenseCompactification f)
    (K : DerivedCategory (ModuleSheaf X Λ)) :
    (moduleUnboundedCompactificationToDirectImage f Λ C).app K =
      (moduleUnboundedDerivedDirectImage Λ C.p).map
        ((moduleUnboundedLowerShriekToDirectImage Λ C.j).app K) ≫
      (moduleUnboundedDerivedDirectImageOverIso Λ f C.p C.j C.fac).hom.app K := rfl

variable [CompactSpace S] [QuasiSeparatedSpace S] [IsSeparated f] [LocallyOfFiniteType f]

/-- The chosen actual exceptional-to-ordinary comparison on all unbounded objects. -/
def moduleExceptionalToDirectImageUnbounded :
    moduleExceptionalDirectImageUnbounded f Λ ⟶ moduleUnboundedDerivedDirectImage Λ f :=
  moduleUnboundedCompactificationToDirectImage f Λ (moduleExceptionalCompactification f)
end AlgebraicGeometry.Scheme.EtaleCohomology
