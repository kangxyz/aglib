/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.SourceIso
public import Aglib.AlgebraicGeometry.Compactification.Refinements.CartesianBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RawBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.StructuralComparisons

/-!
# Original compactification functors under source-isomorphism transport

The comparison uses the original open Cartesian base-change isomorphism for
the actual source isomorphism and the identity on the ambient scheme. In
particular the source categories are related by their actual inverse image,
not by a relabelling of the literal pullback scheme.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wX wX' wM wS

variable {X X' M : Scheme.{u}} (e : X' ≅ X) (j : X ⟶ M) [IsOpenImmersion j]
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]
  [HasDerivedCategory.{wM} (ModuleSheaf M Λ)]

/-- Source transport through the original open Cartesian comparison. -/
def moduleUnboundedDerivedLowerShriekSourceIso :
    moduleUnboundedDerivedLowerShriek j Λ ≅
      moduleUnboundedDerivedInverseImage Λ e.hom ⋙
        moduleUnboundedDerivedLowerShriek (e.hom ≫ j) Λ :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft (moduleUnboundedDerivedLowerShriek j Λ)
      (moduleUnboundedDerivedInverseImageIdIso Λ M).symm ≪≫
    moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso e.hom (e.hom ≫ j) j (𝟙 M)
      (isPullback_sourceIsoOpen e j) Λ

section Compactification

variable {S : Scheme.{u}} {f : X ⟶ S} (f' : X' ⟶ S)
  (h : e.hom ≫ f = f') (C : Hom.Compactification f)
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]

/-- Reuse the selected derived category on `C.Xbar` for the ambient scheme after
source-isomorphism transport. -/
local instance unboundedSourceIsoAmbientModel :
    HasDerivedCategory.{wM} (ModuleSheaf (C.ofSourceIso f' e h).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ))

/-- The actual raw compactification functor transported through the original
source inverse image. The ambient scheme and proper map are unchanged. -/
def moduleUnboundedRawCompactificationSourceIso :
    moduleUnboundedRawCompactificationFunctor C Λ ≅
      moduleUnboundedDerivedInverseImage Λ e.hom ⋙
        moduleUnboundedRawCompactificationFunctor (C.ofSourceIso f' e h) Λ :=
  Functor.isoWhiskerRight (moduleUnboundedDerivedLowerShriekSourceIso e C.j Λ)
    (moduleUnboundedDerivedDirectImage Λ C.p) ≪≫ Functor.associator _ _ _

end Compactification

end AlgebraicGeometry.Scheme.EtaleCohomology
