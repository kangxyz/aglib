/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.CartesianBaseChange
public import Aglib.AlgebraicGeometry.Compactification.Refinements.SourceIso
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.RawBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.Composition

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
def moduleDerivedLowerShriekSourceIso :
    moduleDerivedLowerShriek j Λ ≅
      moduleDerivedInverseImage Λ e.hom ⋙ moduleDerivedLowerShriek (e.hom ≫ j) Λ :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft (moduleDerivedLowerShriek j Λ)
      (moduleDerivedInverseImageIdIso Λ M).symm ≪≫
    moduleDerivedLowerShriekCartesianBaseChangeIso e.hom (e.hom ≫ j) j (𝟙 M)
      (isPullback_sourceIsoOpen e j) Λ

section Compactification

variable {S : Scheme.{u}} {f : X ⟶ S} (f' : X' ⟶ S)
  (h : e.hom ≫ f = f') (C : Hom.Compactification f)
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]

/-- Derived-category instance on module sheaves over `(C.ofSourceIso f' e h).Xbar`, using the
instance on `C.Xbar`.
-/
local instance sourceIsoAmbientModel :
    HasDerivedCategory.{wM} (ModuleSheaf (C.ofSourceIso f' e h).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ))

/-- The actual raw compactification functor transported through the original
source inverse image. The ambient scheme and proper map are unchanged. -/
def moduleRawCompactificationSourceIso :
    moduleRawCompactificationFunctor C Λ ≅
      moduleDerivedInverseImageTorsion e.hom Λ ⋙
        moduleRawCompactificationFunctor (C.ofSourceIso f' e h) Λ :=
  Functor.isoWhiskerLeft (moduleTorsionCohomologyPlus X Λ).ι
      (Functor.isoWhiskerRight (moduleDerivedLowerShriekSourceIso e C.j Λ)
        (moduleDerivedDirectImage Λ C.p)) ≪≫
    Functor.isoWhiskerLeft (moduleTorsionCohomologyPlus X Λ).ι
      (Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (moduleDerivedInverseImageTorsionForgetIso e.hom Λ).symm
      (moduleDerivedLowerShriek (e.hom ≫ C.j) Λ ⋙ moduleDerivedDirectImage Λ C.p) ≪≫
    Functor.associator _ _ _

end Compactification

end AlgebraicGeometry.Scheme.EtaleCohomology
