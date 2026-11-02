/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.CartesianBaseChange
public import Aglib.CategoryTheory.NatTrans.NormalizedExchangeNaturality
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.SourceIsoCompatibility
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.BaseChangeCompatibility
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.BaseChangeIdentity

/-!
# Actual source-isomorphism comparison and original compactified base change

Source transport is identified with the original identity-base exchange,
including the original inverse-image identity comparison. This is a map
compatibility statement, not a relabelling of the source scheme.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wX wX' wY wS

variable {X X' Y S : Scheme.{u}} (e : X' ≅ X) (j : X ⟶ Y) [IsOpenImmersion j]
  (p : Y ⟶ S) (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]
  [HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]

/-- The original source transport before restriction to torsion inputs. -/
def moduleCompactifiedSourceIso :
    moduleDerivedLowerShriek j Λ ⋙ moduleDerivedDirectImage Λ p ≅
      moduleDerivedInverseImage Λ e.hom ⋙
        (moduleDerivedLowerShriek (e.hom ≫ j) Λ ⋙ moduleDerivedDirectImage Λ p) :=
  Functor.isoWhiskerRight (moduleDerivedLowerShriekSourceIso e j Λ)
    (moduleDerivedDirectImage Λ p) ≪≫ Functor.associator _ _ _

omit [IsOpenImmersion j] in
private theorem sourceIsoProperIdentityEquation :
    SourceIsoProperIdentityEquation
      (moduleDerivedBaseChangeMap Λ p p (𝟙 S) (𝟙 Y)
        (isPullback_sourceIsoProperIdentity p).w.symm)
      (moduleDerivedInverseImageIdIso Λ Y) (moduleDerivedInverseImageIdIso Λ S) :=
  moduleDerivedBaseChangeMap_id Λ p (isPullback_sourceIsoProperIdentity p).w.symm

/-- The original compactified exchange over identity base/ambient maps is
exactly the original source-isomorphism comparison after identity normalization. -/
theorem moduleCompactifiedBaseChangeMap_sourceIso_identity :
    SourceIsoExchangeEquation
      (moduleCompactifiedBaseChangeMap j p (e.hom ≫ j) p e.hom (𝟙 Y) (𝟙 S)
        (isPullback_sourceIsoOpen e j) (isPullback_sourceIsoProperIdentity p) Λ)
      (moduleDerivedInverseImageIdIso Λ S) (moduleCompactifiedSourceIso e j p Λ) :=
  sourceIsoExchange_of_proper_identity
    (moduleDerivedBaseChangeMap Λ p p (𝟙 S) (𝟙 Y)
      (isPullback_sourceIsoProperIdentity p).w.symm)
    (moduleDerivedInverseImageIdIso Λ Y) (moduleDerivedInverseImageIdIso Λ S)
    (moduleDerivedLowerShriekCartesianBaseChangeIso e.hom (e.hom ≫ j) j (𝟙 Y)
      (isPullback_sourceIsoOpen e j) Λ)
    (sourceIsoProperIdentityEquation p Λ)

end AlgebraicGeometry.Scheme.EtaleCohomology
