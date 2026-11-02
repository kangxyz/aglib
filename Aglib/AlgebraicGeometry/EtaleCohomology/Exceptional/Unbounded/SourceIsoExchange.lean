/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.SourceIsoCompatibility
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.BaseChangeCompatibility
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.BaseChangeIdentity
public import Aglib.CategoryTheory.NatTrans.NormalizedExchangeNaturality

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
def moduleUnboundedCompactifiedSourceIso :
    moduleUnboundedDerivedLowerShriek j Λ ⋙ moduleUnboundedDerivedDirectImage Λ p ≅
      moduleUnboundedDerivedInverseImage Λ e.hom ⋙
        (moduleUnboundedDerivedLowerShriek (e.hom ≫ j) Λ ⋙ moduleUnboundedDerivedDirectImage Λ p) :=
  Functor.isoWhiskerRight (moduleUnboundedDerivedLowerShriekSourceIso e j Λ)
    (moduleUnboundedDerivedDirectImage Λ p) ≪≫ Functor.associator _ _ _

omit [IsOpenImmersion j] in
private theorem sourceIsoProperIdentityEquation :
    SourceIsoProperIdentityEquation
      (moduleUnboundedDerivedBaseChangeMap Λ p p (𝟙 S) (𝟙 Y)
        (isPullback_sourceIsoProperIdentity p).w.symm)
      (moduleUnboundedDerivedInverseImageIdIso Λ Y) (moduleUnboundedDerivedInverseImageIdIso Λ S) :=
  moduleUnboundedDerivedBaseChangeMap_id Λ p (isPullback_sourceIsoProperIdentity p).w.symm

/-- The original compactified exchange over identity base/ambient maps is
exactly the original source-isomorphism comparison after identity normalization. -/
theorem moduleUnboundedCompactifiedBaseChangeMap_sourceIso_identity :
    SourceIsoExchangeEquation
      (moduleUnboundedCompactifiedBaseChangeMap j p (e.hom ≫ j) p e.hom (𝟙 Y) (𝟙 S)
        (isPullback_sourceIsoOpen e j) (isPullback_sourceIsoProperIdentity p) Λ)
      (moduleUnboundedDerivedInverseImageIdIso Λ S)
      (moduleUnboundedCompactifiedSourceIso e j p Λ) :=
  sourceIsoExchange_of_proper_identity
    (moduleUnboundedDerivedBaseChangeMap Λ p p (𝟙 S) (𝟙 Y)
      (isPullback_sourceIsoProperIdentity p).w.symm)
    (moduleUnboundedDerivedInverseImageIdIso Λ Y) (moduleUnboundedDerivedInverseImageIdIso Λ S)
    (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso e.hom (e.hom ≫ j) j (𝟙 Y)
      (isPullback_sourceIsoOpen e j) Λ)
    (sourceIsoProperIdentityEquation p Λ)

end AlgebraicGeometry.Scheme.EtaleCohomology
