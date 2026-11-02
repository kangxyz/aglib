/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.UnboundedOpen
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleFullyFaithful
public import Aglib.CategoryTheory.Adjunction.ConjugateStructuralCoherence

/-!
# Full faithfulness of native unbounded module extension

The original derived unit is invertible by its proved localization equation,
the original open-extension unit, and exactness of inverse image. Essential
surjectivity of the existing localization extends this to every unbounded
object. No replacement model or independent choice of an adjunction is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u w w'

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{w} (ModuleSheaf U Λ)]
  [HasDerivedCategory.{w'} (ModuleSheaf X Λ)]

private theorem moduleUnboundedDerivedLowerShriek_unit_isIso_original :
    IsIso (moduleUnboundedDerivedLowerShriekAdjunction j Λ).unit := by
  let adj := moduleLowerShriekAdjunction j Λ
  have h (K : CochainComplex (ModuleSheaf U Λ) ℤ) :
      IsIso ((adj.mapHomologicalComplex (.up ℤ)).unit.app K) := by
    have hK (n : ℤ) :
        IsIso (((adj.mapHomologicalComplex (.up ℤ)).unit.app K).f n) := by
      change IsIso (adj.unit.app (K.X n))
      infer_instance
    exact HomologicalComplex.Hom.isIso_of_components _
  let : IsIso (adj.mapHomologicalComplex (.up ℤ)).unit :=
    NatIso.isIso_of_isIso_app _
  let : CatCommSq ((moduleLowerShriek j Λ).mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q (moduleUnboundedDerivedLowerShriek j Λ) :=
    ⟨(moduleLowerShriek j Λ).mapDerivedCategoryFactors.symm⟩
  let : CatCommSq ((moduleInverseImage j Λ).mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q (moduleUnboundedDerivedInverseImage Λ j) :=
    ⟨(moduleInverseImage j Λ).mapDerivedCategoryFactors.symm⟩
  exact (adj.mapHomologicalComplex (.up ℤ)).localization_unit_isIso_of_original
    DerivedCategory.Q (HomologicalComplex.quasiIso (ModuleSheaf U Λ) (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso (ModuleSheaf X Λ) (.up ℤ))
    (moduleUnboundedDerivedLowerShriek j Λ) (moduleUnboundedDerivedInverseImage Λ j)

/-- The same original localized unit is invertible on every original cochain value. -/
theorem moduleUnboundedDerivedLowerShriek_unit_Q_isIso
    (K : CochainComplex (ModuleSheaf U Λ) ℤ) :
    IsIso ((moduleUnboundedDerivedLowerShriekAdjunction j Λ).unit.app
      (DerivedCategory.Q.obj K)) := by
  let := moduleUnboundedDerivedLowerShriek_unit_isIso_original j Λ
  infer_instance

/-- The actual unbounded unit uses the generic localization-unit theorem. -/
instance moduleUnboundedDerivedLowerShriek_unit_isIso :
    IsIso (moduleUnboundedDerivedLowerShriekAdjunction j Λ).unit :=
  moduleUnboundedDerivedLowerShriek_unit_isIso_original j Λ

/-- Genuine full faithfulness of the installed unbounded module extension. -/
def moduleUnboundedDerivedLowerShriekFullyFaithful :
    (moduleUnboundedDerivedLowerShriek j Λ).FullyFaithful :=
  (moduleUnboundedDerivedLowerShriekAdjunction j Λ).fullyFaithfulLOfIsIsoUnit

instance moduleUnboundedDerivedLowerShriek_full : (moduleUnboundedDerivedLowerShriek j Λ).Full :=
  (moduleUnboundedDerivedLowerShriekFullyFaithful j Λ).full

instance moduleUnboundedDerivedLowerShriek_faithful :
    (moduleUnboundedDerivedLowerShriek j Λ).Faithful :=
  (moduleUnboundedDerivedLowerShriekFullyFaithful j Λ).faithful

end AlgebraicGeometry.Scheme.EtaleCohomology
