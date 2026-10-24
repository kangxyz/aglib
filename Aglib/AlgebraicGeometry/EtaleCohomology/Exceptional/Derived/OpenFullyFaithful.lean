/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.Open
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleFullyFaithful

/-!
# Full faithfulness of native bounded-below module extension

The original derived unit is invertible by its proved localization equation,
the original open-extension unit, and exactness of inverse image. Essential
surjectivity of the existing localization extends this to every bounded-below
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

/-- The original derived unit is invertible on the original localized complexes. -/
theorem moduleDerivedLowerShriek_unit_Q_isIso
    (K : CochainComplex.Plus (ModuleSheaf U Λ)) :
    IsIso ((moduleDerivedLowerShriekAdjunction j Λ).unit.app
      (DerivedCategory.Plus.Q.obj K)) := by
  let adj := moduleLowerShriekAdjunction j Λ
  have hc : IsIso ((adj.mapCochainComplexPlus.unit.app K).hom) := by
    have hf (n : ℤ) : IsIso ((adj.mapCochainComplexPlus.unit.app K).hom.f n) := by
      change IsIso (adj.unit.app (K.obj.X n))
      infer_instance
    exact HomologicalComplex.Hom.isIso_of_components _
  have hm : IsIso ((CochainComplex.Plus.ι (ModuleSheaf U Λ)).map
      (adj.mapCochainComplexPlus.unit.app K)) := hc
  have hη : IsIso (adj.mapCochainComplexPlus.unit.app K) :=
    isIso_of_reflects_iso _ (CochainComplex.Plus.ι (ModuleSheaf U Λ))
  have : IsIso (moduleInverseImage j Λ).rightDerivedFunctorPlusUnit :=
    (moduleInverseImage j Λ).isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  have hcomp : IsIso
      ((moduleDerivedLowerShriekAdjunction j Λ).unit.app (DerivedCategory.Plus.Q.obj K) ≫
        (moduleDerivedInverseImage Λ j).map
          ((moduleLowerShriek j Λ).rightDerivedFunctorPlusExactComparison.hom.app K)) := by
    rw [moduleDerivedLowerShriekAdjunction_unit_fac]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((moduleDerivedInverseImage Λ j).map
      ((moduleLowerShriek j Λ).rightDerivedFunctorPlusExactComparison.hom.app K))

/-- The original unit is invertible on every actual bounded-below derived object. -/
instance moduleDerivedLowerShriek_unit_isIso :
    IsIso (moduleDerivedLowerShriekAdjunction j Λ).unit := by
  let Q := DerivedCategory.Plus.Q (C := ModuleSheaf U Λ)
  let : Q.EssSurj := Localization.essSurj Q (CochainComplex.Plus.quasiIso (ModuleSheaf U Λ))
  have h (K : DerivedCategory.Plus (ModuleSheaf U Λ)) :
      IsIso ((moduleDerivedLowerShriekAdjunction j Λ).unit.app K) := by
    rw [← NatTrans.isIso_app_iff_of_iso _ (Q.objObjPreimageIso K)]
    exact moduleDerivedLowerShriek_unit_Q_isIso j Λ (Q.objPreimage K)
  exact NatIso.isIso_of_isIso_app _

/-- Genuine full faithfulness of the installed bounded-below module extension. -/
def moduleDerivedLowerShriekFullyFaithful : (moduleDerivedLowerShriek j Λ).FullyFaithful :=
  (moduleDerivedLowerShriekAdjunction j Λ).fullyFaithfulLOfIsIsoUnit

instance moduleDerivedLowerShriek_full : (moduleDerivedLowerShriek j Λ).Full :=
  (moduleDerivedLowerShriekFullyFaithful j Λ).full

instance moduleDerivedLowerShriek_faithful : (moduleDerivedLowerShriek j Λ).Faithful :=
  (moduleDerivedLowerShriekFullyFaithful j Λ).faithful

end AlgebraicGeometry.Scheme.EtaleCohomology
