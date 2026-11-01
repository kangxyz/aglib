/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.SectionCone
public import Aglib.AlgebraicGeometry.Modules.ClosedImmersion.QuotientComparison
public import Aglib.AlgebraicGeometry.Modules.IdealPowers.IdealSheaf
public import Aglib.AlgebraicGeometry.Modules.Pullback.UnitSections

/-! # Original unit sections on the actual closed thickenings

The existing equal-kernel closed-immersion comparison and native pullback-unit
isomorphism identify the original ideal-sheaf quotient sections with the
structure-ring sections of the literal base-change thickening. The original
quotient-unit formula is retained before any limit transfer.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u

variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A) (n : ℕ)

/-- The existing quotient comparison, on the same original structure module. -/
def idealSheafThickeningUnitIso :
    (idealSheafQuotientFunctor X (idealThickeningIdealSheaf f I ^ n)).obj
        (SheafOfModules.unit X.ringCatSheaf) ≅
      (pushforward (idealThickeningι f (I ^ n))).obj
        ((pullback (idealThickeningι f (I ^ n))).obj
          (SheafOfModules.unit X.ringCatSheaf)) :=
  closedImmersionQuotientIso (idealThickeningIdealSheaf f I ^ n).subschemeι
    (idealThickeningι f (I ^ n)) (by
      rw [IdealSheafData.ker_subschemeι, idealThickeningι_ker,
        idealThickeningIdealSheaf_pow]) _

/-- The comparison retains the actual two quotient units. -/
@[reassoc]
theorem idealSheafThickeningUnitIso_unit :
    (idealSheafQuotientUnit X (idealThickeningIdealSheaf f I ^ n)).app
        (SheafOfModules.unit X.ringCatSheaf) ≫ (idealSheafThickeningUnitIso f I n).hom =
      (pullbackPushforwardAdjunction (idealThickeningι f (I ^ n))).unit.app
        (SheafOfModules.unit X.ringCatSheaf) :=
  closedImmersionUnit_quotientIso_hom _ _ _ _

/-- Original quotient sections are the original thickening's structure-ring sections. -/
def idealSheafUnitSectionEquiv :
    Γ((idealSheafQuotientFunctor X (idealThickeningIdealSheaf f I ^ n)).obj
      (SheafOfModules.unit X.ringCatSheaf), ⊤) ≃
        Γ(idealThickeningSpace f (I ^ n), ⊤) :=
  (((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).mapIso
    (idealSheafThickeningUnitIso f I n)).toLinearEquiv.toEquiv).trans
      (pullbackUnitGlobalSectionsEquiv (idealThickeningι f (I ^ n)))

/-- The full original scalar/unit equation on sections. -/
theorem idealSheafUnitSectionEquiv_unit (r : Γ(X, ⊤)) :
    idealSheafUnitSectionEquiv f I n
      (Hom.app ((idealSheafQuotientUnit X (idealThickeningIdealSheaf f I ^ n)).app
        (SheafOfModules.unit X.ringCatSheaf)) ⊤ r) =
      (idealThickeningι f (I ^ n)).appTop r := by
  have h := congrArg (fun k : SheafOfModules.unit X.ringCatSheaf ⟶
      (pushforward (idealThickeningι f (I ^ n))).obj
        ((pullback (idealThickeningι f (I ^ n))).obj
          (SheafOfModules.unit X.ringCatSheaf)) => Hom.app k ⊤ r)
    (idealSheafThickeningUnitIso_unit f I n)
  exact (congrArg (pullbackUnitGlobalSectionsEquiv (idealThickeningι f (I ^ n))) h).trans
    (pullbackUnitGlobalSectionsEquiv_unit (idealThickeningι f (I ^ n)) r)

end AlgebraicGeometry.Scheme.Modules.Coherent
