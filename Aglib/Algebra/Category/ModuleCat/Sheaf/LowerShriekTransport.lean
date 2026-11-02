/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-! # Transport of an actual left adjoint between coefficient presentations

The complete three-factor functor and adjunction are formed from the fixed
coefficient equivalences and an existing valued adjunction. A specified native
right-adjoint comparison then identifies the original right functor. The unit
and finite-limit consequence retain these exact constructions.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Equivalence

variable {A A' B B' : Type*}
  [Category* A] [Category* A'] [Category* B] [Category* B']
  (E : A ≌ A') (F : B ≌ B')

/-- The literal three-factor left functor through the original equivalences. -/
def coefficientLeftFunctor (L : A ⥤ B) : A' ⥤ B' :=
  (E.inverse ⋙ L) ⋙ F.functor

variable {L : A ⥤ B} {R : B ⥤ A}

/-- The actual three adjunctions compose before the native right functor is identified. -/
def coefficientTransportAdjunction (a : L ⊣ R) :
    coefficientLeftFunctor E F L ⊣ F.inverse ⋙ R ⋙ E.functor :=
  (E.symm.toAdjunction.comp a).comp F.toAdjunction

/-- Original right comparison, with the same associator and inverse orientation. -/
def coefficientRightIso (Q : B' ⥤ A')
    (e : Q ≅ (F.inverse ⋙ R) ⋙ E.functor) :
    F.inverse ⋙ R ⋙ E.functor ≅ Q :=
  (Functor.associator _ _ _).symm ≪≫ e.symm

/-- The complete actual adjunction after the original right comparison. -/
def coefficientAdjunction (a : L ⊣ R) (Q : B' ⥤ A')
    (e : Q ≅ (F.inverse ⋙ R) ⋙ E.functor) :
    coefficientLeftFunctor E F L ⊣ Q :=
  (coefficientTransportAdjunction E F a).ofNatIsoRight (coefficientRightIso E F Q e)

/-- The exact original transported left functor preserves finite limits. -/
instance coefficientLeft_preservesFiniteLimits (L : A ⥤ B) [PreservesFiniteLimits L] :
    PreservesFiniteLimits (coefficientLeftFunctor E F L) := by
  let : PreservesLimitsOfSize.{0, 0} E.inverse := E.toAdjunction.rightAdjoint_preservesLimits
  let : PreservesFiniteLimits E.inverse := PreservesLimitsOfSize0.preservesFiniteLimits _
  let : PreservesLimitsOfSize.{0, 0} F.functor :=
    F.symm.toAdjunction.rightAdjoint_preservesLimits
  let : PreservesFiniteLimits F.functor := PreservesLimitsOfSize0.preservesFiniteLimits _
  exact comp_preservesFiniteLimits (E.inverse ⋙ L) F.functor

/-- Whole unit of the actual adjunction, with the original native right comparison. -/
theorem coefficientAdjunction_unit (a : L ⊣ R) (Q : B' ⥤ A')
    (e : Q ≅ (F.inverse ⋙ R) ⋙ E.functor) :
    (coefficientAdjunction E F a Q e).unit =
      (coefficientTransportAdjunction E F a).unit ≫
        Functor.whiskerLeft (coefficientLeftFunctor E F L)
          (coefficientRightIso E F Q e).hom := rfl

end CategoryTheory.Equivalence
