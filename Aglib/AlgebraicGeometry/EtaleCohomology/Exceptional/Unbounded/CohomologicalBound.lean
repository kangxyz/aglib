/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.Underlying
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.Torsion
public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.CoefficientBound

/-!
# Original abelian bounds imply all-module bounds over a torsion ring

The actual derived underlying comparison, proved using relative acyclicity,
identifies the original higher derived objects in the same degree. A positive
annihilator of the ring unit makes every module sheaf internally torsion.
The geometric torsion-sheaf bound remains an explicit input; no such bound or
base-change invertibility is proved here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u wMX wMS wAX wAS

attribute [local instance] hasSheafifyLarge

variable (Λ : Type (u + 1)) [Ring Λ] {X S : Scheme.{u}} (f : X ⟶ S)
  [HasDerivedCategory.{wMX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wMS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wAX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{wAS} (AbelianSheaf.{u, u + 1} S)]

/-- The same-degree original module higher direct image has the original
abelian higher direct image underneath. -/
def moduleHigherDirectImageUnderlyingObjIso (M : ModuleSheaf X Λ) (n : ℕ) :
    (SheafOfModules.toSheaf (constantRing S Λ)).obj
        (((moduleDirectImage f Λ).rightDerived n).obj M) ≅
      (higherDirectImage f n).obj
        ((SheafOfModules.toSheaf (constantRing X Λ)).obj M) :=
  Functor.rightDerivedObjExactCoefficientIso (moduleDirectImage f Λ) (directImage f)
    (SheafOfModules.toSheaf (constantRing X Λ)) (SheafOfModules.toSheaf (constantRing S Λ))
    (moduleDerivedDirectImageUnderlyingIso Λ f) M n

/-- An abelian same-degree bound on the actual underlying object implies
vanishing of the original module higher direct image. -/
theorem isZero_moduleRightDerived_obj_of_underlying
    (M : ModuleSheaf X Λ) (n : ℕ)
    (h : IsZero ((higherDirectImage f n).obj
      ((SheafOfModules.toSheaf (constantRing X Λ)).obj M))) :
    IsZero (((moduleDirectImage f Λ).rightDerived n).obj M) :=
  Functor.isZero_rightDerived_obj_of_exactCoefficient
    (moduleDirectImage f Λ) (directImage f)
    (SheafOfModules.toSheaf (constantRing X Λ)) (SheafOfModules.toSheaf (constantRing S Λ))
    (moduleDerivedDirectImageUnderlyingIso Λ f) M n h

/-- A supplied torsion-sheaf cohomological bound is an all-object module bound
when a positive integer kills the coefficient ring's unit. -/
theorem moduleRightDerived_bound_of_torsion_bound
    (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0) (d : ℕ)
    (hbound : ∀ F : AbelianSheaf.{u, u + 1} X, Sheaf.IsTorsion F →
      IsZero ((higherDirectImage f (d + 1)).obj F))
    (M : ModuleSheaf X Λ) :
    IsZero (((moduleDirectImage f Λ).rightDerived (d + 1)).obj M) :=
  isZero_moduleRightDerived_obj_of_underlying Λ f M (d + 1)
    (hbound _ (moduleIsTorsion_of_nsmul_one_eq_zero X Λ N hN hΛ M))

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
