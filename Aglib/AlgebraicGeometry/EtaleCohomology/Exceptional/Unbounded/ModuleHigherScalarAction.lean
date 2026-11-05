/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ModuleCoefficientCoproducts
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.ScalarAction
public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.Coproducts.CoefficientEquivariance

/-! # Genuine scalar equivariance of the original higher-image underlying comparison -/

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

/-- The actual same-degree underlying comparison respects original noncentral left scalars. -/
theorem moduleHigherDirectImageUnderlyingIso_scalar (n : ℕ) (a : Λ) :
    Functor.whiskerLeft ((moduleDirectImage f Λ).rightDerived n)
        (moduleUnderlyingScalar Λ S a) ≫
      (moduleHigherDirectImageUnderlyingIso Λ f n).hom =
    (moduleHigherDirectImageUnderlyingIso Λ f n).hom ≫
      Functor.whiskerRight (moduleUnderlyingScalar Λ X a) (higherDirectImage f n) :=
  Functor.rightDerivedExactCoefficientIso_equivariant
    (moduleDirectImage f Λ) (directImage f)
    (SheafOfModules.toSheaf (constantRing X Λ))
    (SheafOfModules.toSheaf (constantRing S Λ))
    (moduleDerivedDirectImageUnderlyingIso Λ f)
    (moduleUnderlyingScalar Λ X a) (moduleUnderlyingScalar Λ S a)
    (moduleDerivedDirectImageUnderlyingIso_scalar Λ f a) n

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
