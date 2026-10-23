/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.FundamentalGroupComparison

/-! # Zero coefficients detected on the original finite geometric fibre

The actual representing finite-etale group is detected by its faithful point
functor. A subsingleton original fibre therefore gives annihilation by one,
so the original sheaf itself is zero, without assuming cohomology vanishing.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Scheme.FiniteEtale

namespace AlgebraicGeometry.Scheme.EtaleCohomology.CoefficientRepresentation

open MarkedCoefficients

universe u

attribute [local instance] Over.cartesianMonoidalCategory hasSheafifyLarge

/-- A represented finite coefficient with zero original geometric fibre is
an actual zero object in the original additive sheaf category. -/
theorem isZero_of_subsingleton_fiber
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ X)
    [GaloisCategory (Scheme.FiniteEtale X)]
    [PreGaloisCategory.FiberFunctor (fiberToFinite s)]
    {F : AbelianSheaf.{u, u + 1} X} (R : CoefficientRepresentation F)
    [Subsingleton (coefficientFiber s F)] : IsZero F := by
  have hk : KilledBy 1 (representedSheaf R.group) :=
    representedSheaf_killedBy_of_identity_pow R.group 1
      (identity_pow_eq_one_of_fiber s R.group 1 (fun a => by
        rw [pow_one]
        apply Additive.ofMul.injective
        exact (R.fiberPointEquiv s).symm.injective (Subsingleton.elim _ _)))
  change (1 : ℕ) • 𝟙 (representedSheaf R.group) = 0 at hk
  have hzero : IsZero (representedSheaf R.group) :=
    (IsZero.iff_id_eq_zero _).mpr (by simpa only [one_nsmul] using hk)
  exact hzero.of_iso R.iso.symm

end AlgebraicGeometry.Scheme.EtaleCohomology.CoefficientRepresentation
