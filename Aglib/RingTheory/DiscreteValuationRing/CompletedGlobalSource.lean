/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.CompletedGlobalCentre
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.Localization.BaseChange

/-! # Finite type of the actual localized global source

The source localization is the actual scalar extension from the original
polynomial ring to its coefficient-prime localization. It is finite type over
THAT localized base; no finite-type assertion is made for a centre local ring
or for localization as an algebra over the unlocalized polynomial base.
-/

@[expose] public noncomputable section

open IsLocalRing
open scoped TensorProduct

namespace PowerSeriesLocalization

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (ι : Type*) (p : R) [Fact (Irreducible p)]
variable (B : Type*) [CommRing B] [Algebra (MvPolynomial ι R) B]

/-- The localized source has the native algebra action from the localized polynomial base. -/
instance globalLocalSourceAlgebra :
    Algebra (ParameterLocalization.Ring R ι p) (GlobalLocalSource R ι p (B := B)) :=
  inferInstanceAs (Algebra
    (Localization (ParameterLocalization.parameterIdeal R ι p).primeCompl)
    (Localization (Algebra.algebraMapSubmonoid B
      (ParameterLocalization.parameterIdeal R ι p).primeCompl)))

/-- The native localized-base action extends the original polynomial coefficient action. -/
instance globalLocalSourceScalarTower :
    IsScalarTower (MvPolynomial ι R) (ParameterLocalization.Ring R ι p)
      (GlobalLocalSource R ι p (B := B)) :=
  inferInstanceAs (IsScalarTower (MvPolynomial ι R)
    (Localization (ParameterLocalization.parameterIdeal R ι p).primeCompl)
    (Localization (Algebra.algebraMapSubmonoid B
      (ParameterLocalization.parameterIdeal R ι p).primeCompl)))

/-- The actual global-source localization is the tensor scalar extension over the fixed base. -/
def globalLocalSourceTensorEquiv :
    ParameterLocalization.Ring R ι p ⊗[MvPolynomial ι R] B ≃ₐ[ParameterLocalization.Ring R ι p]
      GlobalLocalSource R ι p (B := B) :=
  Localization.tensorRightAlgEquiv (ParameterLocalization.parameterIdeal R ι p).primeCompl B

/-- Localization preserves finite type over the localized ORIGINAL base. -/
theorem globalLocalSource_finiteType [Algebra.FiniteType (MvPolynomial ι R) B] :
    Algebra.FiniteType (ParameterLocalization.Ring R ι p) (GlobalLocalSource R ι p (B := B)) :=
  Algebra.FiniteType.equiv inferInstance (globalLocalSourceTensorEquiv R ι p B)

/-- The tensor comparison sends each original source element to its actual localized image. -/
@[simp] theorem globalLocalSourceTensorEquiv_one_tmul (b : B) :
    globalLocalSourceTensorEquiv R ι p B (1 ⊗ₜ[MvPolynomial ι R] b) =
      algebraMap B (GlobalLocalSource R ι p (B := B)) b :=
  Localization.tensorRightAlgEquiv_apply_one_tmul (R := MvPolynomial ι R) (S := B)
    (ParameterLocalization.parameterIdeal R ι p).primeCompl b

end PowerSeriesLocalization
