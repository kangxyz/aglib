/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.AffineSectionAlgebra
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.NormalBase
public import Aglib.AlgebraicGeometry.Properties.Normal.Basic

/-! # Original normal stalks over a normal affine base

A single actual affine neighbourhood gives a smooth domain algebra over the
normal base. Its native stalk localization transports normality to the
unchanged scheme stalk. No excellence or Noetherianity is required.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u

/-- An integral smooth scheme over a normal domain has normal original stalks. -/
theorem normalStalks_of_smooth_normalBase
    (A : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    {X : Scheme.{u}} [IsIntegral X] (p : X ⟶ Spec (.of A)) [Smooth p] :
    NormalStalks X := by
  intro x
  obtain ⟨V, hV, hx, _⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ (⊤ : X.Opens) from trivial)
  let : Nonempty V := ⟨⟨x, hx⟩⟩
  let B := Γ(X, V)
  let : Algebra A B := (affineSectionCoefficientMap p V).toAlgebra
  let : Algebra.Smooth A B :=
    RingHom.smooth_algebraMap.mp (affineSectionCoefficientMap_smooth p hV)
  let : IsDomain B := inferInstance
  let : IsIntegrallyClosed B := Algebra.Smooth.isIntegrallyClosed_of_normalBase A B
  let q := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  let : q.IsPrime := (hV.primeIdealOf ⟨x, hx⟩).isPrime
  let : Algebra B (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  let : IsLocalization.AtPrime (X.presheaf.stalk x) q := hV.isLocalization_stalk ⟨x, hx⟩
  exact ⟨inferInstance, isIntegrallyClosed_of_isLocalization (X.presheaf.stalk x)
    q.primeCompl q.primeCompl_le_nonZeroDivisors⟩

end AlgebraicGeometry.Scheme
