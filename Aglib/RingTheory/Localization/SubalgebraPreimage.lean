/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.Algebra.Algebra.Subalgebra.Tower

/-! # Localizing the preimage of a subalgebra -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace IsLocalization.SubalgebraPreimage

variable (R R' A A' : Type*) [CommRing R] [CommRing R'] [CommRing A] [CommRing A']
  [Algebra R R'] [Algebra R A] [Algebra R A'] [Algebra A A'] [Algebra R' A']
  [IsScalarTower R A A'] [IsScalarTower R R' A']

/-- The original inverse-image subalgebra, before localization. -/
def preimage (C : Subalgebra R' A') : Subalgebra R A :=
  (C.restrictScalars R).comap (IsScalarTower.toAlgHom R A A')

/-- The original algebra map from the inverse image into the localized subalgebra. -/
def map (C : Subalgebra R' A') : preimage R R' A A' C →ₐ[R] C :=
  ((IsScalarTower.toAlgHom R A A').comp (preimage R R' A A' C).val).codRestrict
    (C.restrictScalars R) (fun b => b.property)

@[simp]
theorem map_coe (C : Subalgebra R' A') (b : preimage R R' A A' C) :
    (map R R' A A' C b : A') = algebraMap A A' b.val := rfl

/-- Localizing the original preimage recovers the actual localized subalgebra.
No finite-generation, Noetherian, reducedness or injectivity hypothesis is required. -/
theorem isLocalization (M : Submonoid R) [IsLocalization M R']
    [IsLocalization (M.map (algebraMap R A)) A'] (C : Subalgebra R' A') :
    letI : Algebra (preimage R R' A A' C) C := (map R R' A A' C).toRingHom.toAlgebra
    IsLocalization (M.map (algebraMap R (preimage R R' A A' C))) C := by
  let : Algebra (preimage R R' A A' C) C := (map R R' A A' C).toRingHom.toAlgebra
  refine { map_units := ?_, surj := ?_, exists_of_eq := ?_ }
  · rintro ⟨b, r, hr, rfl⟩
    change IsUnit (map R R' A A' C (algebraMap R _ r))
    rw [AlgHom.commutes]
    have h := (IsLocalization.map_units R' ⟨r, hr⟩).map (algebraMap R' C)
    simpa only [← IsScalarTower.algebraMap_apply R R' C] using h
  · intro c
    obtain ⟨⟨a, m⟩, he⟩ := IsLocalization.surj (M.map (algebraMap R A)) (c : A')
    obtain ⟨r, hr, hm⟩ := m.property
    have hmC : algebraMap A A' m ∈ C := by
      rw [← hm, ← IsScalarTower.algebraMap_apply R A A',
        IsScalarTower.algebraMap_apply R R' A']
      exact C.algebraMap_mem _
    have ha : algebraMap A A' a ∈ C := by
      rw [← he]
      exact C.mul_mem c.property hmC
    refine ⟨(⟨a, ha⟩, ⟨algebraMap R _ r, ⟨r, hr, rfl⟩⟩), ?_⟩
    apply Subtype.ext
    change (c : A') * algebraMap A A' (algebraMap R A r) = algebraMap A A' a
    rw [hm]
    exact he
  · intro x y h
    have h' := congrArg Subtype.val h
    change algebraMap A A' x.val = algebraMap A A' y.val at h'
    obtain ⟨m, hm⟩ := IsLocalization.exists_of_eq (M := M.map (algebraMap R A)) h'
    obtain ⟨r, hr, he⟩ := m.property
    refine ⟨⟨algebraMap R _ r, ⟨r, hr, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    change algebraMap R A r * x.val = algebraMap R A r * y.val
    rw [he]
    exact hm

end IsLocalization.SubalgebraPreimage
