/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.IntegralClosure.HeightOneLocalization
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# The actual dual of the maximal ideal of a normal local domain

Over a Noetherian normal local domain of Krull dimension at least two,
the original scalar map to the dual of its actual maximal ideal is a
linear isomorphism. Its value at `a` is the map `x ↦ a * x`.

The proof first treats any nonzero ideal contained in no height-one
prime. Linearity gives a cross-multiplication identity, and the native
height-one divisibility theorem puts its scalar back in the original ring.
The maximal ideal avoids every height-one prime by the dimension bound.
No regularity, excellence, trait, or coefficient-field hypothesis is used.

This supplies the original scalar correction for closed-fibre extensions
in `Cohomology/Proper/ClosedFibreExtensions`. Derived residue-field
vanishing still needs the actual geometric lift of the quotient.
-/

@[expose] public section

namespace Ideal

variable {R : Type*} [CommRing R]

/-- The original scalar multiplication map into the dual of an actual ideal. -/
def scalarToDual (I : Ideal R) : R →ₗ[R] (I →ₗ[R] R) :=
  LinearMap.toSpanSingleton R (I →ₗ[R] R) I.subtype

@[simp]
theorem scalarToDual_apply (I : Ideal R) (a : R) (x : I) :
    scalarToDual I a x = a * (x : R) := rfl

private theorem linearMap_cross_mul (I : Ideal R) (f : I →ₗ[R] R) (x y : I) :
    (x : R) * f y = (y : R) * f x := by
  have hxy : (x : R) • y = (y : R) • x := Subtype.ext (mul_comm _ _)
  simpa only [map_smul, smul_eq_mul] using congrArg f hxy

variable [IsDomain R]

/-- A nonzero ideal detects equality of its scalar multiplication maps. -/
theorem scalarToDual_injective (I : Ideal R) (hI : I ≠ ⊥) :
    Function.Injective (scalarToDual I) := by
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp hI
  intro a b hab
  apply mul_right_cancel₀ hx0
  exact congrArg (fun f : I →ₗ[R] R => f ⟨x, hx⟩) hab

variable [IsNoetherianRing R] [IsIntegrallyClosed R]

/-- Every linear map from a nonzero ideal avoiding all height-one primes
to its normal Noetherian domain is multiplication by an original scalar. -/
theorem scalarToDual_surjective_of_forall_height_one_not_le
    (I : Ideal R) (hI : I ≠ ⊥)
    (havoid : ∀ P : Ideal R, P.IsPrime → P.height = 1 → ¬I ≤ P) :
    Function.Surjective (scalarToDual I) := by
  intro f
  obtain ⟨t, ht, ht0⟩ := (Submodule.ne_bot_iff _).mp hI
  have hdiv : t ∣ f ⟨t, ht⟩ := by
    apply IsIntegrallyClosed.dvd_of_forall_height_one ht0
    intro P hP hheight
    obtain ⟨s, hs, hsP⟩ := SetLike.not_le_iff_exists.mp (havoid P hP hheight)
    refine ⟨s, hsP, f ⟨s, hs⟩, ?_⟩
    exact (linearMap_cross_mul I f ⟨t, ht⟩ ⟨s, hs⟩).symm
  obtain ⟨a, ha⟩ := hdiv
  refine ⟨a, ?_⟩
  apply LinearMap.ext
  intro x
  change a * (x : R) = f x
  apply mul_left_cancel₀ ht0
  calc
    t * (a * (x : R)) = (x : R) * (t * a) := by ring
    _ = (x : R) * f ⟨t, ht⟩ := by rw [← ha]
    _ = t * f x := (linearMap_cross_mul I f ⟨t, ht⟩ x).symm

end Ideal

namespace IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- In local dimension at least two, the original maximal ideal is
contained in no height-one prime of the original ring. -/
theorem maximalIdeal_not_le_height_one (hdim : 2 ≤ ringKrullDim R)
    (P : Ideal R) [P.IsPrime] (hP : P.height = 1) : ¬maximalIdeal R ≤ P := by
  intro hmP
  have he : maximalIdeal R = P :=
    le_antisymm hmP (le_maximalIdeal_of_isPrime P)
  have hd := hdim
  rw [← maximalIdeal_height_eq_ringKrullDim, he, hP] at hd
  norm_num at hd

private theorem maximalIdeal_ne_bot_of_two_le_ringKrullDim
    (hdim : 2 ≤ ringKrullDim R) : maximalIdeal R ≠ ⊥ := by
  intro hm
  have hd := hdim
  rw [← maximalIdeal_height_eq_ringKrullDim, hm, Ideal.height_bot] at hd
  norm_num at hd

variable [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]

/-- The original scalar map to the dual of the actual maximal ideal is
bijective over a normal Noetherian local domain of dimension at least two. -/
theorem maximalIdeal_scalarToDual_bijective (hdim : 2 ≤ ringKrullDim R) :
    Function.Bijective (Ideal.scalarToDual (maximalIdeal R)) := by
  have hm := maximalIdeal_ne_bot_of_two_le_ringKrullDim hdim
  refine ⟨Ideal.scalarToDual_injective _ hm,
    Ideal.scalarToDual_surjective_of_forall_height_one_not_le _ hm ?_⟩
  intro P hP hheight
  let : P.IsPrime := hP
  exact maximalIdeal_not_le_height_one hdim P hheight

/-- The linear equivalence whose forward map is the original scalar
map `a ↦ (x ↦ a * x)` on the original maximal ideal. -/
noncomputable def maximalIdealDualEquiv (hdim : 2 ≤ ringKrullDim R) :
    R ≃ₗ[R] (maximalIdeal R →ₗ[R] R) :=
  LinearEquiv.ofBijective (Ideal.scalarToDual (maximalIdeal R))
    (maximalIdeal_scalarToDual_bijective hdim)

@[simp]
theorem maximalIdealDualEquiv_apply (hdim : 2 ≤ ringKrullDim R)
    (a : R) (x : maximalIdeal R) : maximalIdealDualEquiv hdim a x = a * (x : R) := rfl

@[simp]
theorem maximalIdealDualEquiv_toLinearMap (hdim : 2 ≤ ringKrullDim R) :
    (maximalIdealDualEquiv hdim).toLinearMap = Ideal.scalarToDual (maximalIdeal R) := rfl

end IsLocalRing
