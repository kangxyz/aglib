/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.LinearAlgebra.ExteriorPower.Semilinear
public import Mathlib.LinearAlgebra.Determinant

/-!
# The actual top exterior frame and its determinant coefficients

A displayed basis indexed by `Fin n` identifies the native top exterior
power with the coefficient ring. The forward map is the original basis
determinant, extended by the native exterior universal property; its
inverse multiplies the original wedge of that basis. Change of basis and
change of coefficient rings retain the literal determinant factor.
The coefficient ring is arbitrary and dimension zero is included.
-/

@[expose] public section

noncomputable section

open Function Module

universe u v w x

namespace exteriorPower

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] {n : ℕ}

/-- Every original top wedge is the original determinant times the basis wedge. -/
theorem ιMulti_eq_det_smul (b : Basis (Fin n) R M) (s : Fin n → M) :
    ιMulti R n s = b.det s • ιMulti R n b := by
  have H : ιMulti R n (M := M) = b.det.smulRight (ιMulti R n b) := by
    apply b.ext_alternating
    intro t ht
    let σ : Equiv.Perm (Fin n) := Equiv.ofBijective t (Finite.injective_iff_bijective.mp ht)
    change ιMulti R n (b ∘ σ) = b.det (b ∘ σ) • ιMulti R n b
    simp [AlternatingMap.map_perm, Module.Basis.det_self]
  exact congrArg (fun F => F s) H

end exteriorPower

namespace Module.Basis

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] {n : ℕ}

/-- The native top exterior power is a free rank-one module in the original basis wedge. -/
def exteriorPowerTopEquiv (b : Basis (Fin n) R M) : (⋀[R]^n M) ≃ₗ[R] R where
  toLinearMap := exteriorPower.alternatingMapLinearEquiv b.det
  invFun r := r • exteriorPower.ιMulti R n b
  left_inv x := by
    have H : ((LinearMap.id (R := R) (M := R)).smulRight
        (exteriorPower.ιMulti R n b)).comp
          (exteriorPower.alternatingMapLinearEquiv b.det) = LinearMap.id := by
      apply exteriorPower.linearMap_ext
      apply AlternatingMap.ext
      intro s
      change exteriorPower.alternatingMapLinearEquiv b.det (exteriorPower.ιMulti R n s) •
        exteriorPower.ιMulti R n b = exteriorPower.ιMulti R n s
      rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
      exact (exteriorPower.ιMulti_eq_det_smul b s).symm
    exact LinearMap.congr_fun H x
  right_inv r := by
    change (exteriorPower.alternatingMapLinearEquiv b.det)
      (r • exteriorPower.ιMulti R n b) = r
    rw [map_smul, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, b.det_self]
    simp

/-- The forward scalar coordinate is exactly the original basis determinant on every wedge. -/
@[simp]
theorem exteriorPowerTopEquiv_ιMulti (b : Basis (Fin n) R M) (s : Fin n → M) :
    b.exteriorPowerTopEquiv (exteriorPower.ιMulti R n s) = b.det s :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti b.det s

/-- The inverse scalar coordinate is exactly scalar multiplication of the original basis wedge. -/
@[simp]
theorem exteriorPowerTopEquiv_symm_apply (b : Basis (Fin n) R M) (r : R) :
    b.exteriorPowerTopEquiv.symm r = r • exteriorPower.ιMulti R n b := rfl

/-- The original basis wedge has scalar coordinate one, including rank zero. -/
@[simp]
theorem exteriorPowerTopEquiv_basis (b : Basis (Fin n) R M) :
    b.exteriorPowerTopEquiv (exteriorPower.ιMulti R n b) = 1 := by
  rw [exteriorPowerTopEquiv_ιMulti, b.det_self]

/-- Change of the original frame has the literal original determinant coefficient. -/
theorem exteriorPowerTopEquiv_changeBasis (b c : Basis (Fin n) R M) (x : ⋀[R]^n M) :
    b.exteriorPowerTopEquiv x = b.det c * c.exteriorPowerTopEquiv x := by
  have hx : x = c.exteriorPowerTopEquiv x • exteriorPower.ιMulti R n c :=
    (c.exteriorPowerTopEquiv.symm_apply_apply x).symm
  rw [hx, map_smul, exteriorPowerTopEquiv_ιMulti]
  simp [c.det_self, mul_comm]

variable {S : Type w} [CommRing S] {N : Type x} [AddCommGroup N] [Module S N]

/-- An original semilinear map acts on the top exterior coordinates by the determinant
of the images of the source basis and the original coefficient-ring homomorphism. -/
theorem exteriorPowerTopEquiv_mapSemilinear
    (b : Basis (Fin n) R M) (c : Basis (Fin n) S N) {φ : R →+* S}
    (f : M →ₛₗ[φ] N) (x : ⋀[R]^n M) :
    c.exteriorPowerTopEquiv (exteriorPower.mapSemilinear n f x) =
      c.det (f ∘ b) * φ (b.exteriorPowerTopEquiv x) := by
  have hx : x = b.exteriorPowerTopEquiv x • exteriorPower.ιMulti R n b :=
    (b.exteriorPowerTopEquiv.symm_apply_apply x).symm
  rw [hx, LinearMap.map_smulₛₗ, exteriorPower.mapSemilinear_apply_ιMulti,
    map_smul, exteriorPowerTopEquiv_ιMulti]
  simp [b.det_self, mul_comm]

end Module.Basis
