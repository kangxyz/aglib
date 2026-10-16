/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
# Semilinear maps on the native exterior powers

A semilinear map over an arbitrary homomorphism of commutative rings
induces a semilinear map between the existing exterior powers. Its value
on every original wedge is the wedge of the original images. Identity,
composition and agreement with the native linear map retain this exact
formula. Ring and module universes remain independent.
-/

@[expose] public section

noncomputable section

open Function

universe u v w x u' v'

namespace exteriorPower

variable {R : Type u} {S : Type v} {T : Type u'}
  [CommRing R] [CommRing S] [CommRing T]
  {M : Type w} {N : Type x} {P : Type v'}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
  [AddCommGroup P] [Module T P]

/-- The original image wedge is alternating for restriction through the given ring map. -/
def mapSemilinearAlternating (n : ℕ) {φ : R →+* S} (f : M →ₛₗ[φ] N) :
    letI := Module.compHom (⋀[S]^n N) φ
    M [⋀^Fin n]→ₗ[R] (⋀[S]^n N) := by
  classical
  letI := Module.compHom (⋀[S]^n N) φ
  exact
    { toFun := fun v => ιMulti S n (f ∘ v)
      map_update_add' := fun v i x y => by
        change ιMulti S n (f ∘ update v i (x + y)) =
          ιMulti S n (f ∘ update v i x) + ιMulti S n (f ∘ update v i y)
        simp only [Function.comp_update, map_add, AlternatingMap.map_update_add]
      map_update_smul' := fun v i r x => by
        change ιMulti S n (f ∘ update v i (r • x)) =
          φ r • ιMulti S n (f ∘ update v i x)
        simp only [Function.comp_update, f.map_smulₛₗ, AlternatingMap.map_update_smul]
      map_eq_zero_of_eq' := fun v i j hv hij =>
        (ιMulti S n).map_eq_zero_of_eq (f ∘ v) (congrArg f hv) hij }

/-- The original exterior power carries every original scalar-changing linear map. -/
def mapSemilinear (n : ℕ) {φ : R →+* S} (f : M →ₛₗ[φ] N) :
    (⋀[R]^n M) →ₛₗ[φ] (⋀[S]^n N) := by
  letI := Module.compHom (⋀[S]^n N) φ
  let L : (⋀[R]^n M) →ₗ[R] (⋀[S]^n N) :=
    alternatingMapLinearEquiv (mapSemilinearAlternating n f)
  exact
    { toFun := L
      map_add' := L.map_add
      map_smul' := L.map_smul }

/-- The semilinear exterior map sends each original wedge to the original image wedge. -/
@[simp]
theorem mapSemilinear_apply_ιMulti (n : ℕ) {φ : R →+* S}
    (f : M →ₛₗ[φ] N) (v : Fin n → M) :
    mapSemilinear n f (ιMulti R n v) = ιMulti S n (f ∘ v) := by
  let := Module.compHom (⋀[S]^n N) φ
  exact alternatingMapLinearEquiv_apply_ιMulti (mapSemilinearAlternating n f) v

/-- Semilinear maps out of the native exterior power are determined by original wedges. -/
@[ext]
theorem semilinearMap_ext {n : ℕ} {φ : R →+* S}
    {f g : (⋀[R]^n M) →ₛₗ[φ] N}
    (h : ∀ v : Fin n → M, f (ιMulti R n v) = g (ιMulti R n v)) : f = g := by
  apply LinearMap.ext
  intro x
  have hx : x ∈ Submodule.span R (Set.range (ιMulti R n (M := M))) := by
    rw [ιMulti_span]
    trivial
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨v, rfl⟩ := hx; exact h v
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul r x _ hx => simp only [f.map_smulₛₗ, g.map_smulₛₗ, hx]

/-- Identity is preserved by the original semilinear exterior construction. -/
@[simp]
theorem mapSemilinear_id (n : ℕ) :
    mapSemilinear n (LinearMap.id (R := R) (M := M)) = LinearMap.id := by
  apply semilinearMap_ext
  intro v
  simp

/-- Composition changes the coefficient ring through the original composite ring map. -/
theorem mapSemilinear_comp (n : ℕ) {φ : R →+* S} {ψ : S →+* T} {χ : R →+* T}
    [RingHomCompTriple φ ψ χ]
    (f : M →ₛₗ[φ] N) (g : N →ₛₗ[ψ] P) :
    mapSemilinear n (g.comp f : M →ₛₗ[χ] P) =
      (mapSemilinear n g).comp (mapSemilinear n f) := by
  apply semilinearMap_ext
  intro v
  simp only [mapSemilinear_apply_ιMulti, LinearMap.comp_apply]
  rfl

/-- For one coefficient ring, the construction is the existing native exterior map. -/
theorem mapSemilinear_eq_map (n : ℕ) {N : Type x} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) : mapSemilinear n f = map n f := by
  apply semilinearMap_ext
  intro v
  simp

end exteriorPower
