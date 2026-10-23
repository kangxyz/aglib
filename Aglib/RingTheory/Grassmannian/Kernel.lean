/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Grassmannian
public import Mathlib.RingTheory.Flat.LocallyFree

/-!
# Grassmannian points as kernels

* `Module.Grassmannian.ofSurjective`: the kernel of a surjective linear map `g : M → Q` onto a
  finite projective module of rank `k` at every prime is a point of `G(k, M; R)`
  (`ofSurjective_toSubmodule`).
* `Module.Grassmannian.eq_of_le`: comparable points of `G(k, M; R)` are equal, since the
  surjection `M ⧸ N₁ ↠ M ⧸ N₂` of finite projective modules of the same rank at every prime is
  bijective (`Module.bijective_of_surjective_of_rankAtStalk_eq`).
-/

@[expose] public section

universe u v

namespace Module.Grassmannian

/-- **A Grassmannian point from a surjection**: the kernel of a surjective linear map `g : M → Q`
onto a finite projective module of rank `k` at every prime is a point of `G(k, M; R)`. -/
def ofSurjective {R : Type u} [CommRing R] {M Q : Type v} [AddCommGroup M] [Module R M]
    [AddCommGroup Q] [Module R Q] [Module.Finite R Q] [Module.Projective R Q] {k : ℕ}
    (g : M →ₗ[R] Q) (hg : Function.Surjective g) (hk : ∀ p, Module.rankAtStalk (R := R) Q p = k) :
    Module.Grassmannian R M k where
  toSubmodule := LinearMap.ker g
  finite_quotient := Module.Finite.equiv (g.quotKerEquivOfSurjective hg).symm
  projective_quotient := Module.Projective.of_equiv (g.quotKerEquivOfSurjective hg).symm
  rankAtStalk_eq p := (congrFun (Module.rankAtStalk_eq_of_equiv
    (g.quotKerEquivOfSurjective hg)) p).trans (hk p)

theorem ofSurjective_toSubmodule {R : Type u} [CommRing R] {M Q : Type v} [AddCommGroup M]
    [Module R M] [AddCommGroup Q] [Module R Q] [Module.Finite R Q] [Module.Projective R Q]
    {k : ℕ} (g : M →ₗ[R] Q) (hg : Function.Surjective g)
    (hk : ∀ p, Module.rankAtStalk (R := R) Q p = k) :
    (ofSurjective g hg hk).toSubmodule = LinearMap.ker g :=
  rfl

/-- **Comparable Grassmannian points are equal**: if `N₁ ≤ N₂` in `G(k, M; R)`, then `N₁ = N₂`; the
surjection `M ⧸ N₁ ↠ M ⧸ N₂` of finite projective modules of the same rank at every prime is
bijective (`Module.bijective_of_surjective_of_rankAtStalk_eq`). This reduces the naturality of a
family of points to an inclusion of submodules. -/
theorem eq_of_le {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] {k : ℕ}
    {N₁ N₂ : Module.Grassmannian R M k} (h : N₁.toSubmodule ≤ N₂.toSubmodule) : N₁ = N₂ := by
  apply Module.Grassmannian.ext
  refine le_antisymm h fun x hx => ?_
  have hb := Module.bijective_of_surjective_of_rankAtStalk_eq (Submodule.factor_surjective h)
    fun m _ => by rw [N₁.rankAtStalk_eq, N₂.rankAtStalk_eq]
  have hx' : Submodule.factor h (N₁.toSubmodule.mkQ x) = Submodule.factor h 0 := by
    rw [Submodule.factor_mk, map_zero, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact hx
  exact (Submodule.Quotient.mk_eq_zero _).mp (hb.1 hx')

end Module.Grassmannian
