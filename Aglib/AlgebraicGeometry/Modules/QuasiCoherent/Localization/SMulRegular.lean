/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Localization.AffineOpenSections
public import Mathlib.Algebra.GroupWithZero.Action.Regular

/-!
# Nonzerodivisors on the sections over an affine open

Let `U` be an affine open of a scheme `X` and `M` a module sheaf whose restriction along the
canonical map `Spec Γ(X, U) → X` is quasicoherent. If `a ∈ Γ(X, U)` is a nonzerodivisor on
`Γ(M, U)`, its restriction to every open `V ≤ U` is a nonzerodivisor on `Γ(M, V)`.

* `AffineOpenSections.isSMulRegular_basicOpen`: the case `V = D(f)`. A section over `D(f)` is
  `t / fⁿ` for a section `t` over `U`, and a section over `U` restricting to zero on `D(f)` is
  killed by a power of `f` (`exists_power_mul_eq_restriction`, `exists_power_smul_eq_zero`);
  so this is the exactness of localization (Stacks 00CS) applied to multiplication by `a`.
* `AffineOpenSections.isSMulRegular_restrict`: a general `V ≤ U` is covered by basic opens
  `D(f) ≤ V` with `f ∈ Γ(X, U)`, and a section of a sheaf vanishing on each of them vanishes.

Quasicoherence is used only on the affine chart, and no finiteness or Noetherian hypothesis is
needed.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules.QuasiCoherent.AffineOpenSections

variable {X : Scheme.{u}} (M : X.Modules) {U : X.Opens}

/-- **Nonzerodivisors restrict to basic opens**: a nonzerodivisor `a` on the sections over an
affine open `U` restricts to a nonzerodivisor on the sections over `D(f)`, for `f ∈ Γ(X, U)`. -/
theorem isSMulRegular_basicOpen (hU : IsAffineOpen U)
    [(M.restrict hU.fromSpec).IsQuasicoherent] {a : Γ(X, U)} (ha : IsSMulRegular Γ(M, U) a)
    (f : Γ(X, U)) :
    IsSMulRegular Γ(M, X.basicOpen f) (X.presheaf.map (homOfLE (X.basicOpen_le f)).op a) := by
  rw [isSMulRegular_iff_right_eq_zero_of_smul]
  intro m hm
  obtain ⟨n, t, ht⟩ := exists_power_mul_eq_restriction M hU f m
  have h1 : M.presheaf.map (homOfLE (X.basicOpen_le f)).op (a • t) = 0 := by
    rw [Scheme.Modules.map_smul, ht, smul_comm, hm, smul_zero]
  obtain ⟨k, hk⟩ := exists_power_smul_eq_zero M hU f (a • t) h1
  have h2 : f ^ k • t = 0 := by
    apply ha.right_eq_zero_of_smul
    rw [smul_comm, hk]
  have h3 : (X.presheaf.map (homOfLE (X.basicOpen_le f)).op f) ^ (k + n) • m = 0 := by
    rw [pow_add, mul_smul, ← ht, ← map_pow, ← Scheme.Modules.map_smul, h2, map_zero]
  have hu : IsUnit ((X.presheaf.map (homOfLE (X.basicOpen_le f)).op f) ^ (k + n)) :=
    (X.toRingedSpace.isUnit_res_basicOpen f).pow (k + n)
  exact (hu.smul_left_cancel).mp (h3.trans (smul_zero _).symm)

/-- **Nonzerodivisors restrict to subopens**: a nonzerodivisor `a` on the sections over an
affine open `U` restricts to a nonzerodivisor on the sections over every open `V ≤ U`. -/
theorem isSMulRegular_restrict (hU : IsAffineOpen U)
    [(M.restrict hU.fromSpec).IsQuasicoherent] {a : Γ(X, U)} (ha : IsSMulRegular Γ(M, U) a)
    {V : X.Opens} (hVU : V ≤ U) :
    IsSMulRegular Γ(M, V) (X.presheaf.map (homOfLE hVU).op a) := by
  rw [isSMulRegular_iff_right_eq_zero_of_smul]
  intro m hm
  have hc : Presheaf.equalizerSieve (F := M.val.presheaf) m 0 ∈
      (Opens.grothendieckTopology X) V := by
    intro x hxV
    obtain ⟨f, hfV, hxf⟩ := hU.exists_basicOpen_le ⟨x, hxV⟩ (hVU hxV)
    refine ⟨X.basicOpen f, homOfLE hfV, ?_, hxf⟩
    change M.presheaf.map (homOfLE hfV).op m = M.presheaf.map (homOfLE hfV).op 0
    rw [map_zero]
    apply (isSMulRegular_basicOpen M hU ha f).right_eq_zero_of_smul
    have hres : X.presheaf.map (homOfLE (X.basicOpen_le f)).op a =
        X.presheaf.map (homOfLE hfV).op (X.presheaf.map (homOfLE hVU).op a) := by
      rw [← CommRingCat.comp_apply, ← Functor.map_comp]
      rfl
    rw [hres, ← Scheme.Modules.map_smul, hm, map_zero]
  apply M.isSheaf.isSeparated V _ hc
  intro W j hj
  exact hj

end AlgebraicGeometry.Scheme.Modules.QuasiCoherent.AffineOpenSections
