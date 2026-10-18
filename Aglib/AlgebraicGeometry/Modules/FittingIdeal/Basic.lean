/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.FittingIdeal.BaseChange
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Sections
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Localization.AffineOpenSections
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-!
# Fitting ideal sheaves

Let `M` be a quasi-coherent `𝒪_X`-module of finite type on a scheme `X`, in the sense of Aglib's
`Scheme.Modules.QuasiCoherent.affineLocallyFiniteType`: on every affine chart the restriction is
quasi-coherent with finitely generated global sections. For `k : ℕ`, the `k`-th Fitting ideal sheaf
`Scheme.Modules.fittingIdealSheaf M hM k : X.IdealSheafData` has, on every affine open `U`, the
ideal `Fitt_k(Γ(M, U)) ⊆ Γ(X, U)` (`ideal_fittingIdealSheaf`). This is the quasi-coherent sheaf of
ideals of Stacks Project, Tag 0C3C (Section 31.9, Fitting ideals), restricted to finite type
modules. The finite generation of the sections on an affine open is
`QuasiCoherent.finite_sections_of_affineLocallyFiniteType`.

* `fittingIdeal_sections_basicOpen`: Fitting ideals of sections commute with restriction to basic
  opens. The restriction `Γ(M, U) → Γ(M, D(f))` is a localization at `f` (by the denominator
  clearing of `AffineOpenSections`), and Fitting ideals commute with localization
  (`Module.fittingIdeal_of_isLocalizedModule`, Stacks, Tag 07ZA (3)); this is the ideal-sheaf
  condition of Stacks, Tag 0C3C.
* `fittingIdealSheaf_mono`: `Fitt_k ⊆ Fitt_l` for `k ≤ l` (Stacks, Tag 07Z9 on each affine).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (M : X.Modules)

/-- Fitting ideals of the sections of a quasi-coherent sheaf of finite type commute with restriction
from an affine open `U` to a basic open `D(f) ⊆ U`: the restriction of sections is a localization at
`f`, and Fitting ideals commute with localization (Stacks Project, Tag 07ZA (3)). -/
theorem fittingIdeal_sections_basicOpen (hM : QuasiCoherent.affineLocallyFiniteType X M)
    (U : X.affineOpens) (f : Γ(X, U)) (k : ℕ) :
    (Module.fittingIdeal Γ(X, U) Γ(M, U) k).map
        (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom =
      Module.fittingIdeal Γ(X, X.basicOpen f) Γ(M, X.basicOpen f) k := by
  have hU : IsAffineOpen U.1 := U.2
  have : (M.restrict hU.fromSpec).IsQuasicoherent := (hM Γ(X, U) hU.fromSpec).1
  have := QuasiCoherent.finite_sections_of_affineLocallyFiniteType M hM U
  have := hU.isLocalization_basicOpen f
  let : Module Γ(X, U) Γ(M, X.basicOpen f) :=
    Module.compHom _ (algebraMap Γ(X, U) Γ(X, X.basicOpen f))
  have : IsScalarTower Γ(X, U) Γ(X, X.basicOpen f) Γ(M, X.basicOpen f) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let g : Γ(M, U) →ₗ[Γ(X, U)] Γ(M, X.basicOpen f) :=
    { toFun := M.presheaf.map (homOfLE (X.basicOpen_le f)).op
      map_add' := map_add _
      map_smul' := fun r x => M.map_smul (homOfLE (X.basicOpen_le f)) r x }
  have : IsLocalizedModule (Submonoid.powers f) g := by
    refine ⟨fun x => ?_, fun y => ?_, fun {x₁ x₂} hx => ?_⟩
    · rw [Module.End.isUnit_iff]
      have hu : IsUnit (algebraMap Γ(X, U) Γ(X, X.basicOpen f) x) :=
        IsLocalization.map_units _ x
      have e : ⇑(algebraMap Γ(X, U) (Module.End Γ(X, U) Γ(M, X.basicOpen f)) x) =
          ⇑(algebraMap Γ(X, X.basicOpen f) (Module.End Γ(X, X.basicOpen f) Γ(M, X.basicOpen f))
            (algebraMap Γ(X, U) Γ(X, X.basicOpen f) x)) := rfl
      rw [e, ← Module.End.isUnit_iff]
      exact hu.map _
    · obtain ⟨n, t, ht⟩ :=
        QuasiCoherent.AffineOpenSections.exists_power_mul_eq_restriction M hU f y
      refine ⟨⟨t, ⟨f ^ n, n, rfl⟩⟩, ?_⟩
      change (algebraMap Γ(X, U) Γ(X, X.basicOpen f) (f ^ n)) • y =
        M.presheaf.map (homOfLE (X.basicOpen_le f)).op t
      rw [ht, map_pow]
      rfl
    · have h0 : M.presheaf.map (homOfLE (X.basicOpen_le f)).op (x₁ - x₂) = 0 := by
        rw [map_sub]
        exact sub_eq_zero.mpr hx
      obtain ⟨n, hn⟩ :=
        QuasiCoherent.AffineOpenSections.exists_power_smul_eq_zero M hU f _ h0
      refine ⟨⟨f ^ n, n, rfl⟩, ?_⟩
      rw [Submonoid.smul_def, Submonoid.smul_def, ← sub_eq_zero, ← smul_sub]
      exact hn
  exact (Module.fittingIdeal_of_isLocalizedModule (Submonoid.powers f) g k).symm

/-- The `k`-th **Fitting ideal sheaf** of a quasi-coherent sheaf of finite type `M`: on every affine
open `U` its ideal is `Fitt_k(Γ(M, U))` (Stacks Project, Tag 0C3C). -/
def fittingIdealSheaf (hM : QuasiCoherent.affineLocallyFiniteType X M) (k : ℕ) :
    X.IdealSheafData where
  ideal U := Module.fittingIdeal Γ(X, U) Γ(M, U) k
  map_ideal_basicOpen U f := fittingIdeal_sections_basicOpen M hM U f k

@[simp]
theorem ideal_fittingIdealSheaf (hM : QuasiCoherent.affineLocallyFiniteType X M) (k : ℕ)
    (U : X.affineOpens) :
    (fittingIdealSheaf M hM k).ideal U = Module.fittingIdeal Γ(X, U) Γ(M, U) k :=
  rfl

/-- The Fitting ideal sheaves increase with `k` (Stacks Project, Tag 07Z9, on every affine
open). -/
theorem fittingIdealSheaf_mono (hM : QuasiCoherent.affineLocallyFiniteType X M) :
    Monotone (fittingIdealSheaf M hM) := fun _ _ hkl _ =>
  Module.fittingIdeal_mono hkl

end AlgebraicGeometry.Scheme.Modules
