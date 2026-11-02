/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.LocalRing.Length

/-!
# Finite length for the original finite local scalar restriction

The original finite local ring map preserves finite length by the native
residue-degree length formula. No surjectivity or Noetherianity is required.
-/

@[expose] public noncomputable section

universe u v w

namespace ModuleCat

/-- The literal restricted module, with the original action through sigma. -/
theorem finiteLength_restrictScalars_of_finite_local
    {R : Type u} {A : Type v} [CommRing R] [CommRing A]
    [IsLocalRing R] [IsLocalRing A]
    (sigma : R →+* A) [IsLocalHom sigma] (hfinite : sigma.Finite)
    (M : ModuleCat.{w} A) (hM : IsFiniteLength A M) :
    IsFiniteLength R ((ModuleCat.restrictScalars sigma).obj M) := by
  let : Algebra R A := sigma.toAlgebra
  let : Module.Finite R A := hfinite
  let : IsLocalHom (algebraMap R A) := inferInstanceAs (IsLocalHom sigma)
  let : Module R M := Module.compHom M sigma
  let : IsScalarTower R A M :=
    ⟨fun r a x => by
      change (r • a) • x = sigma r • (a • x)
      rw [Algebra.smul_def]
      exact mul_smul _ _ _⟩
  change IsFiniteLength R M
  apply Module.length_ne_top_iff.mp
  rw [IsLocalRing.length_restrictScalars R A M]
  obtain ⟨l, hl⟩ := ENat.ne_top_iff_exists.mp (Module.length_ne_top_iff.mpr hM)
  rw [← hl, Module.length_eq_finrank, ← ENat.natCast_mul]
  exact ENat.natCast_ne_top _

end ModuleCat
