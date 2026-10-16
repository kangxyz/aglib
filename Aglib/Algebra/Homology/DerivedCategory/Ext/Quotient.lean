/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The actual quotient-ring action on native Ext from a ring quotient

The original R-action on Ext from R/I is annihilated by I. The native
annihilated-module construction makes it an R/I-module. Its action is
proved equal to original Yoneda precomposition with multiplication on R/I,
which is the action used by scalar coinduction. No regularity, finiteness,
Noetherianity or alternate Ext implementation is involved.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Abelian

universe u w

namespace CategoryTheory.Abelian.Ext

variable {R : Type u} [CommRing R] [HasExt.{w} (ModuleCat.{u} R)]
  (I : Ideal R) (N : ModuleCat.{u} R) (n : ℕ)

/-- The original scalar action on Ext from R/I is killed by the defining ideal. -/
theorem quotientSourceIsTorsionBySet :
    Module.IsTorsionBySet R (Ext (ModuleCat.of R (R ⧸ I)) N n) I := by
  intro e a
  have ha : (a : R) • 𝟙 (ModuleCat.of R (R ⧸ I)) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro b
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective b
    change Ideal.Quotient.mk I ((a : R) * r) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (I.mul_mem_right r a.property)
  calc
    (a : R) • e = (mk₀ ((a : R) • 𝟙 (ModuleCat.of R (R ⧸ I)))).comp e
        (zero_add n) := by
      simp only [mk₀_smul, smul_comp, mk₀_id_comp]
    _ = 0 := by rw [ha]; simp

/-- The native quotient-ring module structure on the unchanged original Ext group.
This is explicit rather than a global instance, retaining the original R-action. -/
@[instance_reducible]
def quotientSourceModule : Module (R ⧸ I) (Ext (ModuleCat.of R (R ⧸ I)) N n) :=
  (quotientSourceIsTorsionBySet I N n).module

/-- A representative in R acts by the unchanged native R-scalar multiplication on Ext. -/
@[simp]
theorem quotientSourceModule_mk_smul (r : R)
    (e : Ext (ModuleCat.of R (R ⧸ I)) N n) :
    letI := quotientSourceModule I N n
    Ideal.Quotient.mk I r • e = r • e :=
  Module.IsTorsionBySet.mk_smul (quotientSourceIsTorsionBySet I N n) r e

/-- Right multiplication on the actual quotient is an original R-linear source endomorphism. -/
def quotientSourceMul (b : R ⧸ I) :
    ModuleCat.of R (R ⧸ I) ⟶ ModuleCat.of R (R ⧸ I) :=
  ModuleCat.ofHom (LinearMap.mulRight R b)

omit [HasExt.{w} (ModuleCat.{u} R)] in
/-- Multiplication by a ring representative is the original scalar endomorphism. -/
@[simp]
theorem quotientSourceMul_mk (r : R) :
    quotientSourceMul I (Ideal.Quotient.mk I r) =
      r • 𝟙 (ModuleCat.of R (R ⧸ I)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective b
  change Ideal.Quotient.mk I (s * r) = Ideal.Quotient.mk I (r * s)
  rw [mul_comm]

/-- The quotient action is exactly original Yoneda precomposition with source multiplication. -/
theorem quotientSourceModule_smul_eq_precomp (b : R ⧸ I)
    (e : Ext (ModuleCat.of R (R ⧸ I)) N n) :
    letI := quotientSourceModule I N n
    b • e = (mk₀ (quotientSourceMul I b)).comp e (zero_add n) := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [quotientSourceModule_mk_smul, quotientSourceMul_mk]
  simp only [mk₀_smul, smul_comp, mk₀_id_comp]

end CategoryTheory.Abelian.Ext
