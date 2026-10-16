/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Actual scalar adjunctions along surjective ring maps

Scalar restriction along a surjective ring map is fully faithful on all
modules. Its essential image consists of the modules annihilated by the
original ring-map kernel. For commutative rings this characterizes
invertibility of the original extension/restriction unit and proves
invertibility of its original counit. No finite-generation hypothesis is used.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace ModuleCat

variable {R : Type u} {S : Type w}

section Ring

variable [Ring R] [Ring S] (φ : R →+* S)

/-- Scalar restriction along a surjective ring map is fully faithful on
arbitrary modules, with the actual original linear maps as preimages. -/
def fullyFaithfulRestrictScalarsOfSurjective (hφ : Function.Surjective φ) :
    (restrictScalars.{v} φ).FullyFaithful where
  preimage {M N} f := ofHom
    { toFun := f.hom
      map_add' := f.hom.map_add
      map_smul' := by
        intro a m
        obtain ⟨r, rfl⟩ := hφ a
        exact f.hom.map_smul r m }

/-- The kernel of a ring map annihilates every actual restricted module. -/
theorem ker_le_annihilator_restrictScalars (N : ModuleCat.{v} S) :
    RingHom.ker φ ≤ Module.annihilator R ((restrictScalars φ).obj N) := by
  intro r hr
  rw [Module.mem_annihilator]
  intro n
  rw [restrictScalars.smul_def, RingHom.mem_ker.mp hr, zero_smul]

/-- An arbitrary module descends through a surjective ring map exactly
when the original ring-map kernel annihilates it. -/
theorem mem_essImage_restrictScalars_iff_ker_le_annihilator
    (hφ : Function.Surjective φ) (M : ModuleCat.{v} R) :
    (restrictScalars φ).essImage M ↔ RingHom.ker φ ≤ Module.annihilator R M := by
  constructor
  · rintro ⟨N, ⟨e⟩⟩ r hr
    rw [Module.mem_annihilator]
    intro m
    apply e.toLinearEquiv.symm.injective
    change e.inv (r • m) = e.inv 0
    rw [e.inv.hom.map_smul, map_zero]
    change φ r • (show N from e.inv m) = 0
    rw [RingHom.mem_ker.mp hr, zero_smul]
  · intro hM
    have hT : Module.IsTorsionBySet R M (RingHom.ker φ) :=
      fun {m} {r} => (Module.mem_annihilator.mp (hM r.property)) m
    let : Module (R ⧸ RingHom.ker φ) M := hT.module
    let e := φ.quotientKerEquivOfSurjective hφ
    let : Module S M := Module.compHom M e.symm.toRingHom
    let N : ModuleCat.{v} S := ModuleCat.of S M
    let eM : (restrictScalars φ).obj N ≃ₗ[R] M :=
      { toFun := fun m => m
        invFun := fun m => m
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := by
          intro r m
          change e.symm (φ r) • (show M from m) = r • (show M from m)
          rw [RingHom.quotientKerEquivOfSurjective_symm_apply]
          rfl }
    exact ⟨N, ⟨eM.toModuleIso⟩⟩

end Ring

section CommRing

variable [CommRing R] [CommRing S] (φ : R →+* S)

/-- Surjective scalar restriction makes the original extension/restriction
counit invertible on every original module. -/
theorem extendRestrictScalarsAdj_counit_isIso_of_surjective
    (hφ : Function.Surjective φ) (N : ModuleCat.{max v w} S) :
    IsIso ((extendRestrictScalarsAdj φ).counit.app N) := by
  let := (fullyFaithfulRestrictScalarsOfSurjective φ hφ).full
  infer_instance

/-- The original extension/restriction unit is invertible precisely on
modules annihilated by the original kernel, without a finiteness hypothesis. -/
theorem extendRestrictScalarsAdj_unit_isIso_iff_ker_le_annihilator
    (hφ : Function.Surjective φ) (M : ModuleCat.{max v w} R) :
    IsIso ((extendRestrictScalarsAdj φ).unit.app M) ↔
      RingHom.ker φ ≤ Module.annihilator R M := by
  let := (fullyFaithfulRestrictScalarsOfSurjective φ hφ).full
  exact (extendRestrictScalarsAdj φ).isIso_unit_app_iff_mem_essImage.trans
    (mem_essImage_restrictScalars_iff_ker_le_annihilator φ hφ M)

end CommRing

end ModuleCat
