/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineQuotient
public import Aglib.AlgebraicGeometry.Modules.ClosedImmersion.Support

/-! # Actual affine coordinates of ideal-sheaf annihilation

The ideal and the action are both transported by the original `ΓSpecIso`.
The forward statement holds for every module sheaf. Quasicoherence is used
only to recover sheaf annihilation from the original affine global sections.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules.Coherent

variable (B : CommRingCat.{u}) (K : (Spec B).IdealSheafData)
  (M : (Spec B).Modules)

/-- Actual ideal-sheaf annihilation bounds the annihilator of the original
Spec-coordinate module, with its original scalar action. -/
theorem affineIdeal_le_annihilator_of_killed (h : killedByIdealSheaf K M) :
    affineIdeal B K ≤ Module.annihilator B (moduleSpecΓFunctor.obj M) := by
  rw [affineIdeal, Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, Module.mem_annihilator]
  intro m
  change (Scheme.ΓSpecIso B).inv ((Scheme.ΓSpecIso B).hom a) • (show Γ(M, ⊤) from m) = 0
  rw [Iso.hom_inv_id_apply]
  exact h ⟨⊤, isAffineOpen_top _⟩ a ha m

/-- On a quasicoherent affine module sheaf, original coordinate annihilation
is equivalent to actual ideal-sheaf annihilation. -/
theorem killed_iff_affineIdeal_le_annihilator [M.IsQuasicoherent] :
    killedByIdealSheaf K M ↔
      affineIdeal B K ≤ Module.annihilator B (moduleSpecΓFunctor.obj M) := by
  refine ⟨affineIdeal_le_annihilator_of_killed B K M, fun h => ?_⟩
  apply killedByIdealSheaf_of_affineCover K M
    (fun _ : Unit => (⟨⊤, isAffineOpen_top _⟩ : (Spec B).affineOpens))
  · intro x
    exact ⟨(), trivial⟩
  · intro i a ha
    rw [Module.mem_annihilator]
    intro m
    have hm := (Module.mem_annihilator.mp
      (h (Ideal.mem_map_of_mem (Scheme.ΓSpecIso B).hom.hom ha))) m
    change (Scheme.ΓSpecIso B).inv ((Scheme.ΓSpecIso B).hom a) • (show Γ(M, ⊤) from m) = 0 at hm
    simpa only [Iso.hom_inv_id_apply] using hm

/-- The original geometric power becomes the same power of the actual
affine coordinate ideal, with no change of ideal or exponent. -/
theorem affineIdeal_pow_le_annihilator_of_killed (n : ℕ)
    (h : killedByIdealSheaf (K ^ n) M) :
    affineIdeal B K ^ n ≤ Module.annihilator B (moduleSpecΓFunctor.obj M) := by
  simpa only [affineIdeal_pow] using affineIdeal_le_annihilator_of_killed B (K ^ n) M h

end AlgebraicGeometry.Scheme.Modules.Coherent
