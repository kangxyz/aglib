/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.ClosedImmersion.Locality

/-! # Ideal annihilation under ordinary sheaf quotients and ideal sums -/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {X : Scheme.{u}}

/-- An ordinary sheaf epimorphism preserves annihilation, with no
quasicoherence hypothesis. Surjectivity is used only on actual stalks. -/
theorem killedByIdealSheaf_of_epi (I : X.IdealSheafData)
    {M N : X.Modules} (f : M ⟶ N) [Epi f] (hM : killedByIdealSheaf I M) :
    killedByIdealSheaf I N := by
  apply (killedByIdealSheaf_iff_germ_smul_eq_zero I N).mpr
  intro U x hx a ha m
  obtain ⟨s, rfl⟩ := (ModuleCat.epi_iff_surjective ((moduleStalk X x).map f)).mp
    inferInstance m
  rw [← ((moduleStalk X x).map f).hom.map_smul,
    killedByIdealSheaf_germ_smul_eq_zero I M hM U x hx a ha, map_zero]

/-- The sum of two independent ideals annihilates exactly their common
annihilated coefficients. -/
theorem killedByIdealSheaf_sup_iff (I K : X.IdealSheafData) (M : X.Modules) :
    killedByIdealSheaf (I ⊔ K) M ↔
      killedByIdealSheaf I M ∧ killedByIdealSheaf K M := by
  simp only [killedByIdealSheaf_iff_le_annihilator]
  change (∀ U, I.ideal U ⊔ K.ideal U ≤ _) ↔ _
  simp only [sup_le_iff, forall_and]

end AlgebraicGeometry.Scheme.Modules
