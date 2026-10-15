/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.ShortComplex.BaseChange.LocalFreeness
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# The adjacent-degree local cohomology and base-change criterion

For a complex over a local ring, assume the original residue-field
comparison in degree `i` is surjective. Its original homology in that
degree is free exactly when the original comparison in degree `i - 1`
is surjective. Only three neighboring terms are finite and the last two
are flat; no term bounds or Noetherianity are required.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CochainComplex

universe u v

variable {R : Type u} [CommRing R] [IsLocalRing R]
    (K : CochainComplex (ModuleCat.{max u v} R) ℤ)

/-- Under surjectivity of the original degree-`i` residue-field map, freeness of the
original degree-`i` homology is equivalent to surjectivity of the predecessor map. -/
theorem free_homology_iff_epi_residue_predecessor (i : ℤ)
    [Module.Finite R (K.X (i - 1))] [Module.Finite R (K.X i)]
    [Module.Finite R (K.X (i + 1))] [Module.Flat R (K.X i)] [Module.Flat R (K.X (i + 1))]
    [Epi (extendScalarsHomologyMap (algebraMap R (IsLocalRing.ResidueField R)) K i)] :
    Module.Free R (K.homology i) ↔
      Epi (extendScalarsHomologyMap (algebraMap R (IsLocalRing.ResidueField R)) K (i - 1)) := by
  have hn : (ComplexShape.up ℤ).next i = i + 1 := (ComplexShape.up ℤ).next_eq' rfl
  have hp : (ComplexShape.up ℤ).prev i = i - 1 :=
    (ComplexShape.up ℤ).prev_eq' (by change (i - 1) + 1 = i; omega)
  have hnp : (ComplexShape.up ℤ).next (i - 1) = i :=
    (ComplexShape.up ℤ).next_eq' (by change (i - 1) + 1 = i; omega)
  let : Module.Finite R (K.sc i).X₂ := by
    change Module.Finite R (K.X i)
    infer_instance
  let : Module.Finite R (K.sc i).X₃ := by
    change Module.Finite R (K.X ((ComplexShape.up ℤ).next i))
    rw [hn]
    infer_instance
  let : Module.Flat R (K.sc i).X₃ := by
    change Module.Flat R (K.X ((ComplexShape.up ℤ).next i))
    rw [hn]
    infer_instance
  have hcurrent := (K.sc i).free_homology_iff_free_opcycles_of_epi_residue
  change Module.Free R (K.homology i) ↔ Module.Free R (K.opcycles i) at hcurrent
  let T := K.sc (i - 1)
  let : Module.Finite R T.X₂ := by
    change Module.Finite R (K.X (i - 1))
    infer_instance
  let : Module.Finite R T.X₃ := by
    change Module.Finite R (K.X ((ComplexShape.up ℤ).next (i - 1)))
    rw [hnp]
    infer_instance
  let : Module.Flat R T.X₃ := by
    change Module.Flat R (K.X ((ComplexShape.up ℤ).next (i - 1)))
    rw [hnp]
    infer_instance
  have hprev := T.epi_residue_homologyBaseChangeMap_iff_free_cokernel
  change Epi (extendScalarsHomologyMap (algebraMap R (IsLocalRing.ResidueField R))
    K (i - 1)) ↔ Module.Free R (cokernel T.g : ModuleCat.{max u v} R) at hprev
  have hpn : (ComplexShape.up ℤ).prev ((ComplexShape.up ℤ).next (i - 1)) = i - 1 := by
    rw [hnp, hp]
  let e' : K.opcycles ((ComplexShape.up ℤ).next (i - 1)) ≅ cokernel T.g :=
    (K.opcyclesIsCokernel (i - 1) _ hpn).coconePointUniqueUpToIso (colimit.isColimit _)
  let e : K.opcycles i ≅ cokernel T.g :=
    eqToIso (congrArg (fun j : ℤ => K.opcycles j) hnp.symm) ≪≫ e'
  have he : Module.Free R (K.opcycles i) ↔
      Module.Free R (cokernel T.g : ModuleCat.{max u v} R) := by
    constructor
    · intro h
      let := h
      exact Module.Free.of_equiv e.toLinearEquiv
    · intro h
      let := h
      exact Module.Free.of_equiv e.symm.toLinearEquiv
  exact hcurrent.trans (he.trans hprev.symm)

end CochainComplex
