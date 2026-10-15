/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.ShortComplex.Adjunction
public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# Exact cycle sequences from a surjective homology comparison

The original cycles, their inclusion and the outgoing differential form
an exact short complex. The canonical map from the original short complex
fixes its middle and last objects. If an additive adjunction's homology
comparison is an epimorphism, its left adjoint preserves exactness of this
displayed cycle sequence. The proof uses the original comparison's
coefficient naturality; no exactness premise on the left adjoint is added.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ShortComplex

variable {C : Type*} [Category* C] [Abelian C] (S : ShortComplex C)

/-- The exact sequence of the original cycles, middle object and outgoing arrow. -/
def cyclesShortComplex : ShortComplex C :=
  ShortComplex.mk S.iCycles S.g S.iCycles_g

/-- The original cycles give the kernel of the outgoing differential. -/
theorem cyclesShortComplex_exact : S.cyclesShortComplex.Exact :=
  exact_of_f_is_kernel _ S.cyclesIsKernel

/-- The canonical map to the cycle sequence retains both original final objects. -/
def toCyclesShortComplex : S ⟶ S.cyclesShortComplex where
  τ₁ := S.toCycles
  τ₂ := 𝟙 _
  τ₃ := 𝟙 _
  comm₁₂ := by simp [cyclesShortComplex, S.toCycles_i]
  comm₂₃ := by simp [cyclesShortComplex]

end CategoryTheory.ShortComplex

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive] [G.PreservesHomology]

/-- A surjective original homology comparison forces exactness of the actual mapped cycle
sequence. The left adjoint need not preserve kernels or homology. -/
theorem exact_map_cyclesShortComplex_of_epi_homologyComparison
    (adj : F ⊣ G) (S : ShortComplex C) [Epi (adj.homologyComparison S)] :
    (S.cyclesShortComplex.map F).Exact := by
  let T := S.cyclesShortComplex
  let f := S.toCyclesShortComplex
  let φ := F.mapShortComplex.map f
  let : IsIso φ.τ₂ := by
    change IsIso (F.map (𝟙 S.X₂))
    rw [F.map_id]
    infer_instance
  let : Mono φ.τ₃ := by
    change Mono (F.map (𝟙 S.X₃))
    rw [F.map_id]
    infer_instance
  let : Epi (ShortComplex.homologyMap φ) := inferInstance
  have hz : F.map (ShortComplex.homologyMap f) = 0 :=
    (F.map_isZero ((T.exact_iff_isZero_homology).mp S.cyclesShortComplex_exact)).eq_of_tgt _ _
  have hw : adj.homologyComparison S ≫ ShortComplex.homologyMap φ = 0 := by
    rw [← adj.homologyComparison_naturality f, hz, zero_comp]
  apply (S.cyclesShortComplex.map F).exact_iff_isZero_homology.mpr
  apply IsZero.of_epi_eq_zero (ShortComplex.homologyMap φ)
  apply (cancel_epi (adj.homologyComparison S)).mp
  simpa only [comp_zero] using hw

end CategoryTheory.Adjunction
