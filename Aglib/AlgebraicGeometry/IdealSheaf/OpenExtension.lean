/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Extension of ideal sheaves from quasi-compact open immersions

The native pushforward ideal is the ideal of the schematic closure of the closed
subscheme. Its restriction is the original ideal, and a protected open on which
the original ideal is the unit ideal remains disjoint from the extended centre.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}}

/-- Schematic closure along a quasi-compact open immersion restricts to the
original closed subscheme, with equality of the actual ideal sheaves. -/
@[simp]
theorem comap_map_of_isOpenImmersion (J : Y.IdealSheafData) (j : Y ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] : (J.map j).comap j = J := by
  ext W
  rw [ideal_comap_of_isOpenImmersion, map]
  have h : IsPullback J.subschemeι (𝟙 _) j (J.subschemeι ≫ j) :=
    IsPullback.of_vert_isIso_mono ⟨by simp⟩
  rw [← ker_ideal_of_isPullback_of_isOpenImmersion
    (J.subschemeι ≫ j) J.subschemeι (𝟙 _) j h W, ker_subschemeι]

/-- If an ideal on an open subscheme is the unit ideal over a protected open,
its schematic closure is still the unit ideal over that protected open. -/
theorem map_comap_eq_top_of_comap_eq_top (J : Y.IdealSheafData) (j : Y ⟶ X)
    [QuasiCompact j] (U : X.Opens)
    (hJ : J.comap (j ⁻¹ᵁ U).ι = ⊤) : (J.map j).comap U.ι = ⊤ := by
  have havoid : j '' (J.support : Set Y) ⊆ (U : Set X)ᶜ := by
    rintro _ ⟨y, hy, rfl⟩ hyU
    have hsupport := congrArg support hJ
    rw [support_comap, support_top] at hsupport
    have hm : (⟨y, hyU⟩ : (j ⁻¹ᵁ U).toScheme) ∈
        J.support.preimage (j ⁻¹ᵁ U).ι.continuous := hy
    rw [hsupport] at hm
    exact hm
  have hclosure : closure (j '' (J.support : Set Y)) ⊆ (U : Set X)ᶜ :=
    closure_minimal havoid U.isOpen.isClosed_compl
  apply (support_eq_bot_iff _).mp
  rw [support_comap, support_map]
  ext x
  change (x.val ∈ closure (j '' (J.support : Set Y))) ↔ False
  exact iff_false_intro (fun hx ↦ hclosure hx x.property)

/-- A centre on a quasi-compact open extends literally, while remaining the
unit ideal on a second prescribed open. No Noetherian hypothesis is needed. -/
theorem exists_extension_eq_top (U V : X.Opens) [QuasiCompact V.ι]
    (J : V.toScheme.IdealSheafData) (hJ : J.comap (V.ι ⁻¹ᵁ U).ι = ⊤) :
    ∃ I : X.IdealSheafData, I.comap V.ι = J ∧ I.comap U.ι = ⊤ :=
  ⟨J.map V.ι, comap_map_of_isOpenImmersion J V.ι,
    map_comap_eq_top_of_comap_eq_top J V.ι U hJ⟩

end AlgebraicGeometry.Scheme.IdealSheafData
