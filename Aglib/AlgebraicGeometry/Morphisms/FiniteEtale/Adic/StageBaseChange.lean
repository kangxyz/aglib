/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Nilpotent
public import Aglib.AlgebraicGeometry.IdealSheaf.Closed.MonoFactor
public import Aglib.AlgebraicGeometry.IdealSheaf.Colon
public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.Completion

/-!
# Finite etale base change between actual ideal-power thickenings

The native inclusions of positive thickenings have nilpotent kernel, so the
existing global nilpotent equivalence applies to their literal base-change
functors. Index zero is excluded from this nilpotence assertion.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.FiniteEtale.Adic

variable {X : Scheme.{u}} (K : X.IdealSheafData)

/-- The native inclusion from the smaller thickening to the larger one. -/
abbrev stageMap {n m : ℕ} (h : n ≤ m) : (K ^ n).subscheme ⟶ (K ^ m).subscheme :=
  IdealSheafData.inclusion (Modules.Coherent.idealSheaf_pow_le X K h)

@[reassoc]
theorem stageMap_ι {n m : ℕ} (h : n ≤ m) :
    stageMap K h ≫ (K ^ m).subschemeι = (K ^ n).subschemeι :=
  IdealSheafData.inclusion_subschemeι _

theorem stageMap_refl (n : ℕ) : stageMap K (le_refl n) = 𝟙 _ :=
  IdealSheafData.inclusion_id _

@[reassoc]
theorem stageMap_comp {n m k : ℕ} (h : n ≤ m) (h' : m ≤ k) :
    stageMap K h ≫ stageMap K h' = stageMap K (h.trans h') :=
  IdealSheafData.inclusion_comp _ _

/-- The map between original power thickenings is a closed immersion. -/
instance instIsClosedImmersionStageMap {n m : ℕ} (h : n ≤ m) :
    IsClosedImmersion (stageMap K h) := by
  have : IsClosedImmersion (stageMap K h ≫ (K ^ m).subschemeι) := by
    rw [stageMap_ι]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ (K ^ m).subschemeι

/-- The kernel of the original transition is the original pulled-back ideal. -/
theorem stageMap_ker {n m : ℕ} (h : n ≤ m) :
    (stageMap K h).ker = (K ^ n).comap (K ^ m).subschemeι := by
  have hk := IdealSheafData.ker_comap_of_mono (stageMap K h) (K ^ m).subschemeι
  rw [stageMap_ι, IdealSheafData.ker_subschemeι] at hk
  exact hk.symm

/-- Every transition whose source index is positive is a nilpotent thickening. -/
theorem stageMap_ker_isNilpotent {n m : ℕ} (h : n ≤ m) (hn : 0 < n) :
    IsNilpotent (stageMap K h).ker := by
  refine ⟨m, ?_⟩
  rw [stageMap_ker, ← IdealSheafData.comap_pow, ← pow_mul]
  apply le_bot_iff.mp
  calc
    (K ^ (n * m)).comap (K ^ m).subschemeι ≤ (K ^ m).comap (K ^ m).subschemeι :=
      IdealSheafData.comap_mono _ (Modules.Coherent.idealSheaf_pow_le X K
        (by simpa using Nat.mul_le_mul_right m hn))
    _ = ⊥ := IdealSheafData.comap_subschemeι_self _

/-- The literal finite-etale base change between positive stages is an equivalence. -/
theorem stageMap_baseChange_isEquivalence {n m : ℕ} (h : n ≤ m) (hn : 0 < n) :
    (baseChange (stageMap K h)).IsEquivalence :=
  Nilpotent.closedImmersion_baseChange_isEquivalence _ (stageMap_ker_isNilpotent K h hn)

end AlgebraicGeometry.Scheme.FiniteEtale.Adic
