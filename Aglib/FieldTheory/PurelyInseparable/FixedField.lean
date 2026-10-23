/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!
# The full automorphism fixed field of a normal extension

The field fixed by every automorphism of a normal field extension is purely
inseparable over the original base. Normality suffices; the extension need not
be finite or separable.
-/

@[expose] public noncomputable section

namespace IntermediateField

/-- The full automorphism fixed field of a normal field extension is purely
inseparable over the original base, without a finite-dimensionality assumption. -/
theorem isPurelyInseparable_fixedField_top
    (K M : Type*) [Field K] [Field M] [Algebra K M] [Normal K M] :
    IsPurelyInseparable K (fixedField (⊤ : Subgroup (M ≃ₐ[K] M))) := by
  classical
  let F : IntermediateField K M := fixedField (⊤ : Subgroup (M ≃ₐ[K] M))
  change IsPurelyInseparable K F
  apply (isPurelyInseparable_iff_subsingleton_emb K F).mpr
  refine ⟨fun f g ↦ ?_⟩
  obtain ⟨f', hf'⟩ := IsAlgClosed.surjective_domRestrict_of_isAlgebraic
    (K := K) (L := F) (M := AlgebraicClosure F) (E := M) f
  obtain ⟨g', hg'⟩ := IsAlgClosed.surjective_domRestrict_of_isAlgebraic
    (K := K) (L := F) (M := AlgebraicClosure F) (E := M) g
  let : Algebra M (AlgebraicClosure F) := f'.toRingHom.toAlgebra
  let : IsScalarTower K M (AlgebraicClosure F) :=
    IsScalarTower.of_algebraMap_eq fun k ↦ (f'.commutes k).symm
  apply AlgHom.ext
  intro x
  have hfix : g'.restrictNormal' M (x : M) = (x : M) :=
    (mem_fixedField_iff (⊤ : Subgroup (M ≃ₐ[K] M)) (x : M)).mp x.property
      (g'.restrictNormal' M) (Subgroup.mem_top _)
  have hcomm : f' (g'.restrictNormal' M (x : M)) = g' (x : M) := by
    change algebraMap M (AlgebraicClosure F) (g'.restrictNormal M (x : M)) =
      g' (algebraMap M M (x : M))
    exact g'.restrictNormal_commutes M (x : M)
  calc
    f x = f' (x : M) :=
      (congrArg (fun h : F →ₐ[K] AlgebraicClosure F ↦ h x) hf').symm
    _ = f' (g'.restrictNormal' M (x : M)) := congrArg f' hfix.symm
    _ = g' (x : M) := hcomm
    _ = g x := congrArg (fun h : F →ₐ[K] AlgebraicClosure F ↦ h x) hg'

end IntermediateField
