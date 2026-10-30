/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.AlgebraicGeometry.Limits

/-! # Unramified maps detected after an actual surjective source map

The full original open-diagonal equalizer argument uses only the given
surjective source, formal unramifiedness and local finite type. No separated,
connected, section or nilpotent hypothesis is substituted.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Hom

universe u

/-- The actual surjective source map detects the original same-base lifts. -/
theorem eq_of_precomp_eq_of_surjective
    {T T' Z X : Scheme.{u}} (q : T' ⟶ T) [Surjective q]
    (p : Z ⟶ X) [FormallyUnramified p] [LocallyOfFiniteType p]
    (s t : T ⟶ Z) (hbase : s ≫ p = t ≫ p) (heq : q ≫ s = q ≫ t) : s = t := by
  let a : T ⟶ pullback p p := pullback.lift s t hbase
  let j : pullback a (pullback.diagonal p) ⟶ T := pullback.fst _ _
  have hjopen : IsOpenImmersion j := by dsimp [j]; infer_instance
  have hqa : q ≫ a = (q ≫ s) ≫ pullback.diagonal p := by
    apply pullback.hom_ext
    · simp [a, pullback.lift_fst]
    · simpa [a, pullback.lift_fst, pullback.lift_snd] using heq.symm
  let l : T' ⟶ pullback a (pullback.diagonal p) := pullback.lift q (q ≫ s) hqa
  have hlj : l ≫ j = q := by exact pullback.lift_fst _ _ _
  have hjsurj : Surjective j := by
    constructor
    intro x
    obtain ⟨z, hz⟩ := q.surjective x
    exact ⟨l z, (congrArg (fun k : T' ⟶ T => k z) hlj).trans hz⟩
  have : IsIso j := (isIso_iff_isOpenImmersion_and_surjective j).mpr ⟨hjopen, hjsurj⟩
  apply (cancel_epi j).mp
  have hj : j ≫ a = pullback.snd a (pullback.diagonal p) ≫ pullback.diagonal p :=
    pullback.condition
  calc
    j ≫ s = (j ≫ a) ≫ pullback.fst p p := by simp [a, pullback.lift_fst]
    _ = pullback.snd a (pullback.diagonal p) := by rw [hj]; simp
    _ = (j ≫ a) ≫ pullback.snd p p := by rw [hj]; simp
    _ = j ≫ t := by simp [a, pullback.lift_snd]

end AlgebraicGeometry.Scheme.Hom
