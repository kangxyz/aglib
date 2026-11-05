/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.PrincipalClosedComplement
public import Aglib.AlgebraicGeometry.EtaleCohomology.PullbackIsomorphism
public import Mathlib.RingTheory.KrullDimension.Zero

/-! # Original principal restriction detects every degree over a rank-zero domain

A nonzero principal denominator avoids the unique prime. Its literal open
is the whole base, so the original pullback restriction is an isomorphism.
This supplies the rank-zero branch for every coefficient and every degree,
without a lower-degree vanishing or closed residual hypothesis.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
universe u eY eV
attribute [local instance] hasSheafifyLarge

/-- The original principal open is the whole rank-zero domain. -/
theorem principalSupportOpen_eq_top_of_rank_zero
    (R : Type u) [CommRing R] [IsDomain R]
    (s : R) (hs : s ≠ 0) (hd : ringKrullDim R ≤ 0) :
    principalSupportOpen R s = ⊤ := by
  let : Ring.KrullDimLE 0 R := Ring.krullDimLE_iff.mpr (by simpa using hd)
  apply top_unique
  intro x _
  change s ∉ x.asIdeal
  intro hx
  have hmax : (⊥ : Ideal R).IsMaximal := Ideal.isPrime_bot.isMaximal'
  have hxbot : x.asIdeal = ⊥ := (hmax.eq_of_le x.isPrime.ne_top bot_le).symm
  rw [hxbot, Ideal.mem_bot] at hx
  exact hs hx

/-- Literal principal restriction is injective in every degree at rank zero. -/
theorem principalOpen_class_eq_zero_of_rank_zero
    (R : Type u) [CommRing R] [IsDomain R]
    (s : R) (hs : s ≠ 0) (hd : ringKrullDim R ≤ 0)
    {Y : Scheme.{u}} (b : Y ⟶ Spec (.of R))
    [HasExt.{eY} (AbelianSheaf.{u, u + 1} Y)]
    [HasExt.{eV} (AbelianSheaf.{u, u + 1}
      (pullback (principalSupportOpen R s).ι b))]
    (F : AbelianSheaf.{u, u + 1} Y) (q : ℕ) (c : Sheaf.H.{eY} F q)
    (hc : cohomologyPullback.{u, eY, eV}
      (pullback.snd (principalSupportOpen R s).ι b) F q c = 0) : c = 0 := by
  let : IsIso (principalSupportOpen R s).ι := by
    rw [principalSupportOpen_eq_top_of_rank_zero R s hs hd]
    change IsIso (Spec (.of R)).topIso.hom
    infer_instance
  apply (cohomologyPullback_bijective_of_isEquivalence
    (pullback.snd (principalSupportOpen R s).ι b) F q).injective
  exact hc.trans (map_zero _).symm

end AlgebraicGeometry.Scheme.EtaleCohomology
