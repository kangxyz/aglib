/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Nagata.FiniteType
public import Aglib.RingTheory.Nagata.CompleteLocalSurface

/-!
# Surface compatibility and actual algebraic dimension bounds

General Nagata finite-type ascent is supplied by the dimension-free lower.
The algebraic dimension consequence retains its original finite-generator
proof; no dimension preservation is asserted for transcendental algebras.
-/

@[expose] public noncomputable section

open Polynomial

universe u

namespace IsJapaneseRing

/-- The domain part of monogenic Nagata ascent. Its prime-quotient consumer
below supplies the actual injective coefficient map. -/
theorem of_adjoin_singleton_eq_top_of_dimLE_two
    {A B : Type u} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra A B] (hA : IsNagataRing.{u, 0} A) (hdim : ringKrullDim A ≤ 2)
    (hinj : Function.Injective (algebraMap A B))
    (b : B) (hb : Algebra.adjoin A ({b} : Set B) = ⊤) :
    IsJapaneseRing.{u, 0} B := by
  have := hdim
  exact of_adjoin_singleton_eq_top hA hinj b hb

end IsJapaneseRing

namespace IsNagataRing

/-- Monogenic algebras over a Nagata ring of dimension at most two are
Nagata. The target need not be a domain and has no dimension premise. -/
theorem of_adjoin_singleton_eq_top_of_dimLE_two
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (hA : IsNagataRing.{u, 0} A) (hdim : ringKrullDim A ≤ 2)
    (b : B) (hb : Algebra.adjoin A ({b} : Set B) = ⊤) :
    IsNagataRing.{u, 0} B := by
  have := hdim
  exact of_adjoin_singleton_eq_top hA b hb

end IsNagataRing

namespace IsNagataRing

/-- Polynomial Nagata stability for a coefficient ring of dimension at most
two. No target dimension assertion is used or inferred here. -/
theorem polynomial_of_dimLE_two
    {A : Type u} [CommRing A] (hA : IsNagataRing.{u, 0} A)
    (hdim : ringKrullDim A ≤ 2) : IsNagataRing.{u, 0} A[X] := by
  have := hdim
  exact hA.polynomial

end IsNagataRing

private theorem dimension_le_two_of_monogenic_algebraic
    {A B : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [CommRing B] [Algebra A B] (hdim : ringKrullDim A ≤ 2)
    (b : B) (hb : Algebra.adjoin A ({b} : Set B) = ⊤) (hba : IsAlgebraic A b) :
    ringKrullDim B ≤ 2 := by
  obtain ⟨f, hf, hfb⟩ := hba
  have hdrop := ringKrullDim_succ_le_of_surjective (aeval b).toRingHom
    (Algebra.aeval_surjective_of_adjoin_eq_top b hb)
    (mem_nonZeroDivisors_iff_ne_zero.mpr hf) hfb
  have hdim' : ringKrullDim B + 1 ≤ ringKrullDim A + 1 := by
    simpa only [Polynomial.ringKrullDim_of_isNoetherianRing] using hdrop
  exact ENat.WithBot.add_le_add_one_right_iff.mp
    (hdim'.trans (add_le_add hdim le_rfl))

namespace IsNagataRing

/-- A finite-type injective algebraic map of domains preserves the Nagata
property in dimension at most two. The dimension bound on the target is
proved by the same actual finite-generator tower. -/
theorem of_finiteType_isAlgebraic_and_dimLE_two
    {A B : Type u} [CommRing A] [CommRing B] [IsDomain B]
    [Algebra A B] [Algebra.FiniteType A B] [Algebra.IsAlgebraic A B]
    (hA : IsNagataRing.{u, 0} A) (hdim : ringKrullDim A ≤ 2)
    (hinj : Function.Injective (algebraMap A B)) :
    IsNagataRing.{u, 0} B ∧ ringKrullDim B ≤ 2 := by
  classical
  have hgen (s : Finset B) :
      IsNagataRing.{u, 0} (Algebra.adjoin A (s : Set B)) ∧
        ringKrullDim (Algebra.adjoin A (s : Set B)) ≤ 2 := by
    induction s using Finset.induction_on with
    | empty =>
      let e : Algebra.adjoin A ((∅ : Finset B) : Set B) ≃ₐ[A] A :=
        (Subalgebra.equivOfEq _ _ (show Algebra.adjoin A ((∅ : Finset B) : Set B) = ⊥ by
          simp only [Finset.coe_empty, Algebra.adjoin_empty])).trans
            (Algebra.botEquivOfInjective hinj)
      refine ⟨IsNagataRing.of_ringEquiv hA e.symm.toRingEquiv, ?_⟩
      rw [e.toRingEquiv.ringKrullDim]
      exact hdim
    | @insert x s _ ih =>
      let C := Algebra.adjoin A (s : Set B)
      let : IsNoetherianRing C := ih.1.isNoetherianRing
      let E := Algebra.adjoin C ({x} : Set B)
      let z : E := ⟨x, Algebra.self_mem_adjoin_singleton C x⟩
      have hsurj : Function.Surjective (aeval z : C[X] →ₐ[C] E) := by
        intro y
        obtain ⟨f, hf⟩ := Algebra.adjoin_eq_exists_aeval C x y
        refine ⟨f, Subtype.ext ?_⟩
        simpa only [z, Polynomial.coe_aeval_mk_apply] using hf
      have hz : Algebra.adjoin C ({z} : Set E) = ⊤ := by
        rw [Algebra.adjoin_singleton_eq_range_aeval]
        exact (AlgHom.range_eq_top _).mpr hsurj
      have hAC : Function.Injective (algebraMap A C) := by
        intro a b h
        apply hinj
        exact congrArg (fun c : C => (c : B)) h
      have hxC : IsAlgebraic C x :=
        (Algebra.IsAlgebraic.isAlgebraic (R := A) x).extendScalars hAC
      have hzC : IsAlgebraic C z :=
        (isAlgebraic_algHom_iff E.val Subtype.val_injective).mp hxC
      have hE : IsNagataRing.{u, 0} E :=
        ih.1.of_adjoin_singleton_eq_top_of_dimLE_two ih.2 z hz
      have hdimE : ringKrullDim E ≤ 2 :=
        dimension_le_two_of_monogenic_algebraic ih.2 z hz hzC
      have heq : E.restrictScalars A = Algebra.adjoin A ((insert x s : Finset B) : Set B) := by
        rw [Finset.coe_insert, ← Set.singleton_union, Set.union_comm]
        exact (Algebra.adjoin_union_eq_adjoin_adjoin A (s : Set B) ({x} : Set B)).symm
      let e : E ≃+* Algebra.adjoin A ((insert x s : Finset B) : Set B) :=
        (Subalgebra.equivOfEq _ _ heq).toRingEquiv
      refine ⟨IsNagataRing.of_ringEquiv hE e, ?_⟩
      rw [← e.ringKrullDim]
      exact hdimE
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType A B).out
  let e : Algebra.adjoin A (s : Set B) ≃ₐ[A] B :=
    (Subalgebra.equivOfEq _ _ hs).trans Subalgebra.topEquiv
  refine ⟨IsNagataRing.of_ringEquiv (hgen s).1 e.toRingEquiv, ?_⟩
  rw [← e.toRingEquiv.ringKrullDim]
  exact (hgen s).2

/-- The Nagata conclusion of finite-type generically algebraic stability.
Generic algebraicity is represented over the original coefficient domain. -/
theorem of_finiteType_isAlgebraic_of_dimLE_two
    {A B : Type u} [CommRing A] [CommRing B] [IsDomain B]
    [Algebra A B] [Algebra.FiniteType A B] [Algebra.IsAlgebraic A B]
    (hA : IsNagataRing.{u, 0} A) (hdim : ringKrullDim A ≤ 2)
    (hinj : Function.Injective (algebraMap A B)) : IsNagataRing.{u, 0} B :=
  (hA.of_finiteType_isAlgebraic_and_dimLE_two hdim hinj).1

/-- The target dimension is a consequence, not an input, of the actual
algebraic finite-generator tower used for Nagata stability. -/
theorem ringKrullDim_le_two_of_finiteType_isAlgebraic
    {A B : Type u} [CommRing A] [CommRing B] [IsDomain B]
    [Algebra A B] [Algebra.FiniteType A B] [Algebra.IsAlgebraic A B]
    (hA : IsNagataRing.{u, 0} A) (hdim : ringKrullDim A ≤ 2)
    (hinj : Function.Injective (algebraMap A B)) : ringKrullDim B ≤ 2 :=
  (hA.of_finiteType_isAlgebraic_and_dimLE_two hdim hinj).2

end IsNagataRing

namespace IsNagataRing

/-- Essentially finite-type algebraic surface domains are Nagata over the actual Nagata base. -/
theorem of_essFiniteType_isAlgebraic_of_dimLE_two
    {A B : Type u} [CommRing A] [CommRing B] [IsDomain B]
    [Algebra A B] [Algebra.EssFiniteType A B] [Algebra.IsAlgebraic A B]
    (hA : IsNagataRing.{u, 0} A) (hdim : ringKrullDim A ≤ 2)
    (hinj : Function.Injective (algebraMap A B)) : IsNagataRing.{u, 0} B := by
  let S := Algebra.EssFiniteType.subalgebra A B
  let : Algebra.IsAlgebraic A S :=
    Algebra.IsAlgebraic.of_injective S.val Subtype.val_injective
  have hinjS : Function.Injective (algebraMap A S) := by
    intro a b hab
    apply hinj
    exact congrArg (fun x : S => (x : B)) hab
  have hS : IsNagataRing.{u, 0} S :=
    hA.of_finiteType_isAlgebraic_of_dimLE_two hdim hinjS
  exact IsNagataRing.of_isLocalization (Algebra.EssFiniteType.submonoid A B) hS

/-- Completeness and dimension of the original base discharge the original chart's
Nagata premise; nothing is assumed about the chart's completion. -/
theorem of_essFiniteType_isAlgebraic_of_complete_surface
    {A B : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [CommRing B] [IsDomain B] [Algebra A B]
    [Algebra.EssFiniteType A B] [Algebra.IsAlgebraic A B]
    (hA : ringKrullDim A = 2) (hinj : Function.Injective (algebraMap A B)) :
    IsNagataRing.{u, 0} B := by
  let : Ring.KrullDimLE 2 A := Ring.krullDimLE_iff.mpr hA.le
  exact of_essFiniteType_isAlgebraic_of_dimLE_two
    (IsNagataRing.of_complete_local_dimLE_two A) hA.le hinj

end IsNagataRing
