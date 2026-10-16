/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.CochainComplex.Cycles
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Splitting the exact tail of a projective complex

For a bounded-above cochain complex of projective objects, exactness strictly
above a degree makes the cycles in that degree projective. The proof descends
through the actual short exact cycle sequences. For finite module terms, the
same splitting makes these cycles and their homology finite, without a
Noetherian assumption. If the incoming differential is zero, the actual
homology is projective as well.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C]

/-- If the next cycles are projective, exactness there splits the inclusion of
cycles into the current term. Both arrows are the native cycle-sequence arrows. -/
def cyclesRetractOfExactAt (K : CochainComplex C ℤ) (n : ℤ)
    (h : K.ExactAt (n + 1)) [Projective (K.cycles (n + 1))] :
    Retract (K.cycles n) (K.X n) where
  i := K.iCycles n
  r := (K.shortExact_cycles n h).splittingOfProjective.r
  retract := (K.shortExact_cycles n h).splittingOfProjective.f_r

/-- A bounded-above projective complex has projective cycles in every degree
above which its homology vanishes. -/
theorem projective_cycles_of_exact_above (K : CochainComplex C ℤ) (b n : ℤ)
    [K.IsStrictlyLE b] [∀ i, Projective (K.X i)]
    (h : ∀ i, n < i → K.ExactAt i) : Projective (K.cycles n) := by
  let b' := max b n
  have : K.IsStrictlyLE b' := K.isStrictlyLE_of_le b b' (le_max_left _ _)
  have hb : Projective (K.cycles (b' + 1)) :=
    (IsZero.of_mono (K.iCycles (b' + 1))
      (K.isZero_of_isStrictlyLE b' (b' + 1) (by lia))).projective
  have hd : ∀ i, i ≤ b' + 1 → n ≤ i → Projective (K.cycles i) :=
    Int.leInductionDown (motive := fun i _ => n ≤ i → Projective (K.cycles i))
      (fun _ => hb) (fun i hi ih hni => by
        have : Projective (K.cycles ((i - 1) + 1)) := by
          simpa only [sub_add_cancel] using ih (by lia)
        exact (K.cyclesRetractOfExactAt (i - 1) (h _ (by lia))).projective)
  exact hd n (by dsimp [b']; lia) le_rfl

/-- When the incoming differential is zero, projective cycles identify with
the actual homology, so an exact projective tail makes that homology projective. -/
theorem projective_homology_of_exact_above_of_d_eq_zero (K : CochainComplex C ℤ) (b n : ℤ)
    [K.IsStrictlyLE b] [∀ i, Projective (K.X i)]
    (h : ∀ i, n < i → K.ExactAt i) (hd : K.d (n - 1) n = 0) :
    Projective (K.homology n) := by
  have := K.projective_cycles_of_exact_above b n h
  exact Projective.of_iso (K.isoHomologyπ (n - 1) n (by simp) hd) inferInstance

/-- A projective complex concentrated termwise in degrees at least `n`, bounded
above, and exact above `n` has projective homology in degree `n`. -/
theorem projective_homology_of_isStrictlyGE_of_exact_above
    (K : CochainComplex C ℤ) (b n : ℤ) [K.IsStrictlyLE b] [K.IsStrictlyGE n]
    [∀ i, Projective (K.X i)] (h : ∀ i, n < i → K.ExactAt i) :
    Projective (K.homology n) :=
  K.projective_homology_of_exact_above_of_d_eq_zero b n h
    ((K.isZero_of_isStrictlyGE n (n - 1) (by lia)).eq_of_src _ _)

end CochainComplex

namespace CochainComplex

universe u v

variable {R : Type u} [Ring R]

/-- Cycles above which a projective module complex is exact are finite whenever
the current term is finite; neither lower boundedness nor Noetherianity is used. -/
theorem finite_cycles_of_exact_above (K : CochainComplex (ModuleCat.{v} R) ℤ) (b n : ℤ)
    [K.IsStrictlyLE b] [∀ i, Module.Projective R (K.X i)] [Module.Finite R (K.X n)]
    (h : ∀ i, n < i → K.ExactAt i) : Module.Finite R (K.cycles n) := by
  have (i : ℤ) : Projective (K.X i) := inferInstance
  have : Projective (K.cycles (n + 1)) :=
    K.projective_cycles_of_exact_above b (n + 1) (fun i hi => h i (by lia))
  let r := K.cyclesRetractOfExactAt n (h (n + 1) (by lia))
  apply Module.Finite.of_surjective r.r.hom
  intro x
  refine ⟨r.i x, ?_⟩
  change (r.i ≫ r.r) x = x
  rw [r.retract]
  rfl

/-- Homology of an exact projective tail is finite when its degree term is
finite, with no Noetherian hypothesis on the coefficient ring. -/
theorem finite_homology_of_exact_above (K : CochainComplex (ModuleCat.{v} R) ℤ) (b n : ℤ)
    [K.IsStrictlyLE b] [∀ i, Module.Projective R (K.X i)] [Module.Finite R (K.X n)]
    (h : ∀ i, n < i → K.ExactAt i) : Module.Finite R (K.homology n) := by
  have := K.finite_cycles_of_exact_above b n h
  exact Module.Finite.of_surjective (K.homologyπ n).hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)

end CochainComplex
