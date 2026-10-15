/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Aglib.Algebra.Homology.Simplex.Relative.Reindex
public import Aglib.Algebra.Homology.Simplex.Relative.Singleton
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.Fintype.Card

/-!
# Native full-support tuple cohomology on a finite simplex

For the `n + 1` vertices `Fin (n + 1)`, the actual alternating complex on
surjective tuples has native homology equal to the scalar module in degree
`n`, and zero homology in every other degree. The top comparison recursively
uses the original vertex-removal connecting map and the explicit singleton
normalization. No ordered-Cech comparison is supplied as a premise.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u v

namespace AlgebraicTopology.RelativeSimplex

variable {R : Type u} [Ring R]

/-- Too few tuple positions give the actual zero term of the full-support complex. -/
theorem isZero_X_of_card_lt {ι : Type v} [Fintype ι] (q : ℕ)
    (hq : q + 1 < Fintype.card ι) : IsZero ((complex R (Set.univ : Set ι)).X q) := by
  have : IsEmpty (Tuple (Set.univ : Set ι) q) := ⟨fun a => by
    have hsurj := (univ_supported_iff_surjective a.val).mp a.property
    have hcard := Fintype.card_le_of_surjective a.val hsurj
    simp only [Fintype.card_fin] at hcard
    omega⟩
  rw [complex_X]
  exact ModuleCat.isZero_of_subsingleton _

/-- The top cohomology of the native full-support tuple complex, normalized by
the actual singleton evaluation and successive native connecting maps. -/
def fullSupportTopLinearEquiv (R : Type u) [Ring R] :
    ∀ n : ℕ, (complex R (Set.univ : Set (Fin (n + 1)))).homology n ≃ₗ[R] R
  | 0 =>
    letI : Unique (Fin 1) := { default := 0, uniq := Fin.eq_zero }
    homologyZeroLinearEquiv_of_unique
  | n + 1 =>
    (((homologyFunctor (ModuleCat.{u} R) (.up ℕ) (n + 1)).mapIso
      (complexReindexIso (finSuccEquiv' (0 : Fin (n + 2))))).toLinearEquiv.trans
        (optionDeltaIso R (Fin (n + 1)) n).symm.toLinearEquiv).trans
      (fullSupportTopLinearEquiv R n)

/-- The actual native complex is exact in every degree other than the top degree. -/
theorem fullSupport_exactAt_of_ne (n q : ℕ) (hq : q ≠ n) :
    (complex R (Set.univ : Set (Fin (n + 1)))).ExactAt q := by
  induction n generalizing q with
  | zero =>
    cases q with
    | zero => exact (hq rfl).elim
    | succ q =>
      let : Unique (Fin 1) := { default := 0, uniq := Fin.eq_zero }
      exact exactAt_succ_of_unique q
  | succ n ih =>
    cases q with
    | zero =>
      exact HomologicalComplex.ExactAt.of_isZero (isZero_X_of_card_lt 0 (by simp))
    | succ q =>
      have hq' : q ≠ n := by omega
      have hz := (ih q hq').isZero_homology
      have hz' : IsZero
          ((complex R (Set.univ : Set (Option (Fin (n + 1))))).homology (q + 1)) :=
        hz.of_iso (optionDeltaIso R (Fin (n + 1)) q).symm
      exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
        (hz'.of_iso ((homologyFunctor (ModuleCat.{u} R) (.up ℕ) (q + 1)).mapIso
          (complexReindexIso (finSuccEquiv' (0 : Fin (n + 2))))))

/-- Vanishing of the unchanged native homology objects away from the top degree. -/
theorem fullSupport_isZero_homology_of_ne (n q : ℕ) (hq : q ≠ n) :
    IsZero ((complex R (Set.univ : Set (Fin (n + 1)))).homology q) :=
  (fullSupport_exactAt_of_ne (R := R) n q hq).isZero_homology

end AlgebraicTopology.RelativeSimplex
