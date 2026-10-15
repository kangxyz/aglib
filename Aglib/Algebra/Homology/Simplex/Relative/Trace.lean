/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Aglib.Algebra.Homology.Simplex.Relative.Evaluation

/-!
# Increasing-tuple normalization of the native top class

The finite full-support cohomology equivalence is precisely evaluation on
the increasing identity tuple, after the original cycles quotient. The
recursive native connecting maps introduce no extra sign or scalar factor.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u

namespace AlgebraicTopology.RelativeSimplex

variable {R : Type u} [Ring R]

/-- The increasing tuple of all vertices of the finite simplex. -/
def identityTuple (n : ℕ) : Tuple (Set.univ : Set (Fin (n + 1))) n :=
  ⟨id, fun i _hi => ⟨i, rfl⟩⟩

theorem tupleReindex_finSucc_option_identity (n : ℕ) :
    tupleReindex (finSuccEquiv' (0 : Fin (n + 2))).symm
      (optionTuple (identityTuple n)) = identityTuple (n + 1) := by
  apply Subtype.ext
  funext k
  refine Fin.cases ?_ (fun j => ?_) k
  · exact finSuccEquiv'_symm_none 0
  · simp [tupleReindex, optionTuple, identityTuple]

/-- The displayed top scalar equivalence is exactly evaluation of the original
cycle on the increasing tuple. -/
theorem fullSupportTopLinearEquiv_homologyπ (n : ℕ)
    (c : (complex R (Set.univ : Set (Fin (n + 1)))).cycles n) :
    fullSupportTopLinearEquiv R n ((complex R (Set.univ : Set (Fin (n + 1)))).homologyπ n c) =
      (complex R (Set.univ : Set (Fin (n + 1)))).iCycles n c (identityTuple n) := by
  induction n with
  | zero =>
    let : Unique (Fin 1) := { default := 0, uniq := Fin.eq_zero }
    change (complex R (Set.univ : Set (Fin 1))).iCycles 0
      (((complex R (Set.univ : Set (Fin 1))).isoHomologyπ₀).inv
        ((complex R (Set.univ : Set (Fin 1))).homologyπ 0 c)) default = _
    have hπ : ((complex R (Set.univ : Set (Fin 1))).isoHomologyπ₀).inv
        ((complex R (Set.univ : Set (Fin 1))).homologyπ 0 c) = c :=
      Iso.hom_inv_id_apply ((complex R (Set.univ : Set (Fin 1))).isoHomologyπ₀) c
    rw [hπ]
    exact congrArg ((complex R (Set.univ : Set (Fin 1))).iCycles 0 c)
      (Subsingleton.elim _ _)
  | succ n ih =>
    let e := finSuccEquiv' (0 : Fin (n + 2))
    let E := complexReindexIso (R := R) e
    let H := (homologyFunctor (ModuleCat.{u} R) (.up ℕ) (n + 1)).mapIso E
    let Δ := optionDeltaIso R (Fin (n + 1)) n
    let π := fullSupportCyclesIso (R := R) n (show Fintype.card (Fin (n + 1)) = n + 1 by simp)
    let y := Δ.inv (H.hom ((complex R (Set.univ : Set (Fin (n + 2)))).homologyπ (n + 1) c))
    let z := π.inv y
    have hπ : (complex R (Set.univ : Set (Fin (n + 1)))).homologyπ n z = y := by
      rw [← fullSupportCyclesIso_hom n
        (show Fintype.card (Fin (n + 1)) = n + 1 by simp)]
      exact Iso.inv_hom_id_apply π y
    change fullSupportTopLinearEquiv R n y = _
    rw [← hπ, ih]
    let π' := fullSupportCyclesIso (R := R) (n + 1)
      (show Fintype.card (Option (Fin (n + 1))) = n + 1 + 1 by simp)
    have hδ : Δ.hom ((complex R (Set.univ : Set (Fin (n + 1)))).homologyπ n z) =
        H.hom ((complex R (Set.univ : Set (Fin (n + 2)))).homologyπ (n + 1) c) := by
      rw [hπ]
      exact Iso.inv_hom_id_apply _ _
    have hnat : H.hom ((complex R (Set.univ : Set (Fin (n + 2)))).homologyπ (n + 1) c) =
        (complex R (Set.univ : Set (Option (Fin (n + 1))))).homologyπ (n + 1)
          (cyclesMap E.hom (n + 1) c) :=
      ConcreteCategory.congr_hom (homologyπ_naturality E.hom (n + 1)) c
    have hz : π'.inv
        (Δ.hom ((complex R (Set.univ : Set (Fin (n + 1)))).homologyπ n z)) =
        cyclesMap E.hom (n + 1) c := by
      apply (ModuleCat.mono_iff_injective π'.hom).mp inferInstance
      rw [Iso.inv_hom_id_apply]
      exact hδ.trans hnat
    have hd := optionDeltaIso_hom_evaluation (R := R)
      (show Fintype.card (Fin (n + 1)) = n + 1 by simp) z (identityTuple n)
    change (complex R (Set.univ : Set (Option (Fin (n + 1))))).iCycles (n + 1)
      (π'.inv (Δ.hom ((complex R (Set.univ : Set (Fin (n + 1)))).homologyπ n z)))
      (optionTuple (identityTuple n)) = _ at hd
    rw [hz] at hd
    calc
      (complex R (Set.univ : Set (Fin (n + 1)))).iCycles n z (identityTuple n) =
          (complex R (Set.univ : Set (Option (Fin (n + 1))))).iCycles (n + 1)
            (cyclesMap E.hom (n + 1) c) (optionTuple (identityTuple n)) := hd.symm
      _ = E.hom.f (n + 1)
          ((complex R (Set.univ : Set (Fin (n + 2)))).iCycles (n + 1) c)
          (optionTuple (identityTuple n)) :=
        congrFun (ConcreteCategory.congr_hom (cyclesMap_i E.hom (n + 1)) c) _
      _ = (complex R (Set.univ : Set (Fin (n + 2)))).iCycles (n + 1) c
          (identityTuple (n + 1)) := by
        change (complexReindexIso (R := R) e).hom.f (n + 1)
          ((complex R (Set.univ : Set (Fin (n + 2)))).iCycles (n + 1) c)
          (optionTuple (identityTuple n)) = _
        rw [complexReindexIso_hom_f_apply, tupleReindex_finSucc_option_identity]

/-- Evaluation on the increasing tuple computes the normalized equivalence on
every native top cohomology class, using its unique original cycle representative. -/
theorem fullSupportTopLinearEquiv_apply (n : ℕ)
    (x : (complex R (Set.univ : Set (Fin (n + 1)))).homology n) :
    fullSupportTopLinearEquiv R n x =
      (complex R (Set.univ : Set (Fin (n + 1)))).iCycles n
        ((fullSupportCyclesIso (R := R) n (by simp)).inv x) (identityTuple n) := by
  let π := fullSupportCyclesIso (R := R) n (show Fintype.card (Fin (n + 1)) = n + 1 by simp)
  have hπ : (complex R (Set.univ : Set (Fin (n + 1)))).homologyπ n (π.inv x) = x := by
    rw [← fullSupportCyclesIso_hom n
      (show Fintype.card (Fin (n + 1)) = n + 1 by simp)]
    exact Iso.inv_hom_id_apply π x
  have h := fullSupportTopLinearEquiv_homologyπ n (π.inv x)
  rw [hπ] at h
  exact h

end AlgebraicTopology.RelativeSimplex
