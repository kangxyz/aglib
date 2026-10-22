/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.HenselizationCompletionCoherence
public import Aglib.RingTheory.Henselian.RectangularCorrection
public import Aglib.RingTheory.AdicCompletion.Congruence

/-!
# Unit-minor approximation in the actual henselization

Finite jets of a formal root in the completion of a local Noetherian ring lift
through the actual henselization quotient equivalences. A unit selected minor
then permits genuine Henselian correction, fixing every unselected coordinate
of the chosen source jet. This supplies the nonsingular zero-variable consumer
for DVR approximation; it does not assume or prove the singular reduction.
-/

@[expose] public noncomputable section

open IsLocalRing MvPolynomial

namespace Henselization

variable (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- The canonical formal map has the original finite-quotient coordinates. -/
theorem quotientMap_eval_toAdicCompletion (n : ℕ) (x : Henselization R) :
    quotientMaximalIdealPowMap R n
      (AdicCompletion.evalₐ (maximalIdeal R) n (toAdicCompletion R x)) =
        Ideal.Quotient.mk (maximalIdeal (Henselization R) ^ n) x := by
  rw [← eval_completionMap, completionMap_toAdicCompletion]
  exact (AdicCompletion.evalₐ (maximalIdeal (Henselization R)) n).commutes x

/-- Correct any chosen source jet of a formal root with unit selected minor.
The correction fixes the source coordinates outside the selected columns. -/
theorem exists_zero_of_selected_unit_minor_of_jet
    {σ ν : Type*} [Fintype σ] [DecidableEq σ] (selected : σ ↪ ν)
    (F : σ → MvPolynomial ν (Henselization R))
    (y : ν → AdicCompletion (maximalIdeal R) R)
    (hF : ∀ i, eval₂ (toAdicCompletion R).toRingHom y (F i) = 0)
    (hdet : IsUnit (eval₂ (toAdicCompletion R).toRingHom y
      (Matrix.det (Matrix.of fun i j => pderiv (selected j) (F i)))))
    (c : ℕ) (y₀ : ν → Henselization R)
    (hjet : ∀ j,
      Ideal.Quotient.mk (maximalIdeal (Henselization R) ^ max c 1) (y₀ j) =
        quotientMaximalIdealPowMap R (max c 1)
          (AdicCompletion.evalₐ (maximalIdeal R) (max c 1) (y j))) :
    ∃ x : ν → Henselization R,
      (∀ i, eval x (F i) = 0) ∧
      (∀ j, j ∉ Set.range selected → x j = y₀ j) ∧
      ∀ j, toAdicCompletion R (x j) - y j ∈
        maximalIdeal (AdicCompletion (maximalIdeal R) R) ^ c := by
  let N := max c 1
  have hN : 0 < N := lt_of_lt_of_le Nat.zero_lt_one (le_max_right c 1)
  let a := maximalIdeal (Henselization R) ^ N
  let q := Ideal.Quotient.mk a
  let e := quotientMaximalIdealPowEquivAll R N
  let t := e.toRingHom.comp (AdicCompletion.evalₐ (maximalIdeal R) N).toRingHom
  let φ := (toAdicCompletion R).toRingHom
  let : HenselianLocalRing (Henselization R ⧸ a) :=
    HenselianLocalRing.quotient_maximalIdeal_pow (Henselization R) N hN.ne'
  let : IsLocalHom q := IsLocalHom.of_surjective q Ideal.Quotient.mk_surjective
  have hcoeff : t.comp φ = q := by
    ext z
    exact quotientMap_eval_toAdicCompletion R N z
  have hpoint : q ∘ y₀ = fun j => t (y j) := funext hjet
  have heval (p : MvPolynomial ν (Henselization R)) :
      q (eval y₀ p) = t (eval₂ φ y p) := by
    rw [eval₂_comp, hom_eval₂, hcoeff, hpoint]
  have herror (i : σ) : eval y₀ (F i) ∈ a := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q (eval y₀ (F i)) = 0
    rw [heval, hF i, map_zero]
  let δ := Matrix.det (Matrix.of fun i j => eval y₀ (pderiv (selected j) (F i)))
  have hδ : IsUnit δ := by
    apply (isUnit_map_iff q δ).mp
    have h := hdet.map t
    have hd : eval y₀ (Matrix.det
        (Matrix.of fun i j => pderiv (selected j) (F i))) = δ := by
      rw [RingHom.map_det]
      rfl
    rw [← heval, hd] at h
    exact h
  have ha : a ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal (Henselization R)).ne_top
      (Ideal.pow_le_self hN.ne')
  have herror' (i : σ) : eval y₀ (F i) ∈ Ideal.span {δ ^ 2} * a := by
    rw [Ideal.span_singleton_eq_top.mpr (hδ.pow 2), Ideal.top_mul]
    exact herror i
  obtain ⟨x, hx, hfree, _, hclose⟩ :=
    HenselianLocalRing.exists_eval_eq_zero_of_mem_embedding_det_sq_mul
      selected F y₀ a ha herror'
  refine ⟨x, hx, hfree, ?_⟩
  intro j
  have hxjet : q (x j) = t (y j) := by
    have hq : q (x j) = q (y₀ j) :=
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (hclose j)
    exact hq.trans (hjet j)
  have heq : AdicCompletion.evalₐ (maximalIdeal R) N (toAdicCompletion R (x j)) =
      AdicCompletion.evalₐ (maximalIdeal R) N (y j) := by
    apply e.injective
    exact (quotientMap_eval_toAdicCompletion R N (x j)).trans hxjet
  have hmem := (AdicCompletion.evalₐ_eq_iff_sub_mem (maximalIdeal R)
    (maximalIdeal R).fg_of_isNoetherianRing N _ _).mp heq
  rw [Ideal.map_pow, ← AdicCompletion.maximalIdeal_eq_map] at hmem
  exact Ideal.pow_le_pow_right (le_max_left c 1) hmem

/-- A formal selected system with residue-unit minor has arbitrary precision
solutions in the actual henselization of the coefficient ring. No DVR or
characteristic assumption is needed for this correction consumer. -/
theorem exists_zero_of_selected_system_of_residue_ne_zero
    {σ ν : Type*} [Fintype σ] [DecidableEq σ] (selected : σ ↪ ν)
    (F : σ → MvPolynomial ν (Henselization R))
    (y : ν → AdicCompletion (maximalIdeal R) R)
    (hF : ∀ i, eval₂ (toAdicCompletion R).toRingHom y (F i) = 0)
    (hdet : IsLocalRing.residue (AdicCompletion (maximalIdeal R) R)
      (eval₂ (toAdicCompletion R).toRingHom y
        (Matrix.det (Matrix.of fun i j => pderiv (selected j) (F i)))) ≠ 0)
    (c : ℕ) :
    ∃ x : ν → Henselization R,
      (∀ i, eval x (F i) = 0) ∧
      ∀ j, toAdicCompletion R (x j) - y j ∈
        maximalIdeal (AdicCompletion (maximalIdeal R) R) ^ c := by
  choose y₀ hy₀ using fun j => Ideal.Quotient.mk_surjective
    (quotientMaximalIdealPowMap R (max c 1)
      (AdicCompletion.evalₐ (maximalIdeal R) (max c 1) (y j)))
  obtain ⟨x, hx, _, hclose⟩ := exists_zero_of_selected_unit_minor_of_jet R
    selected F y hF ((residue_ne_zero_iff_isUnit _).mp hdet) c y₀ hy₀
  exact ⟨x, hx, hclose⟩

end Henselization
