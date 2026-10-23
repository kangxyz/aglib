/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.FiniteLength.Torsion
public import Aglib.RingTheory.Multiplicity.PrincipalEuler.Additivity
public import Aglib.RingTheory.QuotSMulTop.Pi
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.QuotSMulTop

/-!
# Scalar-quotient length bounds in dimension at most one

The scalar quotient of a finite-rank torsion-free module over a Noetherian
domain of dimension at most one has length bounded by its rank times the
scalar-quotient length of the ring. Finite modules satisfy equality. For an
arbitrary ambient module, finitely many elements detect each finite strict
chain, so the finite calculation gives the uniform bound.
-/

@[expose] public section

namespace Module

variable {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- A uniform length bound on images of finitely generated submodules bounds
the image of the entire module, here presented by a surjective linear map. -/
theorem length_le_of_fg_image_bound (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (b : ℕ∞) (h : ∀ P : Submodule R M, P.FG → Module.length R (P.map f) ≤ b) :
    Module.length R N ≤ b := by
  classical
  apply WithBot.coe_le_coe.mp
  rw [Module.coe_length, Order.krullDim]
  apply iSup_le
  intro s
  have hstep (i : Fin s.length) : s i.castSucc < s i.succ := s.step i
  choose x hx hnx using fun i ↦ (SetLike.lt_iff_le_and_exists.mp (hstep i)).2
  choose y hy using fun i ↦ hf (x i)
  let P : Submodule R M := Submodule.span R (Set.range y)
  have hP : P.FG := Submodule.fg_span (Set.finite_range y)
  have hxP (i : Fin s.length) : x i ∈ P.map f :=
    ⟨y i, Submodule.subset_span ⟨i, rfl⟩, hy i⟩
  let t : LTSeries (Submodule R (P.map f)) :=
    { length := s.length
      toFun := fun i ↦ (s i).comap (P.map f).subtype
      step := fun i ↦ SetLike.lt_iff_le_and_exists.mpr
        ⟨Submodule.comap_mono (hstep i).le, ⟨x i, hxP i⟩, hx i, hnx i⟩ }
  have ht : (s.length : WithBot ℕ∞) ≤ (Module.length R (P.map f) : WithBot ℕ∞) := by
    rw [Module.coe_length]
    exact Order.LTSeries.length_le_krullDim t
  exact ht.trans (WithBot.coe_le_coe.mpr (h P hP))

end Module

namespace QuotSMulTop

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

open scoped Pointwise

/-- A scalar-quotient length bound passes from all finitely generated
submodules to the whole module. The map from each small scalar quotient is
used only through its image; it need not be injective. -/
theorem length_le_of_fg_submodule_bound (a : R) (b : ℕ∞)
    (h : ∀ P : Submodule R M, P.FG → Module.length R (QuotSMulTop a P) ≤ b) :
    Module.length R (QuotSMulTop a M) ≤ b := by
  apply Module.length_le_of_fg_image_bound (a • (⊤ : Submodule R M)).mkQ
    (Submodule.mkQ_surjective _) b
  intro P hP
  have hr : LinearMap.range (QuotSMulTop.map a P.subtype) =
      P.map (a • (⊤ : Submodule R M)).mkQ := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨p, rfl⟩ := Submodule.mkQ_surjective (a • (⊤ : Submodule R P)) y
      exact ⟨p, p.property, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨Submodule.Quotient.mk (⟨p, hp⟩ : P), rfl⟩
  rw [← hr]
  exact (Module.length_le_of_surjective (QuotSMulTop.map a P.subtype).rangeRestrict
    (LinearMap.surjective_rangeRestrict _)).trans (h P hP)

/-- A uniform natural-number bound on the small scalar quotients proves
finite length of the scalar quotient of the entire module. -/
theorem isFiniteLength_of_fg_submodule_bound (a : R) (b : ℕ)
    (h : ∀ P : Submodule R M, P.FG → Module.length R (QuotSMulTop a P) ≤ b) :
    IsFiniteLength R (QuotSMulTop a M) :=
  Module.length_ne_top_iff.mp <| ne_of_lt <|
    (length_le_of_fg_submodule_bound a b h).trans_lt (by simp)

end QuotSMulTop


namespace QuotSMulTop

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

open scoped Pointwise nonZeroDivisors

private theorem range_lsmul_eq (a : R) :
    LinearMap.range (LinearMap.lsmul R M a) = a • (⊤ : Submodule R M) := by
  ext x
  rw [Submodule.mem_smul_pointwise_iff_exists]
  simp only [LinearMap.mem_range, LinearMap.lsmul_apply, Submodule.mem_top, true_and]

/-- The scalar quotient of a finite free module has the expected length. -/
theorem length_of_finite_free [Nontrivial R] [Module.Free R M] [Module.Finite R M] (a : R) :
    Module.length R (QuotSMulTop a M) =
      Module.finrank R M * Module.length R (QuotSMulTop a R) := by
  classical
  let b := Module.Free.chooseBasis R M
  rw [(QuotSMulTop.congr a b.equivFun).length_eq,
    ((QuotSMulTop.piEquiv a R (Module.Free.ChooseBasisIndex R M)).restrictScalars R).length_eq,
    Module.length_pi_of_fintype]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Module.finrank_eq_card_basis b]

/-- A nonzero scalar quotient of a finite module over a Noetherian domain
of dimension at most one has finite length. -/
theorem isFiniteLength_of_finite [IsDomain R] [IsNoetherianRing R]
    [Ring.KrullDimLE 1 R] [Module.Finite R M] (a : R) (ha : a ≠ 0) :
    IsFiniteLength R (QuotSMulTop a M) := by
  apply Module.finiteLength_of_isTorsion
  intro x
  refine ⟨⟨a, mem_nonZeroDivisors_iff_ne_zero.mpr ha⟩, ?_⟩
  change a • x = 0
  exact Module.isTorsionBy_quotient_element_smul M a (x := x)

/-- A finite torsion-free module over a Noetherian domain of dimension at
most one has the same scalar-quotient length as a free module of its rank. -/
theorem length_of_finite_torsionFree [IsDomain R] [IsNoetherianRing R]
    [Ring.KrullDimLE 1 R] [Module.Finite R M] [Module.IsTorsionFree R M]
    (a : R) (ha : a ≠ 0) :
    Module.length R (QuotSMulTop a M) =
      Module.finrank R M * Module.length R (QuotSMulTop a R) := by
  classical
  obtain ⟨s, hs, hli⟩ := exists_finset_linearIndependent_of_le_finrank
    (R := R) (M := M) (n := Module.finrank R M) le_rfl
  let F : Submodule R M := Submodule.span R (Set.range ((↑) : s → M))
  let b : Module.Basis s R F := Module.Basis.span hli
  let : Module.Free R F := Module.Free.of_basis b
  have hF : Module.finrank R F = Module.finrank R M := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_coe, hs]
  have hTtors : Module.IsTorsion R (M ⧸ F) := by
    apply Module.finrank_eq_zero_iff_isTorsion.mp
    have h := F.finrank_quotient_add_finrank
    rw [hF] at h
    omega
  have hT := Module.length_ne_top_iff.mpr (Module.finiteLength_of_isTorsion hTtors)
  have hM := Module.length_ne_top_iff.mpr (isFiniteLength_of_finite (M := M) a ha)
  have hFq := Module.length_ne_top_iff.mpr (isFiniteLength_of_finite (M := F) a ha)
  have hMr : IsSMulRegular M a := (isRegular_iff_ne_zero.mpr ha).isSMulRegular
  have hFr : IsSMulRegular F a := (isRegular_iff_ne_zero.mpr ha).isSMulRegular
  have hpM : Module.FinitePrincipal M a := by
    apply Module.finitePrincipal_of_regular M a hMr
    change Module.length R (M ⧸ LinearMap.range (LinearMap.lsmul R M a)) ≠ ⊤
    rw [range_lsmul_eq (M := M) a]
    exact hM
  have hpF : Module.FinitePrincipal F a := by
    apply Module.finitePrincipal_of_regular F a hFr
    change Module.length R (F ⧸ LinearMap.range (LinearMap.lsmul R F a)) ≠ ⊤
    rw [range_lsmul_eq (M := F) a]
    exact hFq
  have hpT : Module.FinitePrincipal (M ⧸ F) a := by
    constructor
    · exact ne_top_of_le_ne_top hT
        (Module.length_le_of_injective (Module.ScalarKernel (M ⧸ F) a).subtype
          (Submodule.subtype_injective _))
    · exact ne_top_of_le_ne_top hT
        (Module.length_le_of_surjective (LinearMap.range (LinearMap.lsmul R (M ⧸ F) a)).mkQ
          (Submodule.mkQ_surjective _))
  have hEuler := Module.principalEuler_add_of_exact F.subtype F.mkQ
    (Submodule.subtype_injective _) (Submodule.mkQ_surjective _)
    (LinearMap.exact_subtype_mkQ _) a hpF hpM hpT
  rw [Module.principalEuler_zero_of_finite_length a hT, add_zero,
    Module.principalEuler_of_regular a hMr, Module.principalEuler_of_regular a hFr] at hEuler
  rw [range_lsmul_eq (M := M) a, range_lsmul_eq (M := F) a] at hEuler
  have hNat : (Module.length R (QuotSMulTop a M)).toNat =
      (Module.length R (QuotSMulTop a F)).toNat := by exact_mod_cast hEuler
  have hlen : Module.length R (QuotSMulTop a M) =
      Module.length R (QuotSMulTop a F) := by
    rw [← ENat.natCast_toNat hM, ← ENat.natCast_toNat hFq, hNat]
  rw [hlen, length_of_finite_free, hF]

/-- The scalar quotient of an arbitrary finite-rank torsion-free module
over a Noetherian domain of dimension at most one has uniformly bounded
length. The ambient module is not required to be finitely generated. -/
theorem length_le_of_rank_lt_aleph0 [IsDomain R] [IsNoetherianRing R]
    [Ring.KrullDimLE 1 R] [Module.IsTorsionFree R M]
    (hrank : Module.rank R M < Cardinal.aleph0) (a : R) (ha : a ≠ 0) :
    Module.length R (QuotSMulTop a M) ≤
      Module.finrank R M * Module.length R (QuotSMulTop a R) := by
  apply length_le_of_fg_submodule_bound
  intro P hP
  let : Module.Finite R P := Module.Finite.of_fg hP
  rw [length_of_finite_torsionFree a ha]
  have hdim : Module.finrank R P ≤ Module.finrank R M :=
    Cardinal.toNat_le_toNat P.rank_le hrank
  exact mul_le_mul_left (Nat.cast_le.mpr hdim) _

/-- Every nonzero scalar quotient of an arbitrary finite-rank torsion-free
module over a Noetherian domain of dimension at most one has finite length. -/
theorem isFiniteLength_of_rank_lt_aleph0 [IsDomain R] [IsNoetherianRing R]
    [Ring.KrullDimLE 1 R] [Module.IsTorsionFree R M]
    (hrank : Module.rank R M < Cardinal.aleph0) (a : R) (ha : a ≠ 0) :
    IsFiniteLength R (QuotSMulTop a M) := by
  apply Module.length_ne_top_iff.mp
  apply ne_top_of_le_ne_top _ (length_le_of_rank_lt_aleph0 hrank a ha)
  have hR := Module.length_ne_top_iff.mpr (isFiniteLength_of_finite (M := R) a ha)
  rw [← ENat.natCast_toNat hR, ← Nat.cast_mul]
  exact ENat.natCast_ne_top _

end QuotSMulTop
