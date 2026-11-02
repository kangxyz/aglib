/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Artinian.SplitQuotientRestriction
public import Aglib.RingTheory.Localization.FiniteIntegralCaptureAway

/-! # Spreading a split quotient of a finite free algebra

For an actual finite basis over a domain, capture the original character
values and coordinates of chosen quotient preimages in one localized finite
subalgebra. The actual quotient restriction then supplies surjectivity and
kernel-power nilpotence. Flatness here follows from the supplied actual basis;
it is not asserted for a general unlocalized finite algebra.
-/

@[expose] public noncomputable section

open scoped TensorProduct BigOperators

namespace Algebra.FiniteAlgebra

universe u v w x y z

variable (R : Type u) [CommRing R] [IsDomain R]
  (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
  {L : Type w} [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [Module.Finite K L]
  {A : Type x} [CommRing A] [Algebra R A]
  {I : Type y} [Finite I] {J : Type z} [Finite J]

include K in
/-- A split nilpotent quotient of a finite free algebra descends to the actual
localization of a module-finite base subalgebra, with its original coordinate
index and its literal base-change equation. -/
theorem exists_finiteIntegral_away_splitQuotient (b : Module.Basis I R A)
    (q : L ⊗[R] A →ₐ[L] (J → L)) (hq : Function.Surjective q)
    (n : ℕ) (hn : (RingHom.ker q.toRingHom) ^ n = ⊥) :
    ∃ r : R, r ≠ 0 ∧ ∃ hr : algebraMap R L r ≠ 0,
      ∃ B : Subalgebra R L, Module.Finite R B ∧
        ∃ qC : (Localization.Away (algebraMap R B r)) ⊗[R] A →ₐ[Localization.Away
          (algebraMap R B r)] (J → Localization.Away (algebraMap R B r)),
          Function.Surjective qC ∧ (RingHom.ker qC.toRingHom) ^ n = ⊥ ∧
          ∀ z j, IsFractionRing.finiteSubalgebraAwayMap B r hr (qC z j) =
            q (Algebra.TensorProduct.map (IsFractionRing.finiteSubalgebraAwayMap B r hr)
              (AlgHom.id R A) z) j := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let : Fintype J := Fintype.ofFinite J
  let χ : J → (A →ₐ[R] L) := fun j =>
    (((Pi.evalAlgHom L (fun _ : J => L) j).comp q).restrictScalars R).comp
      Algebra.TensorProduct.includeRight
  let p : J → L ⊗[R] A := fun j => (hq (Pi.single j 1)).choose
  have hp (j : J) : q (p j) = Pi.single j 1 := (hq (Pi.single j 1)).choose_spec
  let c : J → I → L := fun j i => (b.baseChange L).repr (p j) i
  let s : Finset L :=
    Finset.univ.image (fun ij : I × J => χ ij.2 (b ij.1)) ∪
      Finset.univ.image (fun ji : J × I => c ji.1 ji.2)
  obtain ⟨r, hr, hrL, B, hB, hi, hs⟩ :=
    IsFractionRing.exists_finiteSubalgebra_away_capture R K s
  let C := Localization.Away (algebraMap R B r)
  let i : C →ₐ[R] L := IsFractionRing.finiteSubalgebraAwayMap B r hrL
  have hχ (j : J) (a : I) : χ j (b a) ∈ i.range :=
    hs _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(a, j), Finset.mem_univ _, rfl⟩))
  have hc (j : J) (a : I) : c j a ∈ i.range :=
    hs _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(j, a), Finset.mem_univ _, rfl⟩))
  have hχall (a : A) (j : J) : q (1 ⊗ₜ[R] a) j ∈ i.range := by
    change χ j a ∈ i.range
    rw [← b.sum_repr a, map_sum]
    exact i.range.sum_mem fun a' _ => by
      rw [map_smul]
      exact i.range.smul_mem (hχ j a') (b.repr a a')
  let cc : J → I → C := fun j a => (hc j a).choose
  have hcc (j : J) (a : I) : i (cc j a) = c j a := (hc j a).choose_spec
  let pC : J → C ⊗[R] A := fun j => ∑ a, cc j a ⊗ₜ[R] b a
  have hpC (j : J) : Algebra.TensorProduct.map i (AlgHom.id R A) (pC j) = p j := by
    simp only [pC, map_sum, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hcc]
    simpa only [c, Module.Basis.baseChange_apply, TensorProduct.smul_tmul',
      smul_eq_mul, mul_one] using (b.baseChange L).sum_repr (p j)
  let qC := splitQuotientRestriction i hi q hχall
  have hsurj : Function.Surjective qC :=
    splitQuotientRestriction_surjective i hi q hχall pC (fun j => (congrArg q (hpC j)).trans (hp j))
  have : Module.Free R A := Module.Free.of_basis b
  have hnil : (RingHom.ker qC.toRingHom) ^ n = ⊥ :=
    splitQuotientRestriction_ker_pow i hi q hχall n hn
  exact ⟨r, hr, hrL, B, hB, qC, hsurj, hnil,
    fun z j => splitQuotientRestriction_commutes i hi q hχall z j⟩

end Algebra.FiniteAlgebra
