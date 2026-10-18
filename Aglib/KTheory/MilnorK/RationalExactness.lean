/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.StageEquivalence
public import Aglib.KTheory.MilnorK.ConstantRestriction
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Exactness of the actual finite polynomial residues

The finite dependent residue map on the original rational-function Milnor K_{n+1}
is surjective, and its kernel is precisely the image of constant Milnor K_{n+1}.
Both statements follow by finite degree descent from the proved equivalences
of actual polynomial stages. Combining this with the separately proved
constant specialization gives the actual short exact sequence in every
positive Milnor degree, over arbitrary fields. No exactness, transfer, norm,
reciprocity, or injectivity hypothesis is supplied.
-/

@[expose] public noncomputable section

namespace MilnorK.DegreeFiltration

open Polynomial PolynomialResidue

variable {k : Type*} [Field k]

/-- All residues at or above a polynomial-span bound vanish on that span. -/
theorem residueAt_eq_zero_of_mem_lower (n d : ℕ) (x : K (RatFunc k) (n + 1))
    (hx : x ∈ lower k (n + 1) d) (p : MonicIrreducible k) (hp : d ≤ p.val.natDegree) :
    residueAt p.val n x = 0 :=
  lower_le_ker_residueAt p.val p.property.1 n (lower_mono hp hx)

/-- A class with zero finite residues descends through every positive degree stage. -/
theorem mem_lower_one_of_totalResidue_eq_zero (n : ℕ) (x : K (RatFunc k) (n + 1))
    (hres : totalResidue n x = 0) (d : ℕ) (hx : x ∈ lower k (n + 1) d) :
    x ∈ lower k (n + 1) 1 := by
  induction d with
  | zero => exact lower_mono (Nat.zero_le 1) hx
  | succ d ih =>
    by_cases hd : d = 0
    · simpa only [hd, zero_add] using hx
    · apply ih
      apply (degreeResidues_eq_zero_iff_mem_lower n d (Nat.pos_of_ne_zero hd) x hx).mp
      apply DFinsupp.ext
      intro p
      exact (totalResidue_eq_zero_iff n x).mp hres p.val

/-- The actual kernel is already the degree-one polynomial span. -/
theorem totalResidue_eq_zero_iff_mem_lower_one (n : ℕ) (x : K (RatFunc k) (n + 1)) :
    totalResidue n x = 0 ↔ x ∈ lower k (n + 1) 1 := by
  constructor
  · intro hx
    obtain ⟨d, hd⟩ := exists_mem_lower x
    exact mem_lower_one_of_totalResidue_eq_zero n x hx d hd
  · intro hx
    apply (totalResidue_eq_zero_iff n x).mpr
    intro p
    exact residueAt_eq_zero_of_mem_lower n 1 x hx p p.property.2.natDegree_pos

/-- Every finite residue vector supported strictly below `d` has a representative
in the actual polynomial span with that same bound. The positive-degree step
lifts its top slice through the proved stage equivalence and corrects the lower
degree error by induction. -/
theorem exists_mem_lower_totalResidue_eq (n d : ℕ)
    (y : Π₀ p : MonicIrreducible k, K (AdjoinRoot p.val) n)
    (hy : ∀ p : MonicIrreducible k, d ≤ p.val.natDegree → y p = 0) :
    ∃ x ∈ lower k (n + 1) d, totalResidue n x = y := by
  classical
  induction d generalizing y with
  | zero =>
    refine ⟨0, (lower k (n + 1) 0).zero_mem, ?_⟩
    apply DFinsupp.ext
    intro p
    simpa only [map_zero, DFinsupp.zero_apply] using (hy p (Nat.zero_le _)).symm
  | succ d ih =>
    by_cases hd : d = 0
    · refine ⟨0, (lower k (n + 1) (d + 1)).zero_mem, ?_⟩
      apply DFinsupp.ext
      intro p
      have hp : d + 1 ≤ p.val.natDegree := by
        have hpos := p.property.2.natDegree_pos
        omega
      simpa only [map_zero, DFinsupp.zero_apply] using (hy p hp).symm
    · let r : DegreeResidues k n d :=
        DFinsupp.subtypeDomain (fun p : MonicIrreducible k => p.val.natDegree = d) y
      obtain ⟨s, hs⟩ := (actualStageEquiv (F := k) n d (Nat.pos_of_ne_zero hd)).surjective r
      obtain ⟨x, hx, hxs⟩ := Submodule.mem_map.mp s.property
      have htop : degreeResidues n d x = r := by
        rw [actualStageEquiv_apply, ← hxs, quotientDegreeResidues_mkQ] at hs
        exact hs
      have herror : ∀ p : MonicIrreducible k, d ≤ p.val.natDegree →
          (y - totalResidue n x) p = 0 := by
        intro p hp
        by_cases heq : p.val.natDegree = d
        · have hcoord := DFunLike.congr_fun htop (⟨p, heq⟩ : DegreePlace k d)
          change residueAt p.val n x = y p at hcoord
          simp only [DFinsupp.sub_apply, totalResidue_apply, hcoord, sub_self]
        · have hlt : d + 1 ≤ p.val.natDegree := by omega
          simp only [DFinsupp.sub_apply, hy p hlt, totalResidue_apply,
            residueAt_eq_zero_of_mem_lower n (d + 1) x hx p hlt, sub_self]
      obtain ⟨z, hz, hzr⟩ := ih (y - totalResidue n x) herror
      refine ⟨z + x, (lower k (n + 1) (d + 1)).add_mem
        (lower_mono (Nat.le_succ d) hz) hx, ?_⟩
      rw [map_add, hzr, sub_add_cancel]

end MilnorK.DegreeFiltration

namespace MilnorK.PolynomialResidue

open Polynomial DegreeFiltration

variable {k : Type*} [Field k]

/-- The actual finite polynomial residue map is surjective onto the dependent
finite sum of the original residue-field Milnor K_n groups. -/
theorem totalResidue_surjective (n : ℕ) : Function.Surjective (totalResidue (k := k) n) := by
  classical
  intro y
  let d := y.support.sup (fun p => p.val.natDegree) + 1
  have hy : ∀ p : MonicIrreducible k, d ≤ p.val.natDegree → y p = 0 := by
    intro p hp
    by_contra hne
    have hle := Finset.le_sup (f := fun p : MonicIrreducible k => p.val.natDegree)
      (DFinsupp.mem_support_iff.mpr hne)
    dsimp [d] at hp
    omega
  obtain ⟨x, _, hx⟩ := exists_mem_lower_totalResidue_eq n d y hy
  exact ⟨x, hx⟩

/-- Vanishing of every actual finite residue characterizes the constant image. -/
theorem totalResidue_eq_zero_iff_mem_constant_range (n : ℕ) (x : K (RatFunc k) (n + 1)) :
    totalResidue n x = 0 ↔
      x ∈ LinearMap.range (MilnorK.map (n + 1) (RatFunc.C : k →+* RatFunc k)) := by
  rw [← lower_one_eq_constant_range]
  exact totalResidue_eq_zero_iff_mem_lower_one n x

/-- Exactness at the original rational-function Milnor K_{n+1} group. This statement
does not assert injectivity of the initial constant map. -/
theorem ker_totalResidue_eq_constant_range (n : ℕ) :
    LinearMap.ker (totalResidue (k := k) n) =
      LinearMap.range (MilnorK.map (n + 1) (RatFunc.C : k →+* RatFunc k)) := by
  ext x
  exact totalResidue_eq_zero_iff_mem_constant_range n x

/-- The actual residue map kills every constant class. -/
@[simp] theorem totalResidue_map_constant (n : ℕ) (x : K k (n + 1)) :
    totalResidue n (MilnorK.map (n + 1) (RatFunc.C : k →+* RatFunc k) x) = 0 :=
  (totalResidue_eq_zero_iff_mem_constant_range n _).mpr ⟨x, rfl⟩

/-- The quotient by the proved constant-image kernel is exactly the finite
dependent sum of original finite-place Milnor K_n groups. -/
def quotientConstantEquivResidues (n : ℕ) :
    (K (RatFunc k) (n + 1) ⧸
      LinearMap.range (MilnorK.map (n + 1) (RatFunc.C : k →+* RatFunc k))) ≃ₗ[ℤ]
      Π₀ p : MonicIrreducible k, K (AdjoinRoot p.val) n :=
  (Submodule.quotEquivOfEq _ _ (ker_totalResidue_eq_constant_range n).symm).trans
    ((totalResidue (k := k) n).quotKerEquivOfSurjective (totalResidue_surjective n))

/-- The quotient equivalence computes the original actual residue vector. -/
@[simp] theorem quotientConstantEquivResidues_mk (n : ℕ) (x : K (RatFunc k) (n + 1)) :
    quotientConstantEquivResidues n (Submodule.Quotient.mk x) = totalResidue n x := by
  simp only [quotientConstantEquivResidues, LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]

/-- The actual rational-function sequence is short exact in every positive
Milnor degree: constants inject, their image is the kernel, and every finite
residue vector has a preimage. The degree-zero residue groups are included. -/
theorem rational_short_exact (n : ℕ) :
    Function.Injective (MilnorK.map (n + 1) (RatFunc.C : k →+* RatFunc k)) ∧
      LinearMap.ker (totalResidue (k := k) n) =
        LinearMap.range (MilnorK.map (n + 1) (RatFunc.C : k →+* RatFunc k)) ∧
      Function.Surjective (totalResidue (k := k) n) :=
  ⟨ConstantRestriction.constants_injective k (n + 1),
    ker_totalResidue_eq_constant_range n, totalResidue_surjective n⟩

end MilnorK.PolynomialResidue
