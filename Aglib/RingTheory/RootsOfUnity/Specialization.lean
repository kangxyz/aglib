/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Valuation.ResidualGalois
public import Aglib.RingTheory.IntegralClosure.Inertia
public import Aglib.RingTheory.RootsOfUnity.Reduction
public import Aglib.RingTheory.RootsOfUnity.Inclusion
public import Aglib.RingTheory.RootsOfUnity.FieldEmbedding
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Prime-to-residue-characteristic root specialization

Source: `R5Lab.Aglib.RingTheory.RootsOfUnity.Specialization`,
revision `f8a3314ddecffcada2ec721d26d56a937bed9690`. Exact field, action, embedding and
explicit-data hypotheses are retained. Native objects and maps are reused.
-/

@[expose] public section

noncomputable section
namespace Field.absoluteGaloisGroup.RootsOfUnity.Specialization
universe u
open Valuation.ResidualGalois
open Field.absoluteGaloisGroup.RootsOfUnity
open Field.absoluteGaloisGroup.RootsOfUnity.Reduction
open Field.absoluteGaloisGroup.RootsOfUnity.Inclusion

variable (K : Type u) [NontriviallyNormedField K]
  [hUltra : IsUltrametricDist K] [hComplete : CompleteSpace K]
  (V : ValuationSubring K) [Fact (∀ x : K, x ∈ V ↔ ‖x‖₊ ≤ 1)]

/-- Supporting root/coefficient/inertia slice of `K2-015#lem:k2015-frobenius` at
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`, original proof lines 376–392.
This declaration covers its stated local slice only. -/
def rootInteger (n : ℕ) (hn : 0 < n) (x : Mu K n) : ClosureIntegers K :=
  integralClosureEquiv K V (integralClosure.Inertia.rootElement V K n hn x)

/-- Supporting root/coefficient/inertia slice of `K2-015#lem:k2015-frobenius` at
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`, original proof lines 376–392.
This declaration covers its stated local slice only. -/
@[simp] theorem rootInteger_coe (n : ℕ) (hn : 0 < n) (x : Mu K n) :
    (rootInteger K V n hn x : AlgebraicClosure K) =
      ((x.toMul : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) := by
  exact integralClosureEquiv_coe K V _

/-- Supporting root/coefficient/inertia slice of `K2-015#lem:k2015-frobenius` at
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`, original proof lines 376–392.
This declaration covers its stated local slice only. -/
@[simp] theorem rootInteger_pow (n : ℕ) (hn : 0 < n) (x : Mu K n) :
    rootInteger K V n hn x ^ n = 1 := by
  rw [rootInteger, ← map_pow, integralClosure.Inertia.rootElement_pow, map_one]

/-- Supporting root/coefficient/inertia slice of `K2-015#lem:k2015-frobenius` at
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`, original proof lines 376–392.
This declaration covers its stated local slice only. -/
def rootUnit (n : ℕ) (hn : 0 < n) (x : Mu K n) : (ClosureIntegers K)ˣ where
  val := rootInteger K V n hn x
  inv := rootInteger K V n hn (-x)
  val_inv := by apply Subtype.ext; simp
  inv_val := by apply Subtype.ext; simp

/-- Supporting root/coefficient/inertia slice of `K2-015#lem:k2015-frobenius` at
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`, original proof lines 376–392.
This declaration covers its stated local slice only. -/
def rootsMap (n : ℕ) (hn : 0 < n) : rootsOfUnity n (AlgebraicClosure K) →*
    rootsOfUnity n (AlgebraicClosure (IsLocalRing.ResidueField V)) where
  toFun x := ⟨Units.map (closureReduction K V).toMonoidHom
    (rootUnit K V n hn (Additive.ofMul x)), by
      rw [mem_rootsOfUnity, ← map_pow]
      have h : rootUnit K V n hn (Additive.ofMul x) ^ n = 1 := by
        apply Units.ext
        exact rootInteger_pow K V n hn _
      rw [h, map_one]⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    change closureReduction K V (rootInteger K V n hn 0) = 1
    have h : rootInteger K V n hn 0 = 1 := by apply Subtype.ext; simp
    rw [h, map_one]
  map_mul' x y := by
    apply Subtype.ext
    apply Units.ext
    change closureReduction K V (rootInteger K V n hn (Additive.ofMul (x * y))) =
      closureReduction K V (rootInteger K V n hn (Additive.ofMul x)) *
        closureReduction K V (rootInteger K V n hn (Additive.ofMul y))
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    simp

/-- Supporting root/coefficient/inertia slice of `K2-015#lem:k2015-frobenius` at
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`, original proof lines 376–392.
This declaration covers its stated local slice only. -/
def muMap (n : ℕ) (hn : 0 < n) : Mu K n →+ Mu (IsLocalRing.ResidueField V) n :=
  (rootsMap K V n hn).toAdditive

/-- Supporting root/coefficient/inertia slice of `K2-015#lem:k2015-frobenius` at
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`, original proof lines 376–392.
This declaration covers its stated local slice only. -/
@[simp] theorem muMap_value (n : ℕ) (hn : 0 < n) (x : Mu K n) :
    (((muMap K V n hn x).toMul : (AlgebraicClosure (IsLocalRing.ResidueField V))ˣ) :
      AlgebraicClosure (IsLocalRing.ResidueField V)) =
    closureReduction K V (rootInteger K V n hn x) := rfl

/-- Supporting root/coefficient/inertia slice of `K2-015#lem:k2015-frobenius` at
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`, original proof lines 376–392.
This declaration covers its stated local slice only. -/
theorem muMap_injective (n : ℕ) (hn : 0 < n)
    (hu : IsUnit (n : IsLocalRing.ResidueField V)) : Function.Injective (muMap K V n hn) := by
  intro x y h
  have hnV : IsUnit (n : V) :=
    isUnit_of_map_unit (IsLocalRing.residue V) _ (by simpa using hu)
  have hnW : IsUnit (n : ClosureIntegers K) := by
    simpa using hnV.map (algebraMap V (ClosureIntegers K))
  have hval := congrArg (fun z : Mu (IsLocalRing.ResidueField V) n =>
    ((z.toMul : (AlgebraicClosure (IsLocalRing.ResidueField V))ˣ) :
      AlgebraicClosure (IsLocalRing.ResidueField V))) h
  have hres := (residueClosureEquiv K V).injective hval
  have hxy := integralClosure.Inertia.root_eq_of_residue_eq (IsLocalRing.maximalIdeal
    (ClosureIntegers K)) n
    (Ideal.notMem_of_isUnit _ hnW) (rootInteger_pow K V n hn x) (rootInteger_pow K V n hn y) hres
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  simpa using congrArg (fun z : ClosureIntegers K => (z : AlgebraicClosure K)) hxy

/-- Supporting root/coefficient/inertia slice of `K2-015#lem:k2015-frobenius` at
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`, original proof lines 376–392.
This declaration covers its stated local slice only. -/
theorem muMap_bijective (n : ℕ) (hn : 0 < n)
    (hu : IsUnit (n : IsLocalRing.ResidueField V)) : Function.Bijective (muMap K V n hn) := by
  let : NeZero n := ⟨hn.ne'⟩
  have hnV : IsUnit (n : V) :=
    isUnit_of_map_unit (IsLocalRing.residue V) _ (by simpa using hu)
  let : NeZero (n : K) := ⟨(show IsUnit (n : K) from by
    simpa using hnV.map (algebraMap V K)).ne_zero⟩
  apply (muMap_injective K V n hn hu).bijective_of_nat_card_le
  change Nat.card (rootsOfUnity n (AlgebraicClosure (IsLocalRing.ResidueField V))) ≤
    Nat.card (rootsOfUnity n (AlgebraicClosure K))
  rw [HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure K) n]
  exact card_rootsOfUnity (AlgebraicClosure (IsLocalRing.ResidueField V)) n

/-- Supporting root/coefficient/inertia slice of `K2-015#lem:k2015-frobenius` at
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`, original proof lines 376–392.
This declaration covers its stated local slice only. -/
def muEquiv (n : ℕ) (hn : 0 < n) (hu : IsUnit (n : IsLocalRing.ResidueField V)) :
    Mu K n ≃+ Mu (IsLocalRing.ResidueField V) n :=
  AddEquiv.ofBijective (muMap K V n hn) (muMap_bijective K V n hn hu)

/-- Supporting root/coefficient/inertia slice of `K2-015#lem:k2015-frobenius` at
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`, original proof lines 376–392.
This declaration covers its stated local slice only. -/
theorem muMap_primitive (n : ℕ) (hn : 0 < n)
    (hu : IsUnit (n : IsLocalRing.ResidueField V)) (x : Mu K n)
    (hx : IsPrimitiveRoot (x.toMul : (AlgebraicClosure K)ˣ) n) :
    IsPrimitiveRoot ((muMap K V n hn x).toMul :
      (AlgebraicClosure (IsLocalRing.ResidueField V))ˣ) n := by
  have hx' : IsPrimitiveRoot x.toMul n :=
    hx.of_map_of_injective (f := (rootsOfUnity n (AlgebraicClosure K)).subtype)
      Subtype.val_injective
  have hi : Function.Injective (rootsMap K V n hn) := muMap_injective K V n hn hu
  exact (hx'.map_of_injective hi).map_of_injective
    (f := (rootsOfUnity n (AlgebraicClosure (IsLocalRing.ResidueField V))).subtype)
    Subtype.val_injective

/-- Supporting root/coefficient/inertia slice of `K2-015#lem:k2015-frobenius` at
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`, original proof lines 376–392.
This declaration covers its stated local slice only. -/
theorem muMap_smul (n : ℕ) (hn : 0 < n) (g : Field.absoluteGaloisGroup K) (x : Mu K n) :
    muMap K V n hn (g • x) = absoluteResidue K V g • muMap K V n hn x := by
  have hroot : rootInteger K V n hn (g • x) = integerAut K V g (rootInteger K V n hn x) := by
    apply Subtype.ext
    simp only [rootInteger_coe]
    change AlgEquiv.toAlgHom g (((x.toMul : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)) =
      AlgEquiv.toAlgHom g (rootInteger K V n hn x : AlgebraicClosure K)
    rw [rootInteger_coe]
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  change closureReduction K V (rootInteger K V n hn (g • x)) =
    AlgEquiv.toAlgHom (absoluteResidueHom K V g)
      (closureReduction K V (rootInteger K V n hn x))
  rw [hroot]
  exact (absoluteResidueHom_residue K V g (rootInteger K V n hn x)).symm

/-- Supporting root/coefficient/inertia slice of `K2-015#lem:k2015-frobenius` at
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`, original proof lines 376–392.
This declaration covers its stated local slice only. -/
theorem muMap_muReduction (d e : ℕ) (hd : 0 < d) (he : 0 < e) (x : Mu K (d * e)) :
    muMap K V d hd (muReduction K d e x) =
      muReduction (IsLocalRing.ResidueField V) d e (muMap K V (d * e) (Nat.mul_pos hd he) x) := by
  have hi : rootInteger K V d hd (muReduction K d e x) =
      rootInteger K V (d * e) (Nat.mul_pos hd he) x ^ e := by
    apply Subtype.ext
    change (rootInteger K V d hd (muReduction K d e x) : AlgebraicClosure K) =
      (rootInteger K V (d * e) (Nat.mul_pos hd he) x : AlgebraicClosure K) ^ e
    rw [rootInteger_coe, rootInteger_coe]
    rfl
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  change closureReduction K V (rootInteger K V d hd (muReduction K d e x)) =
    (closureReduction K V (rootInteger K V (d * e) (Nat.mul_pos hd he) x)) ^ e
  rw [hi, map_pow]

/-- Supporting root/coefficient/inertia slice of `K2-015#lem:k2015-frobenius` at
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`, original proof lines 376–392.
This declaration covers its stated local slice only. -/
theorem muMap_muInclusion (d e : ℕ) (hd : 0 < d) (he : 0 < e) (x : Mu K d) :
    muMap K V (d * e) (Nat.mul_pos hd he) (muInclusion K d e x) =
      muInclusion (IsLocalRing.ResidueField V) d e (muMap K V d hd x) := by
  have hi : rootInteger K V (d * e) (Nat.mul_pos hd he) (muInclusion K d e x) =
      rootInteger K V d hd x := by
    apply Subtype.ext
    simp only [rootInteger_coe, muInclusion_value]
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  exact congrArg (closureReduction K V) hi

section Global
open _root_.AlgebraicGeometry.Scheme.FiniteEtale
variable {F : Type u} [Field F] [CharZero F] [hCharK : CharZero K] (i : F →+* K)

/-- Supporting root/coefficient/inertia slice of `K2-015#lem:k2015-frobenius` at
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`, original proof lines 376–392.
This declaration covers its stated local slice only. -/
def embeddingMu (n : ℕ) (hn : 0 < n) : Mu F n ≃+ Mu K n := by
  let : NeZero n := ⟨hn.ne'⟩
  exact FieldEmbedding.rootEmbeddingEquiv i n
omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- Supporting root/coefficient/inertia slice of `K2-015#lem:k2015-frobenius` at
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`, original proof lines 376–392.
This declaration covers its stated local slice only. -/
@[simp] theorem embeddingMu_value (n : ℕ) (hn : 0 < n) (x : Mu F n) :
    (((embeddingMu K i n hn x).toMul : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) =
      FieldEmbeddingBaseChange.closureEmbedding i
        (((x.toMul : (AlgebraicClosure F)ˣ) : AlgebraicClosure F)) := rfl
omit [IsUltrametricDist K] [CompleteSpace K] in
/-- Supporting root/coefficient/inertia slice of `K2-015#lem:k2015-frobenius` at
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`, original proof lines 376–392.
This declaration covers its stated local slice only. -/
theorem embeddingMu_smul (n : ℕ) (hn : 0 < n) (g : Field.absoluteGaloisGroup K) (x : Mu F n) :
    embeddingMu K i n hn (FieldEmbeddingBaseChange.absoluteRestriction i g • x) =
      g • embeddingMu K i n hn x := by
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  exact FieldEmbeddingBaseChange.absoluteRestriction_commutes i g _

-- Retain the original field and topology assumptions as explicit theorem inputs.
omit hUltra hComplete hCharK in
/-- Supporting root/coefficient/inertia slice of `K2-015#lem:k2015-frobenius` at
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`, original proof lines 376–392.
This declaration covers its stated local slice only. -/
@[nolint unusedArguments]
theorem embeddingMu_primitive [IsUltrametricDist K] [CompleteSpace K] [CharZero K]
    (n : ℕ) (hn : 0 < n) (x : Mu F n)
    (hx : IsPrimitiveRoot (x.toMul : (AlgebraicClosure F)ˣ) n) :
    IsPrimitiveRoot ((embeddingMu K i n hn x).toMul : (AlgebraicClosure K)ˣ) n := by
  apply IsPrimitiveRoot.coe_units_iff.mp
  rw [embeddingMu_value]
  exact (IsPrimitiveRoot.coe_units_iff.mpr hx).map_of_injective
    (FieldEmbeddingBaseChange.closureEmbedding i).injective
omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- Supporting root/coefficient/inertia slice of `K2-015#lem:k2015-frobenius` at
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`, original proof lines 376–392.
This declaration covers its stated local slice only. -/
theorem embeddingMu_muReduction (d e : ℕ) (hd : 0 < d) (he : 0 < e) (x : Mu F (d * e)) :
    embeddingMu K i d hd (muReduction F d e x) =
      muReduction K d e (embeddingMu K i (d * e) (Nat.mul_pos hd he) x) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  change FieldEmbeddingBaseChange.closureEmbedding i
    ((((x.toMul : (AlgebraicClosure F)ˣ) : AlgebraicClosure F)) ^ e) =
      (FieldEmbeddingBaseChange.closureEmbedding i
        (((x.toMul : (AlgebraicClosure F)ˣ) : AlgebraicClosure F))) ^ e
  exact map_pow _ _ _
omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- Supporting root/coefficient/inertia slice of `K2-015#lem:k2015-frobenius` at
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`, original proof lines 376–392.
This declaration covers its stated local slice only. -/
theorem embeddingMu_muInclusion (d e : ℕ) (hd : 0 < d) (he : 0 < e) (x : Mu F d) :
    embeddingMu K i (d * e) (Nat.mul_pos hd he) (muInclusion F d e x) =
      muInclusion K d e (embeddingMu K i d hd x) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  rfl

/-- Supporting root/coefficient/inertia slice of `K2-015#lem:k2015-frobenius` at
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`, original proof lines 376–392.
This declaration covers its stated local slice only. -/
def globalMuMap (n : ℕ) (hn : 0 < n) : Mu F n →+ Mu (IsLocalRing.ResidueField V) n :=
  (muMap K V n hn).comp (embeddingMu K i n hn).toAddMonoidHom

/-- Supporting root/coefficient/inertia slice of `K2-015#lem:k2015-frobenius` at
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`, original proof lines 376–392.
This declaration covers its stated local slice only. -/
def globalMuEquiv (n : ℕ) (hn : 0 < n) (hu : IsUnit (n : IsLocalRing.ResidueField V)) :
    Mu F n ≃+ Mu (IsLocalRing.ResidueField V) n :=
  (embeddingMu K i n hn).trans (muEquiv K V n hn hu)

/-- Supporting root/coefficient/inertia slice of `K2-015#lem:k2015-frobenius` at
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`, original proof lines 376–392.
This declaration covers its stated local slice only. -/
theorem globalMuMap_primitive (n : ℕ) (hn : 0 < n) (hu : IsUnit (n : IsLocalRing.ResidueField V))
    (x : Mu F n) (hx : IsPrimitiveRoot (x.toMul : (AlgebraicClosure F)ˣ) n) :
    IsPrimitiveRoot ((globalMuMap K V i n hn x).toMul :
      (AlgebraicClosure (IsLocalRing.ResidueField V))ˣ) n :=
  muMap_primitive K V n hn hu _ (embeddingMu_primitive K i n hn x hx)

/-- Supporting root/coefficient/inertia slice of `K2-015#lem:k2015-frobenius` at
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`, original proof lines 376–392.
This declaration covers its stated local slice only. -/
theorem globalMuMap_smul (n : ℕ) (hn : 0 < n) (g : Field.absoluteGaloisGroup K) (x : Mu F n) :
    globalMuMap K V i n hn (FieldEmbeddingBaseChange.absoluteRestriction i g • x) =
      absoluteResidue K V g • globalMuMap K V i n hn x := by
  change muMap K V n hn (embeddingMu K i n hn
    (FieldEmbeddingBaseChange.absoluteRestriction i g • x)) = _
  rw [embeddingMu_smul, muMap_smul]
  rfl

-- Retain the original characteristic-zero target-field input.
omit hCharK in
/-- Supporting root/coefficient/inertia slice of `K2-015#lem:k2015-frobenius` at
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`, original proof lines 376–392.
This declaration covers its stated local slice only. -/
@[nolint unusedArguments]
theorem globalMuMap_muReduction [CharZero K] (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (x : Mu F (d * e)) :
    globalMuMap K V i d hd (muReduction F d e x) =
      muReduction (IsLocalRing.ResidueField V) d e
        (globalMuMap K V i (d * e) (Nat.mul_pos hd he) x) := by
  change muMap K V d hd (embeddingMu K i d hd (muReduction F d e x)) = _
  rw [embeddingMu_muReduction K i d e hd he, muMap_muReduction K V d e hd he]
  rfl

-- Retain the original characteristic-zero target-field input.
omit hCharK in
/-- Supporting root/coefficient/inertia slice of `K2-015#lem:k2015-frobenius` at
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`, original proof lines 376–392.
This declaration covers its stated local slice only. -/
@[nolint unusedArguments]
theorem globalMuMap_muInclusion [CharZero K] (d e : ℕ) (hd : 0 < d) (he : 0 < e) (x : Mu F d) :
    globalMuMap K V i (d * e) (Nat.mul_pos hd he) (muInclusion F d e x) =
      muInclusion (IsLocalRing.ResidueField V) d e (globalMuMap K V i d hd x) := by
  change muMap K V (d * e) (Nat.mul_pos hd he)
    (embeddingMu K i (d * e) (Nat.mul_pos hd he) (muInclusion F d e x)) = _
  rw [embeddingMu_muInclusion K i d e hd he, muMap_muInclusion K V d e hd he]
  rfl

end Global
end Field.absoluteGaloisGroup.RootsOfUnity.Specialization
