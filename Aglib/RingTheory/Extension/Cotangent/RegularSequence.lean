/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Extension.Basic
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.Data.List.OfFn
public import Mathlib.Algebra.BigOperators.Fin
/-!
# Original conormal classes of a regular kernel list

For a native algebra extension `E` and an ordered weakly regular list `s`
generating its original kernel, `cotangentBasisOfWeaklyRegular` is a basis
of the SAME `E.Cotangent`, over the SAME quotient algebra with its native
`E.σ` scalar action. Its vectors are literally the cotangent classes of
`s.get i`; no alternate quotient module or scalar action is introduced.

The proof first uses regularity of the last element modulo its predecessors
to show that every coefficient of an original zero relation lies in the
whole generated ideal. The same holds for relations lying in the square
of that ideal. Lifting quotient coefficients by the original `E.σ` proves
linear independence of the original conormal classes. Native cotangent
spanning then gives the basis.

Base, quotient and ambient ring universes are independent. Weak regularity
suffices, including empty lists, unit ideals and zero rings. The immediate
consumer is the original conormal sequence of a smooth surjection, using
the same ordered regular-kernel list on the same principal neighborhood.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
universe u v w
namespace Algebra.Extension
open RingTheory.Sequence
variable {A : Type*} [CommRing A]

private theorem regularCotangentCoefficientsOfZero {n : ℕ} (x : Fin n → A)
    (hx : IsWeaklyRegular A (List.ofFn x)) (a : Fin n → A)
    (ha : ∑ i, a i * x i = 0) :
    ∀ i, a i ∈ Ideal.span (Set.range x) := by
  induction n with
  | zero => intro i; exact i.elim0
  | succ n ih =>
    let y : Fin n → A := fun i => x i.castSucc
    let I : Ideal A := Ideal.span (Set.range y)
    let J : Ideal A := Ideal.span (Set.range x)
    have hI : Ideal.ofList (List.ofFn y) = I := by
      unfold Ideal.ofList I
      congr 1
      ext z
      simp only [Set.mem_ofPred_eq, List.mem_ofFn, Set.mem_range]
    have hseq : IsWeaklyRegular A (List.ofFn y ++ [x (Fin.last n)]) := by
      simpa only [List.ofFn_succ', List.concat_eq_append] using hx
    obtain ⟨hprev, htail⟩ := (isWeaklyRegular_append_iff A _ _).mp hseq
    have hr := (isWeaklyRegular_singleton_iff
      (A ⧸ (Ideal.ofList (List.ofFn y) • ⊤ : Submodule A A)) (x (Fin.last n))).mp htail
    rw [hI, Ideal.smul_eq_mul, Ideal.mul_top] at hr
    have hsum : (∑ i : Fin n, a i.castSucc * y i) ∈ I :=
      I.sum_mem fun i _ => I.mul_mem_left _ (Ideal.subset_span ⟨i, rfl⟩)
    have heq : x (Fin.last n) * a (Fin.last n) =
        -(∑ i : Fin n, a i.castSucc * y i) := by
      rw [mul_comm (x (Fin.last n)), eq_neg_iff_add_eq_zero, add_comm]
      simpa only [Fin.sum_univ_castSucc, y] using ha
    have hlast : a (Fin.last n) ∈ I :=
      mem_of_isSMulRegular_quotient_of_smul_mem hr (by
        change x (Fin.last n) * a (Fin.last n) ∈ I
        rw [heq]
        exact I.neg_mem hsum)
    obtain ⟨b, hb⟩ := Ideal.mem_span_range_iff_exists_fun.mp hlast
    let a' : Fin n → A := fun i => a i.castSucc + b i * x (Fin.last n)
    have ha' : ∑ i, a' i * y i = 0 := by
      calc
        ∑ i, a' i * y i = (∑ i, a i.castSucc * y i) +
            (∑ i, b i * y i) * x (Fin.last n) := by
          simp only [a', add_mul, Finset.sum_add_distrib, Finset.sum_mul, mul_right_comm]
        _ = 0 := by
          rw [hb]
          simpa only [Fin.sum_univ_castSucc] using ha
    have hmem := ih y hprev a' ha'
    have hIJ : I ≤ J := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact Ideal.subset_span ⟨i.castSucc, rfl⟩
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact hIJ hlast
    · have hsub := J.sub_mem (hIJ (hmem j))
        (J.mul_mem_left (b j) (Ideal.subset_span ⟨Fin.last n, rfl⟩))
      simpa only [a', add_sub_cancel_right] using hsub

private theorem regularCotangentCoefficientsOfSquare {n : ℕ} (x : Fin n → A)
    (hx : IsWeaklyRegular A (List.ofFn x)) (a : Fin n → A)
    (ha : ∑ i, a i * x i ∈ (Ideal.span (Set.range x)) ^ 2) :
    ∀ i, a i ∈ Ideal.span (Set.range x) := by
  classical
  let I : Ideal A := Ideal.span (Set.range x)
  have hsum : (∑ i, a i * x i) ∈ I • Submodule.span A (Set.range x) := by
    simpa only [I, Ideal.smul_eq_mul, pow_two] using ha
  obtain ⟨b, hb, heq⟩ :=
    (Submodule.mem_ideal_smul_span_iff_exists_sum I x (∑ i, a i * x i)).mp hsum
  have heq' : ∑ i, b i * x i = ∑ i, a i * x i := by
    calc
      ∑ i, b i * x i = b.sum (fun i c => c * x i) :=
        (Finsupp.sum_fintype b (fun i c => c * x i) (fun i => zero_mul (x i))).symm
      _ = ∑ i, a i * x i := by simpa only [smul_eq_mul] using heq
  have hrel : ∑ i, (a i - b i) * x i = 0 := by
    simp only [sub_mul, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr heq'.symm
  have hmem := regularCotangentCoefficientsOfZero x hx (fun i => a i - b i) hrel
  intro i
  simpa only [sub_add_cancel] using I.add_mem (hmem i) (hb i)

variable {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]

private def regularCotangentClass (E : Algebra.Extension.{w} R B) {n : ℕ} (x : Fin n → E.Ring)
    (hI : Ideal.span (Set.range x) = E.ker) (i : Fin n) : E.Cotangent :=
  Algebra.Extension.Cotangent.mk ⟨x i, hI.le (Ideal.subset_span ⟨i, rfl⟩)⟩

private theorem regularCotangentClassesLinearIndependent (E : Algebra.Extension.{w} R B) {n : ℕ}
    (x : Fin n → E.Ring) (hx : IsWeaklyRegular E.Ring (List.ofFn x))
    (hI : Ideal.span (Set.range x) = E.ker) :
    LinearIndependent B (regularCotangentClass E x hI) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro a ha i
  let z : E.ker := ∑ j, E.σ (a j) • ⟨x j, hI.le (Ideal.subset_span ⟨j, rfl⟩)⟩
  have hzero : Algebra.Extension.Cotangent.mk z = 0 := by
    calc
      Algebra.Extension.Cotangent.mk z =
          ∑ j, E.σ (a j) • regularCotangentClass E x hI j := by
        simp only [z, map_sum, map_smul, regularCotangentClass]
      _ = ∑ j, a j • regularCotangentClass E x hI j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [← algebraMap_smul B (E.σ (a j)), E.algebraMap_σ]
      _ = 0 := ha
  have hz := (Algebra.Extension.Cotangent.mk_eq_zero_iff z).mp hzero
  have hsq : ∑ j, E.σ (a j) * x j ∈ (Ideal.span (Set.range x)) ^ 2 := by
    rw [hI]
    simpa [z, smul_eq_mul] using hz
  have hmem : E.σ (a i) ∈ E.ker :=
    hI.le (regularCotangentCoefficientsOfSquare x hx (fun j => E.σ (a j)) hsq i)
  have heq : algebraMap E.Ring B (E.σ (a i)) = 0 := hmem
  rwa [E.algebraMap_σ] at heq

private def regularCotangentClassesBasis (E : Algebra.Extension.{w} R B) {n : ℕ}
    (x : Fin n → E.Ring) (hx : IsWeaklyRegular E.Ring (List.ofFn x))
    (hI : Ideal.span (Set.range x) = E.ker) :
    Module.Basis (Fin n) B E.Cotangent :=
  Module.Basis.mk (regularCotangentClassesLinearIndependent E x hx hI) (by
    exact le_of_eq (Algebra.Extension.Cotangent.span_eq_top_of_span_eq_ker (P := E) x hI).symm)

private theorem regularCotangentClassesBasisApply (E : Algebra.Extension.{w} R B) {n : ℕ}
    (x : Fin n → E.Ring) (hx : IsWeaklyRegular E.Ring (List.ofFn x))
    (hI : Ideal.span (Set.range x) = E.ker) (i : Fin n) :
    regularCotangentClassesBasis E x hx hI i =
      Algebra.Extension.Cotangent.mk ⟨x i, hI.le (Ideal.subset_span ⟨i, rfl⟩)⟩ :=
  Module.Basis.mk_apply _ _ i

private theorem regularCotangentSpanGet (s : List A) :
    Ideal.span (Set.range s.get) = Ideal.ofList s := by
  unfold Ideal.ofList
  congr 1
  ext a
  simp only [Set.mem_range, Set.mem_ofPred_eq, List.mem_iff_get]

/-- The original ordered classes of a weakly regular kernel list form a quotient-ring basis. -/
def cotangentBasisOfWeaklyRegular (E : Algebra.Extension.{w} R B) (s : List E.Ring)
    (hs : IsWeaklyRegular E.Ring s) (hker : Ideal.ofList s = E.ker) :
    Module.Basis (Fin s.length) B E.Cotangent :=
  private_decl% (regularCotangentClassesBasis E s.get
    (by simpa only [List.ofFn_get] using hs) ((regularCotangentSpanGet s).trans hker))

/-- Every basis vector is the original cotangent class of the same ordered generator. -/
theorem cotangentBasisOfWeaklyRegular_apply (E : Algebra.Extension.{w} R B) (s : List E.Ring)
    (hs : IsWeaklyRegular E.Ring s) (hker : Ideal.ofList s = E.ker) (i : Fin s.length) :
    E.cotangentBasisOfWeaklyRegular s hs hker i =
      Cotangent.mk ⟨s.get i, hker.le (Ideal.subset_span (s.get_mem i))⟩ :=
  regularCotangentClassesBasisApply E s.get
    (by simpa only [List.ofFn_get] using hs) ((regularCotangentSpanGet s).trans hker) i

end Algebra.Extension
