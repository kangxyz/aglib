/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
public import Aglib.LinearAlgebra.FrobeniusDifference
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
# Polynomial algebras of inhomogeneous matrix Frobenius equations

The literal quotient by `∑ j, B i j * X j ^ p - X i - C (y i)` represents
its solutions in every base algebra, naturally in the target. Its native
Jacobian is minus identity. For prime `p` vanishing in the base, the actual
map on prime spectra is surjective: every residue separable closure supplies
a solution of the original equations. No invertibility, nontriviality of the
base or test algebra, or global finiteness assumption is imposed.
-/

@[expose] public noncomputable section

open MvPolynomial

namespace Algebra.FrobeniusEquation

variable {A : Type*} [CommRing A] {ι : Type*} [Fintype ι]
  (p : ℕ) (B : Matrix ι ι A) (y : ι → A)

/-- The original coordinate equation for a matrix Frobenius root vector. -/
def equation (i : ι) : MvPolynomial ι A :=
  ∑ j, C (B i j) * X j ^ p - X i - C (y i)

/-- The actual ideal of the simultaneous inhomogeneous equations. -/
def equationIdeal : Ideal (MvPolynomial ι A) := Ideal.span (Set.range (equation p B y))

/-- The literal quotient representing the simultaneous inhomogeneous equations. -/
abbrev CoordinateAlgebra := MvPolynomial ι A ⧸ equationIdeal p B y

/-- The original coordinate class in the representing quotient. -/
def coordinate (i : ι) : CoordinateAlgebra p B y := Ideal.Quotient.mk _ (X i)

variable {S : Type*} [CommRing S] [Algebra A S]

/-- Solutions of the original equations, without a nontriviality assumption. -/
def Solutions :=
  {x : ι → S // ∀ i, ∑ j, algebraMap A S (B i j) * x j ^ p - x i = algebraMap A S (y i)}

lemma aeval_equation (x : ι → S) (i : ι) :
    aeval x (equation p B y i) =
      ∑ j, algebraMap A S (B i j) * x j ^ p - x i - algebraMap A S (y i) := by
  simp [equation]

lemma coordinate_equation (i : ι) :
    ∑ j, algebraMap A (CoordinateAlgebra p B y) (B i j) * coordinate p B y j ^ p -
      coordinate p B y i = algebraMap A (CoordinateAlgebra p B y) (y i) := by
  have h : Ideal.Quotient.mk (equationIdeal p B y) (equation p B y i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
  have hC : ∀ a : A, Ideal.Quotient.mk (equationIdeal p B y) (C a) =
      algebraMap A (CoordinateAlgebra p B y) a := fun _ => rfl
  simpa [equation, coordinate, hC, sub_eq_zero] using h

/-- The algebra map determined by an actual solution. -/
def lift (x : Solutions p B y (S := S)) : CoordinateAlgebra p B y →ₐ[A] S :=
  Ideal.Quotient.liftₐ _ (aeval x.val) (by
    intro f hf
    have hker : equationIdeal p B y ≤ RingHom.ker (aeval x.val).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      change aeval x.val (equation p B y i) = 0
      rw [aeval_equation, x.property i, sub_self]
    exact hker hf)

@[simp]
lemma lift_coordinate (x : Solutions p B y (S := S)) (i : ι) :
    lift p B y x (coordinate p B y i) = x.val i := by
  change aeval x.val (X i) = x.val i
  simp

/-- Evaluation of the original coordinates gives all solutions, uniquely. -/
def homEquivSolutions : (CoordinateAlgebra p B y →ₐ[A] S) ≃ Solutions p B y (S := S) where
  toFun h := ⟨fun i => h (coordinate p B y i), fun i => by
    have hi := congrArg h (coordinate_equation p B y i)
    simpa only [map_sum, map_mul, map_pow, map_sub, AlgHom.commutes] using hi⟩
  invFun := lift p B y
  left_inv h := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    exact lift_coordinate p B y _ i
  right_inv x := by
    apply Subtype.ext
    funext i
    exact lift_coordinate p B y x i

@[simp]
lemma homEquivSolutions_apply (h : CoordinateAlgebra p B y →ₐ[A] S) (i : ι) :
    (homEquivSolutions p B y h).val i = h (coordinate p B y i) := rfl

variable {T : Type*} [CommRing T] [Algebra A T]

/-- Original solutions are transported by the actual target algebra map. -/
def mapSolutions (f : S →ₐ[A] T) (x : Solutions p B y (S := S)) : Solutions p B y (S := T) :=
  ⟨fun i => f (x.val i), fun i => by
    have hi := congrArg f (x.property i)
    simpa only [map_sum, map_mul, map_pow, map_sub, AlgHom.commutes] using hi⟩

/-- Naturality is postcomposition on the original quotient maps. -/
theorem homEquivSolutions_naturality (f : S →ₐ[A] T)
    (h : CoordinateAlgebra p B y →ₐ[A] S) :
    homEquivSolutions p B y (f.comp h) = mapSolutions p B y f (homEquivSolutions p B y h) := rfl

/-- The original partial derivatives are those of minus the identity. -/
lemma pderiv_equation (hp : (p : A) = 0) (i j : ι) :
    pderiv j (equation p B y i) = -pderiv j (X i : MvPolynomial ι A) := by
  have hp' : (p : MvPolynomial ι A) = 0 := by
    simpa using congrArg (C : A →+* MvPolynomial ι A) hp
  simp [equation, hp']

/-- The native presentation of the actual equation quotient. -/
private def presentation : PreSubmersivePresentation A (CoordinateAlgebra p B y) ι ι where
  __ := Algebra.Presentation.naive (v := equation p B y)
  map := fun i => i
  map_inj := Function.injective_id

private lemma presentation_jacobiMatrix [DecidableEq ι] (hp : (p : A) = 0) :
    (presentation p B y).jacobiMatrix = -1 := by
  apply Matrix.ext
  intro i j
  rw [PreSubmersivePresentation.jacobiMatrix_apply]
  change pderiv i (equation p B y j) = _
  rw [pderiv_equation p B y hp]
  simp [pderiv_X, Matrix.one_apply, Pi.single_apply, eq_comm]

/-- The quotient is etale since the actual square Jacobian is minus identity.
This also covers an empty coordinate set and the zero base ring. -/
theorem etale (hp : (p : A) = 0) : Algebra.Etale A (CoordinateAlgebra p B y) := by
  classical
  let P : SubmersivePresentation A (CoordinateAlgebra p B y) ι ι :=
    { presentation p B y with
      jacobian_isUnit := by
        rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
          presentation_jacobiMatrix p B y hp]
        simp only [Matrix.det_neg, Matrix.det_one, mul_one, map_pow, map_neg, map_one]
        have hunit : IsUnit (-1 : CoordinateAlgebra p B y) :=
          ⟨⟨-1, -1, (neg_mul_neg (1 : CoordinateAlgebra p B y) 1).trans (one_mul 1),
            (neg_mul_neg (1 : CoordinateAlgebra p B y) 1).trans (one_mul 1)⟩, rfl⟩
        exact hunit.pow _ }
  apply Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.mpr
  exact P.isStandardSmoothOfRelativeDimension (by simp [Algebra.Presentation.dimension])

/-- Every inhomogeneous system has a solution over a separably closed target field.
The temporary matrix operator is native Frobenius-semilinear, not assumed invertible. -/
theorem exists_solution_of_isSepClosed (hp : p.Prime) (hA : (p : A) = 0)
    (k : Type*) [Field k] [Algebra A k] [IsSepClosed k] :
    Nonempty (Solutions p B y (S := k)) := by
  let : Fact p.Prime := ⟨hp⟩
  have hk : (p : k) = 0 := by simpa using congrArg (algebraMap A k) hA
  let : CharP k p := (CharP.charP_iff_prime_eq_zero hp).2 hk
  let F₀ : (ι → k) →ₛₗ[_root_.frobenius k p] (ι → k) :=
    { toFun := fun x i => _root_.frobenius k p (x i)
      map_add' := fun x z => funext fun i => map_add (_root_.frobenius k p) (x i) (z i)
      map_smul' := fun a x => funext fun i => map_mul (_root_.frobenius k p) a (x i) }
  let F : (ι → k) →ₛₗ[_root_.frobenius k p] (ι → k) :=
    (B.map (algebraMap A k)).mulVecLin.comp F₀
  obtain ⟨x, hx⟩ := LinearMap.surjective_sub_id_of_frobenius p F
    (fun i => algebraMap A k (y i))
  exact ⟨⟨x, fun i => congrFun hx i⟩⟩

/-- The actual base map covers the prime spectrum. A zero base has no primes;
no nontriviality hypothesis is placed on it or on arbitrary test algebras. -/
theorem spectrum_surjective (hp : p.Prime) (hA : (p : A) = 0) :
    Function.Surjective (PrimeSpectrum.comap (algebraMap A (CoordinateAlgebra p B y))) := by
  intro P
  let k := SeparableClosure P.asIdeal.ResidueField
  let : Algebra A k := Algebra.compHom k (algebraMap A P.asIdeal.ResidueField)
  obtain ⟨x⟩ := exists_solution_of_isSepClosed p B y hp hA k
  let f : CoordinateAlgebra p B y →ₐ[A] k := lift p B y x
  refine ⟨⟨RingHom.ker f.toRingHom, RingHom.ker_isPrime _⟩, ?_⟩
  apply PrimeSpectrum.ext
  change (RingHom.ker f.toRingHom).comap (algebraMap A (CoordinateAlgebra p B y)) = P.asIdeal
  have hf : f.toRingHom.comp (algebraMap A (CoordinateAlgebra p B y)) = algebraMap A k :=
    f.comp_algebraMap
  rw [RingHom.comap_ker, hf]
  change RingHom.ker ((algebraMap P.asIdeal.ResidueField k).comp
    (algebraMap A P.asIdeal.ResidueField)) = P.asIdeal
  rw [RingHom.ker_comp_of_injective _ (RingHom.injective _),
    Ideal.ker_algebraMap_residueField]

end Algebra.FrobeniusEquation
