/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# Affine algebraic simplices and their face maps

The coordinate ring of the n-simplex is the actual quotient
`K[t₀,...,tₙ]/(∑ tᵢ - 1)`. A map of vertex sets induces a pullback
by adding barycentric coordinates over each fibre. All maps below are
constructed algebra homomorphisms, not assumed structure maps.
-/

@[expose] public section




noncomputable section

namespace AlgebraicGeometry.AlgebraicSimplex

open CategoryTheory

universe u v

variable (K : Type u) [CommRing K]

/-- The barycentric relation in the polynomial coordinate ring. -/
def relation (n : ℕ) : MvPolynomial (Fin (n + 1)) K :=
  (∑ i, MvPolynomial.X i) - 1

/-- The principal ideal imposing the barycentric relation. -/
def relationIdeal (n : ℕ) : Ideal (MvPolynomial (Fin (n + 1)) K) :=
  Ideal.span {relation K n}

/-- The coordinate ring of the affine algebraic n-simplex. -/
abbrev CoordinateRing (n : ℕ) :=
  MvPolynomial (Fin (n + 1)) K ⧸ relationIdeal K n

/-- The standard barycentric coordinate tᵢ. -/
def coordinate (n : ℕ) (i : Fin (n + 1)) : CoordinateRing K n :=
  Ideal.Quotient.mk (relationIdeal K n) (MvPolynomial.X i)

@[simp]
theorem sum_coordinate (n : ℕ) : ∑ i, coordinate K n i = 1 := by
  have h : Ideal.Quotient.mk (relationIdeal K n) (relation K n) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  simpa [relation, coordinate, map_sub, map_sum, sub_eq_zero] using h

/-- Algebra homomorphisms out of a simplex ring are determined by coordinates. -/
@[ext]
theorem hom_ext {n : ℕ} {A : Type v} [CommRing A] [Algebra K A]
    {f g : CoordinateRing K n →ₐ[K] A}
    (h : ∀ i, f (coordinate K n i) = g (coordinate K n i)) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  exact h i

/-- A tuple of elements summing to one defines a point over any K-algebra. -/
noncomputable def lift {n : ℕ} {A : Type v} [CommRing A] [Algebra K A]
    (a : Fin (n + 1) → A) (ha : ∑ i, a i = 1) : CoordinateRing K n →ₐ[K] A :=
  Ideal.Quotient.liftₐ (relationIdeal K n) (MvPolynomial.aeval a) (by
    intro p hp
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp hp
    simp [relation, map_mul, map_sub, map_sum, ha])

@[simp]
theorem lift_coordinate {n : ℕ} {A : Type v} [CommRing A] [Algebra K A]
    (a : Fin (n + 1) → A) (ha : ∑ i, a i = 1) (i : Fin (n + 1)) :
    lift K a ha (coordinate K n i) = a i := by
  change MvPolynomial.aeval a (MvPolynomial.X i) = a i
  simp

/-- Pullback of barycentric coordinates along a map of vertex sets. -/
noncomputable def pullback {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) :
    CoordinateRing K n →ₐ[K] CoordinateRing K m := by
  classical
  apply lift K (fun i => ∑ j, if f j = i then coordinate K m j else 0)
  rw [Finset.sum_comm]
  simp [sum_coordinate]

@[simp]
theorem pullback_coordinate {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1))
    (i : Fin (n + 1)) :
    pullback K f (coordinate K n i) =
      ∑ j, if f j = i then coordinate K m j else 0 := by
  classical
  simp [pullback]

@[simp]
theorem pullback_id (n : ℕ) : pullback K (id : Fin (n + 1) → Fin (n + 1)) =
    AlgHom.id K (CoordinateRing K n) := by
  ext i
  simp

/-- Contravariant composition holds for every map of finite vertex sets. -/
theorem pullback_comp {l m n : ℕ}
    (f : Fin (m + 1) → Fin (n + 1)) (g : Fin (l + 1) → Fin (m + 1)) :
    (pullback K g).comp (pullback K f) = pullback K (f ∘ g) := by
  classical
  ext i
  simp only [AlgHom.comp_apply, pullback_coordinate, map_sum, apply_ite, map_zero]
  have hsum : ∀ x : Fin (m + 1),
      (if f x = i then ∑ j, if g j = x then coordinate K l j else 0 else 0) =
      ∑ j, if f x = i then (if g j = x then coordinate K l j else 0) else 0 := by
    intro x
    split_ifs <;> simp
  simp_rw [hsum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  calc
    _ = ∑ x, if g j = x then (if f x = i then coordinate K l j else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> rfl
    _ = _ := by simp

/-- Restriction to the i-th face, obtained by omitting vertex i. -/
noncomputable def face {n : ℕ} (i : Fin (n + 2)) :
    CoordinateRing K (n + 1) →ₐ[K] CoordinateRing K n :=
  pullback K i.succAbove

@[simp]
theorem face_coordinate_self {n : ℕ} (i : Fin (n + 2)) :
    face K i (coordinate K (n + 1) i) = 0 := by
  classical
  simp [face, Fin.succAbove_ne]

@[simp]
theorem face_coordinate_succAbove {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) :
    face K i (coordinate K (n + 1) (i.succAbove j)) = coordinate K n j := by
  classical
  simp [face]


/-- The two orders of restricting to a codimension-two face agree. -/
theorem face_comp {n : ℕ} (i : Fin (n + 3)) (j : Fin (n + 2)) :
    (face K j).comp (face K i) =
      (face K (j.predAbove i)).comp (face K (i.succAbove j)) := by
  simp only [face, pullback_comp]
  congr 1
  funext k
  exact (Fin.succAbove_succAbove_succAbove_predAbove i j k).symm


/-- The eliminated-coordinate polynomial chart. -/
def toPolynomial (n : ℕ) : CoordinateRing K n →ₐ[K] MvPolynomial (Fin n) K :=
  lift K (Fin.cases (1 - ∑ j, MvPolynomial.X j) MvPolynomial.X) (by
    simp [Fin.sum_univ_succ])

/-- The n independent coordinates t₁,...,tₙ give the inverse chart. -/
def fromPolynomial (n : ℕ) : MvPolynomial (Fin n) K →ₐ[K] CoordinateRing K n :=
  MvPolynomial.aeval (fun j => coordinate K n j.succ)

@[simp]
theorem toPolynomial_coordinate_zero (n : ℕ) :
    toPolynomial K n (coordinate K n 0) = 1 - ∑ j, MvPolynomial.X j := by
  simp [toPolynomial]

@[simp]
theorem toPolynomial_coordinate_succ (n : ℕ) (i : Fin n) :
    toPolynomial K n (coordinate K n i.succ) = MvPolynomial.X i := by
  simp [toPolynomial]

@[simp]
theorem fromPolynomial_X (n : ℕ) (i : Fin n) :
    fromPolynomial K n (MvPolynomial.X i) = coordinate K n i.succ := by
  simp [fromPolynomial]

theorem toPolynomial_comp_fromPolynomial (n : ℕ) :
    (toPolynomial K n).comp (fromPolynomial K n) = AlgHom.id K _ := by
  ext i
  simp

theorem fromPolynomial_comp_toPolynomial (n : ℕ) :
    (fromPolynomial K n).comp (toPolynomial K n) = AlgHom.id K _ := by
  apply hom_ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [AlgHom.comp_apply, toPolynomial_coordinate_zero, map_sub, map_one,
      map_sum, fromPolynomial_X, AlgHom.id_apply]
    have h := sum_coordinate K n
    rw [Fin.sum_univ_succ] at h
    linear_combination -h
  · simp

/-- The simplex is affine n-space, with an explicit algebraic coordinate chart. -/
def polynomialEquiv (n : ℕ) : CoordinateRing K n ≃ₐ[K] MvPolynomial (Fin n) K :=
  AlgEquiv.ofAlgHom (toPolynomial K n) (fromPolynomial K n)
    (toPolynomial_comp_fromPolynomial K n) (fromPolynomial_comp_toPolynomial K n)

/-- The affine simplex over a domain is integral. -/
instance [IsDomain K] (n : ℕ) : IsDomain (CoordinateRing K n) :=
  MulEquiv.isDomain (MvPolynomial (Fin n) K) (polynomialEquiv K n).toRingEquiv.toMulEquiv

/-- Evaluation at a standard vertex. -/
def vertexEvaluation (n : ℕ) (i : Fin (n + 1)) : CoordinateRing K n →ₐ[K] K :=
  lift K (fun j => if j = i then 1 else 0) (by simp)

@[simp]
theorem vertexEvaluation_coordinate (n : ℕ) (i j : Fin (n + 1)) :
    vertexEvaluation K n i (coordinate K n j) = if j = i then 1 else 0 := by
  simp [vertexEvaluation]

/-- Every barycentric coordinate is a nonzero function over a nontrivial base. -/
theorem coordinate_ne_zero [Nontrivial K] (n : ℕ) (i : Fin (n + 1)) :
    coordinate K n i ≠ 0 := by
  intro h
  have he := congrArg (vertexEvaluation K n i) h
  simp at he

/-- Each face equation is a regular element over an integral base. -/
theorem coordinate_isRegular [IsDomain K] (n : ℕ) (i : Fin (n + 1)) :
    IsRegular (coordinate K n i) :=
  isRegular_iff_ne_zero.mpr (coordinate_ne_zero K n i)

/-- Restriction along any vertex injection is surjective on coordinate rings. -/
theorem pullback_surjective {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1))
    (hf : Function.Injective f) : Function.Surjective (pullback K f) := by
  classical
  let r := Function.invFun f
  have hr : r ∘ f = id := funext (Function.leftInverse_invFun hf)
  have h := pullback_comp K r f
  rw [hr, pullback_id] at h
  intro x
  refine ⟨pullback K r x, ?_⟩
  exact AlgHom.congr_fun h x

theorem face_surjective {n : ℕ} (i : Fin (n + 2)) :
    Function.Surjective (face K i) :=
  pullback_surjective K i.succAbove Fin.succAbove_right_injective

/-- The principal ideal cutting out the i-th face. -/
def faceIdeal {n : ℕ} (i : Fin (n + 2)) : Ideal (CoordinateRing K (n + 1)) :=
  Ideal.span {coordinate K (n + 1) i}

@[simp]
theorem faceIdeal_coordinate_eq_zero {n : ℕ} (i : Fin (n + 2)) :
    Ideal.Quotient.mk (faceIdeal K i) (coordinate K (n + 1) i) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

/-- The retained coordinates identify the smaller simplex with the face quotient. -/
def faceToQuotient {n : ℕ} (i : Fin (n + 2)) :
    CoordinateRing K n →ₐ[K] CoordinateRing K (n + 1) ⧸ faceIdeal K i :=
  lift K (fun j => Ideal.Quotient.mk (faceIdeal K i)
    (coordinate K (n + 1) (i.succAbove j))) (by
      have h := congrArg (Ideal.Quotient.mk (faceIdeal K i)) (sum_coordinate K (n + 1))
      rw [map_sum, map_one, Fin.sum_univ_succAbove _ i] at h
      simpa using h)

@[simp]
theorem faceToQuotient_coordinate {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) :
    faceToQuotient K i (coordinate K n j) =
      Ideal.Quotient.mk (faceIdeal K i) (coordinate K (n + 1) (i.succAbove j)) := by
  simp [faceToQuotient]

theorem faceToQuotient_comp_face {n : ℕ} (i : Fin (n + 2)) :
    (faceToQuotient K i).comp (face K i) = Ideal.Quotient.mkₐ K (faceIdeal K i) := by
  apply Ideal.Quotient.algHom_ext K
  apply MvPolynomial.algHom_ext
  intro k
  change faceToQuotient K i (face K i (coordinate K (n + 1) k)) =
    Ideal.Quotient.mk (faceIdeal K i) (coordinate K (n + 1) k)
  rcases Fin.eq_self_or_eq_succAbove i k with rfl | ⟨j, rfl⟩ <;> simp

/-- The face restriction has exactly the expected principal kernel. -/
theorem ker_face {n : ℕ} (i : Fin (n + 2)) :
    RingHom.ker (face K i) = faceIdeal K i := by
  apply le_antisymm
  · intro p hp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have h := AlgHom.congr_fun (faceToQuotient_comp_face K i) p
    rw [AlgHom.comp_apply, RingHom.mem_ker.mp hp, map_zero] at h
    exact h.symm
  · rw [faceIdeal, Ideal.span_singleton_le_iff_mem]
    exact RingHom.mem_ker.mpr (face_coordinate_self K i)

/-- Every coordinate face is integral over an integral base. -/
instance faceIdeal_isPrime [IsDomain K] {n : ℕ} (i : Fin (n + 2)) :
    (faceIdeal K i).IsPrime := by
  rw [← ker_face]
  exact RingHom.ker_isPrime (face K i)

/-- The i-th face is precisely the closed subscheme tᵢ = 0. -/
def faceQuotientEquiv {n : ℕ} (i : Fin (n + 2)) :
    (CoordinateRing K (n + 1) ⧸ faceIdeal K i) ≃ₐ[K] CoordinateRing K n :=
  (Ideal.quotientEquivAlgOfEq K (ker_face K i).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (face_surjective K i))

/-- The coordinate rings form a simplicial commutative K-algebra, contravariantly
corresponding to the cosimplicial affine algebraic simplex. -/
def simplicialCoordinateRing : SimplexCategoryᵒᵖ ⥤ CommAlgCat K where
  obj n := CommAlgCat.of K (CoordinateRing K n.unop.len)
  map f := CommAlgCat.ofHom (pullback K f.unop.toOrderHom)
  map_id n := by
    apply CommAlgCat.hom_ext
    exact pullback_id K n.unop.len
  map_comp f g := by
    apply CommAlgCat.hom_ext
    exact (pullback_comp K f.unop.toOrderHom g.unop.toOrderHom).symm


/-- Standard indexed face identity used by the alternating face differential. -/
theorem face_comp_of_le {n : ℕ} {i j : Fin (n + 2)} (h : i ≤ j) :
    (face K i).comp (face K j.succ) = (face K j).comp (face K i.castSucc) := by
  simp only [face, pullback_comp]
  congr 1
  funext k
  exact SimplexCategory.congr_toOrderHom_apply (SimplexCategory.δ_comp_δ h) k

/-- Ring maps out of simplex rings are determined on scalars and coordinates. -/
theorem ringHom_ext {n : ℕ} {A : Type v} [CommRing A]
    {f g : CoordinateRing K n →+* A}
    (hC : ∀ a, f (algebraMap K (CoordinateRing K n) a) =
      g (algebraMap K (CoordinateRing K n) a))
    (hX : ∀ i, f (coordinate K n i) = g (coordinate K n i)) : f = g := by
  apply Ideal.Quotient.ringHom_ext
  exact MvPolynomial.ringHom_ext hC hX

variable {K} {L : Type v} [CommRing L]

/-- Change of coefficients by an actual ring homomorphism. -/
def coefficientMap (f : K →+* L) (n : ℕ) : CoordinateRing K n →+* CoordinateRing L n :=
  Ideal.Quotient.lift (relationIdeal K n)
    (MvPolynomial.eval₂Hom ((algebraMap L (CoordinateRing L n)).comp f) (coordinate L n)) (by
      intro p hp
      obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp hp
      simp [relation, map_mul, map_sub, map_sum, sum_coordinate])

@[simp]
theorem coefficientMap_coordinate (f : K →+* L) (n : ℕ) (i : Fin (n + 1)) :
    coefficientMap f n (coordinate K n i) = coordinate L n i := by
  change MvPolynomial.eval₂Hom _ _ (MvPolynomial.X i) = _
  simp

@[simp]
theorem coefficientMap_algebraMap (f : K →+* L) (n : ℕ) (a : K) :
    coefficientMap f n (algebraMap K (CoordinateRing K n) a) =
      algebraMap L (CoordinateRing L n) (f a) := by
  change MvPolynomial.eval₂Hom _ _ (MvPolynomial.C a) = _
  simp

@[simp]
theorem coefficientMap_id (n : ℕ) :
    coefficientMap (RingHom.id K) n = RingHom.id (CoordinateRing K n) := by
  apply ringHom_ext K <;> intro x <;> simp

theorem coefficientMap_comp {M : Type*} [CommRing M] (f : K →+* L) (g : L →+* M)
    (n : ℕ) : (coefficientMap g n).comp (coefficientMap f n) =
      coefficientMap (g.comp f) n := by
  apply ringHom_ext K <;> intro x <;> simp

/-- Coefficient change commutes with every simplex pullback. -/
theorem coefficientMap_pullback (f : K →+* L) {m n : ℕ}
    (a : Fin (m + 1) → Fin (n + 1)) :
    (coefficientMap f m).comp (pullback K a).toRingHom =
      (pullback L a).toRingHom.comp (coefficientMap f n) := by
  classical
  apply ringHom_ext K
  · intro r
    simp
  · intro i
    simp [map_sum, apply_ite]

/-- Coefficient change commutes with each face restriction. -/
theorem coefficientMap_face (f : K →+* L) {n : ℕ} (i : Fin (n + 2)) :
    (coefficientMap f n).comp (face K i).toRingHom =
      (face L i).toRingHom.comp (coefficientMap f (n + 1)) :=
  coefficientMap_pullback f i.succAbove


/-- The underlying simplicial commutative ring. -/
def simplicialRing (K : Type u) [CommRing K] : SimplexCategoryᵒᵖ ⥤ CommRingCat.{u} :=
  simplicialCoordinateRing K ⋙ forget₂ (CommAlgCat K) CommRingCat

/-- Change of coefficients as a natural transformation of simplicial rings. -/
def simplicialCoefficientMap {L : Type u} [CommRing L] (f : K →+* L) :
    simplicialRing K ⟶ simplicialRing L where
  app n := CommRingCat.ofHom (coefficientMap f n.unop.len)
  naturality _ _ a := by
    apply CommRingCat.hom_ext
    exact coefficientMap_pullback f a.unop.toOrderHom

end AlgebraicGeometry.AlgebraicSimplex

/- Migration source: R5Lab/Aglib/AlgebraicGeometry/AlgebraicSimplex/Basic.lean
Frozen packet R5 f8a3314ddecffcada2ec721d26d56a937bed9690.
SHA-256 26183749fbe9e51d2951d31b94d20d36b8c1945241240c2b08fac0e74a805e9e.
Native names and imports replace the source wrappers; stated conditions and maps are retained. -/
