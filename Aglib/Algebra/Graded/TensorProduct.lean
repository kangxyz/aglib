/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.LinearAlgebra.DirectSum.TensorProduct

/-!
# Canonical linear regrouping of native graded tensors

Mathlib's existing tensor/direct-sum distribution is followed by the
original sigma-fiber reindexing, linearly over its unchanged component
modules. No basis, replacement tensor or comparison module is selected.
The whole underlying-map formula is proved before any geometric application.
-/

@[expose] public noncomputable section

open scoped TensorProduct DirectSum

universe u

namespace DirectSum

section Reindex

universe i j a
variable {R : Type u} [CommSemiring R] {ι : Type i} {κ : Type j}
  {A : ι → Type a} [∀ i, AddCommMonoid (A i)] [∀ i, Module R (A i)]

/-- Native fiber reindexing is linear for the original componentwise actions. -/
def sigmaFiberLinearEquiv [DecidableEq κ] (f : ι → κ) :
    (⨁ i, A i) ≃ₗ[R] ⨁ (j : κ) (i : {i : ι // f i = j}), A i.val :=
  (lequivCongrLeft R (Equiv.sigmaFiberEquiv f).symm).trans
    (sigmaLcurryEquiv R (δ := fun j (i : {i : ι // f i = j}) => A i.val))

/-- The fiber comparison retains the original native coordinate. -/
theorem sigmaFiberLinearEquiv_apply_apply [DecidableEq κ] (f : ι → κ)
    (x : ⨁ i, A i) (j : κ) (i : {i : ι // f i = j}) :
    sigmaFiberLinearEquiv (R := R) f x j i = x i.val := rfl

/-- Original single-support values of the canonical fiber reindexing. -/
theorem sigmaFiberLinearEquiv_lof [DecidableEq ι] [DecidableEq κ] (f : ι → κ)
    (i : ι) (x : A i) :
    sigmaFiberLinearEquiv (R := R) f (lof R ι A i x) =
      lof R κ _ (f i) (lof R _ _ ⟨i, rfl⟩ x) := by
  change sigmaLcurryEquiv R (δ := fun j (i : {i : ι // f i = j}) => A i.val)
    (lequivCongrLeft R (Equiv.sigmaFiberEquiv f).symm (lof R ι A i x)) = _
  rw [lequivCongrLeft_lof (R := R) (e := (Equiv.sigmaFiberEquiv f).symm)
    (i := i) (k := ⟨f i, ⟨i, rfl⟩⟩) rfl x x rfl]
  exact sigmaCurry_of (δ := fun j (i : {i : ι // f i = j}) => A i.val)
    ⟨f i, ⟨i, rfl⟩⟩ x

end Reindex

section ChosenOperators

universe a b c i
variable {R : Type u} [CommSemiring R] {ι : Type i}
  {A : Type a} [AddCommMonoid A] [Module R A]
  {F : ι → Type b} [∀ i, AddCommMonoid (F i)] [∀ i, Module R (F i)]
  {P : ι → Type c} [∀ i, AddCommMonoid (P i)] [∀ i, Module R (P i)]

/-- Sum the given component maps after the already chosen source comparison. -/
def mapAfterEquiv (E : A ≃ₗ[R] ⨁ i, F i) (G : ∀ i, F i →ₗ[R] P i) :
    A →ₗ[R] ⨁ i, P i :=
  DirectSum.lmap G ∘ₗ E.toLinearMap

/-- Whole factorization with the actual supplied operator data. -/
def MapFactorization (L : A →ₗ[R] ⨁ i, P i)
    (E : A ≃ₗ[R] ⨁ i, F i) (G : ∀ i, F i →ₗ[R] P i) : Prop :=
  ∀ z, L z = DirectSum.lmap G (E z)

/-- The complete composition retains the same given E in its value formula. -/
theorem mapAfterEquiv_apply (E : A ≃ₗ[R] ⨁ i, F i) (G : ∀ i, F i →ₗ[R] P i) (z : A) :
    mapAfterEquiv E G z = DirectSum.lmap G (E z) := rfl

/-- The entire chosen composition satisfies its literal regular factorization. -/
theorem mapAfterEquiv_factorization (E : A ≃ₗ[R] ⨁ i, F i) (G : ∀ i, F i →ₗ[R] P i) :
    MapFactorization (mapAfterEquiv E G) E G := fun _ => rfl

/-- Original chosen source and inclusion values determine the same given total operator. -/
theorem MapFactorization.values [DecidableEq ι]
    {L : A →ₗ[R] ⨁ i, P i} {E : A ≃ₗ[R] ⨁ i, F i}
    {G : ∀ i, F i →ₗ[R] P i} (hL : MapFactorization L E G)
    {I J : Type*} {M : I → Type*} {N : J → Type*}
    (degree : I → J → ι) (source : ∀ p q, M p → N q → A)
    (inclusion : ∀ i, P i → ⨁ i, P i)
    (fiberValue : ∀ p q, M p → N q → F (degree p q))
    (value : ∀ p q, M p → N q → P (degree p q))
    (hSource : ∀ p q x y, E (source p q x y) =
      lof R ι F (degree p q) (fiberValue p q x y))
    (hOriginal : ∀ p q x y, G (degree p q) (fiberValue p q x y) = value p q x y)
    (hInclusion : ∀ i z, lof R ι P i z = inclusion i z) :
    ∀ p q x y, L (source p q x y) = inclusion (degree p q) (value p q x y) := by
  intro p q x y
  have h₁ := hL (source p q x y)
  have h₂ := congrArg (DirectSum.lmap G) (hSource p q x y)
  simp only [DirectSum.lmap_lof] at h₂
  have h₃ := congrArg (lof R ι P (degree p q)) (hOriginal p q x y)
  exact h₁.trans (h₂.trans (h₃.trans (hInclusion _ _)))

/-- Compose the already chosen source and component equivalences, with no new inverse choice. -/
def equivAfterEquiv (E : A ≃ₗ[R] ⨁ i, F i) (e : ∀ i, F i ≃ₗ[R] P i) :
    A ≃ₗ[R] ⨁ i, P i :=
  E.trans (DirectSum.congrLinearEquiv e)

/-- The entire forward operator uses exactly those same given component maps. -/
theorem equivAfterEquiv_toLinearMap (E : A ≃ₗ[R] ⨁ i, F i) (e : ∀ i, F i ≃ₗ[R] P i) :
    (equivAfterEquiv E e).toLinearMap = mapAfterEquiv E (fun i => (e i).toLinearMap) := by
  change (DirectSum.congrLinearEquiv e).toLinearMap ∘ₗ E.toLinearMap = _
  rw [DirectSum.congrLinearEquiv_toLinearMap]
  rfl

/-- Whole forward identification with the given original maps, before specialization. -/
theorem equivAfterEquiv_toLinearMap_of (E : A ≃ₗ[R] ⨁ i, F i)
    (e : ∀ i, F i ≃ₗ[R] P i) (G : ∀ i, F i →ₗ[R] P i)
    (he : ∀ i, (e i).toLinearMap = G i) :
    (equivAfterEquiv E e).toLinearMap = mapAfterEquiv E G := by
  have h := equivAfterEquiv_toLinearMap E e
  have hFamily := funext he
  rw [hFamily] at h
  exact h

variable [DecidableEq ι]

/-- The inverse on a summand uses the same chosen E and same component inverse. -/
theorem equivAfterEquiv_symm_lof (E : A ≃ₗ[R] ⨁ i, F i) (e : ∀ i, F i ≃ₗ[R] P i)
    (i : ι) (z : P i) :
    (equivAfterEquiv E e).symm (lof R ι P i z) =
      E.symm (lof R ι F i ((e i).symm z)) := by
  apply (equivAfterEquiv E e).injective
  rw [LinearEquiv.apply_symm_apply]
  change lof R ι P i z = DirectSum.lmap (fun j => (e j).toLinearMap)
    (E (E.symm (lof R ι F i ((e i).symm z))))
  rw [LinearEquiv.apply_symm_apply, DirectSum.lmap_lof]
  exact congrArg (lof R ι P i) ((e i).apply_symm_apply z).symm

/-- The whole inverse-inclusion equation retains those same chosen operators. -/
theorem equivAfterEquiv_symm_comp_lof (E : A ≃ₗ[R] ⨁ i, F i)
    (e : ∀ i, F i ≃ₗ[R] P i) (i : ι) :
    (equivAfterEquiv E e).symm.toLinearMap ∘ₗ lof R ι P i =
      E.symm.toLinearMap ∘ₗ lof R ι F i ∘ₗ (e i).symm.toLinearMap := by
  ext z
  exact equivAfterEquiv_symm_lof E e i z

/-- Any whole support decomposition of the given source inverse passes to the full inverse. -/
theorem equivAfterEquiv_symm_support (E : A ≃ₗ[R] ⨁ i, F i)
    (e : ∀ i, F i ≃ₗ[R] P i) (i : ι) (Q₀ Q₁ : A →ₗ[R] A)
    (hE : (Q₀ ∘ₗ E.symm.toLinearMap ∘ₗ lof R ι F i) +
      (Q₁ ∘ₗ E.symm.toLinearMap ∘ₗ lof R ι F i) = E.symm.toLinearMap ∘ₗ lof R ι F i) :
    (Q₀ ∘ₗ (equivAfterEquiv E e).symm.toLinearMap ∘ₗ lof R ι P i) +
      (Q₁ ∘ₗ (equivAfterEquiv E e).symm.toLinearMap ∘ₗ lof R ι P i) =
      (equivAfterEquiv E e).symm.toLinearMap ∘ₗ lof R ι P i := by
  apply LinearMap.ext
  intro z
  have h := LinearMap.congr_fun hE ((e i).symm z)
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearEquiv.coe_coe] at h ⊢
  simp only [equivAfterEquiv_symm_lof]
  exact h

end ChosenOperators

section TensorFiber

universe i₁ i₂ j m n
variable {R : Type u} [CommSemiring R] {ι₁ : Type i₁} {ι₂ : Type i₂} {κ : Type j}
  [DecidableEq ι₁] [DecidableEq ι₂] [DecidableEq κ]
  (M : ι₁ → Type m) (N : ι₂ → Type n)
  [∀ p, AddCommMonoid (M p)] [∀ p, Module R (M p)]
  [∀ q, AddCommMonoid (N q)] [∀ q, Module R (N q)]

/-- The complete canonical tensor/fiber construction is shared before any realization. -/
def tensorFiberEquiv (f : ι₁ × ι₂ → κ) :
    ((⨁ p, M p) ⊗[R] ⨁ q, N q) ≃ₗ[R]
      ⨁ n, ⨁ s : {pq : ι₁ × ι₂ // f pq = n}, M s.val.1 ⊗[R] N s.val.2 :=
  (TensorProduct.directSum R R M N).trans (sigmaFiberLinearEquiv (R := R) f)

/-- Every original pure tensor retains its original index in the selected fiber. -/
theorem tensorFiberEquiv_lof_tmul_lof (f : ι₁ × ι₂ → κ)
    (p : ι₁) (q : ι₂) (x : M p) (y : N q) :
    tensorFiberEquiv (R := R) M N f (lof R ι₁ M p x ⊗ₜ[R] lof R ι₂ N q y) =
      lof R κ _ (f (p, q))
        (lof R {pq : ι₁ × ι₂ // f pq = f (p, q)}
          (fun s => M s.val.1 ⊗[R] N s.val.2) ⟨(p, q), rfl⟩ (x ⊗ₜ[R] y)) := by
  rw [tensorFiberEquiv, LinearEquiv.trans_apply, TensorProduct.directSum_lof_tmul_lof,
    sigmaFiberLinearEquiv_lof]

/-- The inverse retains the same actual index and two original inclusions. -/
theorem tensorFiberEquiv_symm_lof_tmul_lof (f : ι₁ × ι₂ → κ)
    (p : ι₁) (q : ι₂) (x : M p) (y : N q) :
    (tensorFiberEquiv (R := R) M N f).symm
        (lof R κ _ (f (p, q))
          (lof R {pq : ι₁ × ι₂ // f pq = f (p, q)}
            (fun s => M s.val.1 ⊗[R] N s.val.2) ⟨(p, q), rfl⟩ (x ⊗ₜ[R] y))) =
      lof R ι₁ M p x ⊗ₜ[R] lof R ι₂ N q y := by
  apply (tensorFiberEquiv (R := R) M N f).injective
  rw [LinearEquiv.apply_symm_apply, tensorFiberEquiv_lof_tmul_lof]

section Comparison

universe t
variable (f : ι₁ × ι₂ → κ) (P : κ → Type t)
  [∀ n, AddCommMonoid (P n)] [∀ n, Module R (P n)]
  (G : ∀ n, (⨁ s : {pq : ι₁ × ι₂ // f pq = n},
    M s.val.1 ⊗[R] N s.val.2) →ₗ[R] P n)

/-- The complete total operator uses the original fiber maps after canonical distribution. -/
def tensorFiberMap : ((⨁ p, M p) ⊗[R] ⨁ q, N q) →ₗ[R] ⨁ n, P n :=
  mapAfterEquiv (tensorFiberEquiv (R := R) M N f) G

/-- The whole total operator retains the original fiber and its original map on generators. -/
theorem tensorFiberMap_lof_tmul_lof (p : ι₁) (q : ι₂) (x : M p) (y : N q) :
    tensorFiberMap M N f P G (lof R ι₁ M p x ⊗ₜ[R] lof R ι₂ N q y) =
      lof R κ P (f (p, q))
        (G (f (p, q)) (lof R {pq : ι₁ × ι₂ // f pq = f (p, q)}
          (fun s => M s.val.1 ⊗[R] N s.val.2) ⟨(p, q), rfl⟩ (x ⊗ₜ[R] y))) := by
  rw [tensorFiberMap, mapAfterEquiv, LinearMap.comp_apply, LinearEquiv.coe_coe,
    tensorFiberEquiv_lof_tmul_lof, DirectSum.lmap_lof]

/-- Whole factorization on the same supplied total map, source comparison and fiber maps. -/
def TensorFiberMapFactorization
    (L : ((⨁ p, M p) ⊗[R] ⨁ q, N q) →ₗ[R] ⨁ n, P n)
    (s : ((⨁ p, M p) ⊗[R] ⨁ q, N q) ≃ₗ[R]
      ⨁ n, ⨁ t : {pq : ι₁ × ι₂ // f pq = n}, M t.val.1 ⊗[R] N t.val.2) : Prop :=
  MapFactorization L s G

/-- A regular whole value-family equation on the same actual total map. -/
def TensorFiberHomogeneousEq
    (L : ((⨁ p, M p) ⊗[R] ⨁ q, N q) →ₗ[R] ⨁ n, P n)
    (e : ∀ p q, M p →ₗ[R] N q →ₗ[R] P (f (p, q))) : Prop :=
  ∀ p q (x : M p) (y : N q),
    L (lof R ι₁ M p x ⊗ₜ[R] lof R ι₂ N q y) = lof R κ P (f (p, q)) (e p q x y)

/-- The actual operator's family follows before any concrete realization is supplied. -/
theorem TensorFiberMapFactorization.homogeneous
    {L : ((⨁ p, M p) ⊗[R] ⨁ q, N q) →ₗ[R] ⨁ n, P n}
    {s : ((⨁ p, M p) ⊗[R] ⨁ q, N q) ≃ₗ[R]
      ⨁ n, ⨁ t : {pq : ι₁ × ι₂ // f pq = n}, M t.val.1 ⊗[R] N t.val.2}
    (hL : TensorFiberMapFactorization M N f P G L s)
    (e : ∀ p q, M p →ₗ[R] N q →ₗ[R] P (f (p, q)))
    (T : ∀ p q, M p ⊗[R] N q →ₗ[R] P (f (p, q)))
    (hs : ∀ p q (x : M p) (y : N q),
      s (lof R ι₁ M p x ⊗ₜ[R] lof R ι₂ N q y) =
        lof R κ _ (f (p, q))
          (lof R {pq : ι₁ × ι₂ // f pq = f (p, q)}
            (fun t => M t.val.1 ⊗[R] N t.val.2) ⟨(p, q), rfl⟩ (x ⊗ₜ[R] y)))
    (hG : ∀ p q (z : M p ⊗[R] N q),
      G (f (p, q)) (lof R {pq : ι₁ × ι₂ // f pq = f (p, q)}
        (fun t => M t.val.1 ⊗[R] N t.val.2) ⟨(p, q), rfl⟩ z) = T p q z)
    (hT : ∀ p q (x : M p) (y : N q), T p q (x ⊗ₜ[R] y) = e p q x y) :
    TensorFiberHomogeneousEq M N f P L e := by
  intro p q x y
  have h₁ := hL (lof R ι₁ M p x ⊗ₜ[R] lof R ι₂ N q y)
  have h₂ := congrArg (DirectSum.lmap G) (hs p q x y)
  simp only [DirectSum.lmap_lof] at h₂
  have h₃ := congrArg (lof R κ P (f (p, q))) (hG p q (x ⊗ₜ[R] y))
  have h₄ := congrArg (lof R κ P (f (p, q))) (hT p q x y)
  exact h₁.trans (h₂.trans (h₃.trans h₄))

variable (hG : ∀ n, Function.Bijective (G n))

/-- The original fiber map has its one inverse, from the given proof of bijectivity. -/
def tensorFiberDegreeEquiv (n : κ) :
    (⨁ s : {pq : ι₁ × ι₂ // f pq = n}, M s.val.1 ⊗[R] N s.val.2) ≃ₗ[R] P n :=
  LinearEquiv.ofBijective (G n) (hG n)

/-- The complete canonical comparison and its inverse are constructed over variable families. -/
def tensorFiberComparison : ((⨁ p, M p) ⊗[R] ⨁ q, N q) ≃ₗ[R] ⨁ n, P n :=
  equivAfterEquiv (tensorFiberEquiv (R := R) M N f)
    (tensorFiberDegreeEquiv M N f P G hG)

/-- The complete comparison has exactly the original total forward operator. -/
theorem tensorFiberComparison_toLinearMap :
    (tensorFiberComparison M N f P G hG).toLinearMap = tensorFiberMap M N f P G := by
  change (DirectSum.congrLinearEquiv (tensorFiberDegreeEquiv M N f P G hG)).toLinearMap ∘ₗ
    (tensorFiberEquiv (R := R) M N f).toLinearMap = _
  rw [DirectSum.congrLinearEquiv_toLinearMap]
  rfl

/-- Its inverse on a homogeneous element uses that same original fiber inverse. -/
theorem tensorFiberComparison_symm_lof (n : κ) (z : P n) :
    (tensorFiberComparison M N f P G hG).symm (lof R κ P n z) =
      (tensorFiberEquiv (R := R) M N f).symm
        (lof R κ _ n ((tensorFiberDegreeEquiv M N f P G hG n).symm z)) := by
  apply (tensorFiberComparison M N f P G hG).injective
  rw [LinearEquiv.apply_symm_apply]
  change lof R κ P n z = DirectSum.lmap G
    (tensorFiberEquiv (R := R) M N f
      ((tensorFiberEquiv (R := R) M N f).symm
        (lof R κ _ n ((tensorFiberDegreeEquiv M N f P G hG n).symm z))))
  rw [LinearEquiv.apply_symm_apply, DirectSum.lmap_lof]
  exact congrArg (lof R κ P n)
    ((tensorFiberDegreeEquiv M N f P G hG n).apply_symm_apply z).symm

/-- The entire inverse-inclusion equation precedes evaluation in any realization. -/
theorem tensorFiberComparison_symm_comp_lof (n : κ) :
    (tensorFiberComparison M N f P G hG).symm.toLinearMap ∘ₗ lof R κ P n =
      (tensorFiberEquiv (R := R) M N f).symm.toLinearMap ∘ₗ lof R κ _ n ∘ₗ
        (tensorFiberDegreeEquiv M N f P G hG n).symm.toLinearMap := by
  ext z
  exact tensorFiberComparison_symm_lof M N f P G hG n z

end Comparison

end TensorFiber

section TensorTotal

universe m n p
variable {R : Type u} [CommSemiring R]
  (M : ℕ → Type m) (N : ℕ → Type n)
  [∀ p, AddCommMonoid (M p)] [∀ p, Module R (M p)]
  [∀ q, AddCommMonoid (N q)] [∀ q, Module R (N q)]

/-- Distribute the original tensor and regroup its original pairs by total degree. -/
def tensorTotalEquiv :
    ((⨁ p, M p) ⊗[R] ⨁ q, N q) ≃ₗ[R]
      ⨁ n, ⨁ s : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, M s.val.1 ⊗[R] N s.val.2 :=
  tensorFiberEquiv (R := R) M N (fun pq : ℕ × ℕ => pq.1 + pq.2)

/-- The canonical total reindexing sends the original homogeneous pure tensor to its pair. -/
theorem tensorTotalEquiv_lof_tmul_lof (p q : ℕ) (x : M p) (y : N q) :
    tensorTotalEquiv (R := R) M N (lof R ℕ M p x ⊗ₜ[R] lof R ℕ N q y) =
      lof R ℕ _ (p + q) (lof R {pq : ℕ × ℕ // pq.1 + pq.2 = p + q}
          (fun s => M s.val.1 ⊗[R] N s.val.2) ⟨(p, q), rfl⟩ (x ⊗ₜ[R] y)) := by
  exact tensorFiberEquiv_lof_tmul_lof (R := R) M N
    (fun pq : ℕ × ℕ => pq.1 + pq.2) p q x y

/-- The inverse retains the same original pair and two original summand inclusions. -/
theorem tensorTotalEquiv_symm_lof_tmul_lof (p q : ℕ) (x : M p) (y : N q) :
    (tensorTotalEquiv (R := R) M N).symm
        (lof R ℕ _ (p + q) (lof R {pq : ℕ × ℕ // pq.1 + pq.2 = p + q}
          (fun s => M s.val.1 ⊗[R] N s.val.2) ⟨(p, q), rfl⟩ (x ⊗ₜ[R] y))) =
      lof R ℕ M p x ⊗ₜ[R] lof R ℕ N q y := by
  apply (tensorTotalEquiv (R := R) M N).injective
  rw [LinearEquiv.apply_symm_apply, tensorTotalEquiv_lof_tmul_lof]

/-- Whole linear maps on the original tensor are determined by original homogeneous tensors. -/
theorem tensorDirectSum_ext {T : Type p} [AddCommMonoid T] [Module R T]
    {F G : ((⨁ p, M p) ⊗[R] ⨁ q, N q) →ₗ[R] T}
    (h : ∀ p q (x : M p) (y : N q),
      F (lof R ℕ M p x ⊗ₜ[R] lof R ℕ N q y) =
        G (lof R ℕ M p x ⊗ₜ[R] lof R ℕ N q y)) : F = G := by
  apply TensorProduct.ext
  apply DirectSum.linearMap_ext
  intro p
  apply LinearMap.ext
  intro x
  apply DirectSum.linearMap_ext
  intro q
  apply LinearMap.ext
  intro y
  exact h p q x y

/-- Whole underlying-linear comparison with the direct sum of the original degree maps. -/
theorem tensorTotalLinearMap_eq
    (P : ℕ → Type p) [∀ n, AddCommMonoid (P n)] [∀ n, Module R (P n)]
    (F : ((⨁ p, M p) ⊗[R] ⨁ q, N q) →ₗ[R] ⨁ n, P n)
    (G : ∀ n, (⨁ s : {pq : ℕ × ℕ // pq.1 + pq.2 = n},
      M s.val.1 ⊗[R] N s.val.2) →ₗ[R] P n)
    (h : ∀ p q (x : M p) (y : N q),
      F (lof R ℕ M p x ⊗ₜ[R] lof R ℕ N q y) =
        lof R ℕ P (p + q) (G (p + q) (lof R {pq : ℕ × ℕ // pq.1 + pq.2 = p + q}
          (fun s => M s.val.1 ⊗[R] N s.val.2) ⟨(p, q), rfl⟩ (x ⊗ₜ[R] y)))) :
    F = DirectSum.lmap G ∘ₗ (tensorTotalEquiv (R := R) M N).toLinearMap := by
  apply tensorDirectSum_ext M N
  intro p q x y
  change F (lof R ℕ M p x ⊗ₜ[R] lof R ℕ N q y) =
    DirectSum.lmap G (tensorTotalEquiv (R := R) M N
      (lof R ℕ M p x ⊗ₜ[R] lof R ℕ N q y))
  rw [tensorTotalEquiv_lof_tmul_lof, DirectSum.lmap_lof]
  exact h p q x y

/-- The inverse of total degree one has only its two original possible bidegrees. -/
theorem tensorTotalEquiv_symm_degreeOne :
    (TensorProduct.map
        (lof R ℕ M 0 ∘ₗ DFinsupp.lapply 0) (lof R ℕ N 1 ∘ₗ DFinsupp.lapply 1) ∘ₗ
      (tensorTotalEquiv (R := R) M N).symm.toLinearMap ∘ₗ lof R ℕ _ 1) +
      (TensorProduct.map
        (lof R ℕ M 1 ∘ₗ DFinsupp.lapply 1) (lof R ℕ N 0 ∘ₗ DFinsupp.lapply 0) ∘ₗ
      (tensorTotalEquiv (R := R) M N).symm.toLinearMap ∘ₗ lof R ℕ _ 1) =
      (tensorTotalEquiv (R := R) M N).symm.toLinearMap ∘ₗ lof R ℕ _ 1 := by
  apply DirectSum.linearMap_ext R
  intro s
  apply TensorProduct.ext'
  intro x y
  rcases s with ⟨⟨p, q⟩, hpq⟩
  have hpq' : (p = 0 ∧ q = 1) ∨ (p = 1 ∧ q = 0) := by
    cases p with
    | zero => exact Or.inl ⟨rfl, by simpa only [Nat.zero_add] using hpq⟩
    | succ p =>
      have hzero : p + q = 0 := Nat.succ.inj (by simpa only [Nat.succ_add] using hpq)
      obtain ⟨hp, hq⟩ := Nat.add_eq_zero_iff.mp hzero
      exact Or.inr ⟨by simp only [hp], hq⟩
  rcases hpq' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
    change (lof R ℕ M 0 ((of M 0 x) 0) ⊗ₜ[R] lof R ℕ N 1 ((of N 1 y) 1)) +
      (lof R ℕ M 1 ((of M 0 x) 1) ⊗ₜ[R] lof R ℕ N 0 ((of N 1 y) 0)) = _
    rw [of_eq_same, of_eq_same, of_eq_of_ne 0 1 x (by decide),
      of_eq_of_ne 1 0 y (by decide), map_zero, map_zero,
      TensorProduct.zero_tmul, add_zero]
    exact (tensorTotalEquiv_symm_lof_tmul_lof M N 0 1 x y).symm
  · simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
    change (lof R ℕ M 0 ((of M 1 x) 0) ⊗ₜ[R] lof R ℕ N 1 ((of N 0 y) 1)) +
      (lof R ℕ M 1 ((of M 1 x) 1) ⊗ₜ[R] lof R ℕ N 0 ((of N 0 y) 0)) = _
    rw [of_eq_of_ne 1 0 x (by decide), of_eq_of_ne 0 1 y (by decide),
      of_eq_same, of_eq_same, map_zero, map_zero,
      TensorProduct.zero_tmul, zero_add]
    exact (tensorTotalEquiv_symm_lof_tmul_lof M N 1 0 x y).symm


/-- A whole equality with the original total-degree map gives the degree-one projection law. -/
theorem tensorFiberEquiv_symm_degreeOne (f : ℕ × ℕ → ℕ)
    (hf : f = fun pq => pq.1 + pq.2) :
    (TensorProduct.map
        (lof R ℕ M 0 ∘ₗ DFinsupp.lapply 0) (lof R ℕ N 1 ∘ₗ DFinsupp.lapply 1) ∘ₗ
      (tensorFiberEquiv (R := R) M N f).symm.toLinearMap ∘ₗ lof R ℕ _ 1) +
      (TensorProduct.map
        (lof R ℕ M 1 ∘ₗ DFinsupp.lapply 1) (lof R ℕ N 0 ∘ₗ DFinsupp.lapply 0) ∘ₗ
      (tensorFiberEquiv (R := R) M N f).symm.toLinearMap ∘ₗ lof R ℕ _ 1) =
      (tensorFiberEquiv (R := R) M N f).symm.toLinearMap ∘ₗ lof R ℕ _ 1 := by
  subst f
  exact tensorTotalEquiv_symm_degreeOne M N

/-- The complete comparison inverse in degree one has only the original two bidegrees. -/
theorem tensorFiberComparison_symm_degreeOne
    (f : ℕ × ℕ → ℕ) (hf : f = fun pq => pq.1 + pq.2)
    (P : ℕ → Type p) [∀ n, AddCommMonoid (P n)] [∀ n, Module R (P n)]
    (G : ∀ n, (⨁ s : {pq : ℕ × ℕ // f pq = n},
      M s.val.1 ⊗[R] N s.val.2) →ₗ[R] P n)
    (hG : ∀ n, Function.Bijective (G n)) :
    (TensorProduct.map
        (lof R ℕ M 0 ∘ₗ DFinsupp.lapply 0) (lof R ℕ N 1 ∘ₗ DFinsupp.lapply 1) ∘ₗ
      (tensorFiberComparison M N f P G hG).symm.toLinearMap ∘ₗ lof R ℕ P 1) +
      (TensorProduct.map
        (lof R ℕ M 1 ∘ₗ DFinsupp.lapply 1) (lof R ℕ N 0 ∘ₗ DFinsupp.lapply 0) ∘ₗ
      (tensorFiberComparison M N f P G hG).symm.toLinearMap ∘ₗ lof R ℕ P 1) =
      (tensorFiberComparison M N f P G hG).symm.toLinearMap ∘ₗ lof R ℕ P 1 := by
  apply LinearMap.ext
  intro z
  have h := LinearMap.congr_fun (tensorFiberEquiv_symm_degreeOne M N f hf)
    ((tensorFiberDegreeEquiv M N f P G hG 1).symm z)
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearEquiv.coe_coe] at h ⊢
  simp only [tensorFiberComparison_symm_lof]
  exact h

end TensorTotal

end DirectSum
