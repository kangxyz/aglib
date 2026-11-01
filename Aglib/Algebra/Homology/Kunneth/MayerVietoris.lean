/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.TotalComplex.FirstQuadrant
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.RingTheory.Flat.Basic

/-!
# Exact finite antidiagonals for the Künneth Mayer–Vietoris sequence

The maps are the original coordinate tensor maps. The connecting map shifts
only the second degree and multiplies its degree-p summand by (-1)^p. Flat
first factors preserve the original exact rows. The missing second-degree
zero boundary coordinate is handled by injectivity of the original degree-zero
restriction map, without negative cohomology or an auxiliary exactness datum.
-/

@[expose] public noncomputable section

open scoped DirectSum TensorProduct

universe r i j a b c m

namespace DirectSum

variable {R : Type r} [CommRing R]
  {ι : Type i} {κ : Type j}

/-- The original coproduct inclusion along an embedding of its original indices. -/
def embeddingLinearMap (M : κ → Type a) [∀ k, AddCommGroup (M k)] [∀ k, Module R (M k)]
    (e : ι ↪ κ) : (⨁ i, M (e i)) →ₗ[R] ⨁ k, M k := by
  classical
  exact toModule R _ _ (fun i => lof R _ _ (e i))

/-- Projection back to the original embedded coordinates. -/
def embeddingProjection (M : κ → Type a) [∀ k, AddCommGroup (M k)] [∀ k, Module R (M k)]
    (e : ι ↪ κ) : (⨁ k, M k) →ₗ[R] ⨁ i, M (e i) where
  toFun := DFinsupp.comapDomain e e.injective
  map_add' := DFinsupp.comapDomain_add e e.injective
  map_smul' := DFinsupp.comapDomain_smul e e.injective

@[simp]
theorem embeddingLinearMap_apply (M : κ → Type a)
    [∀ k, AddCommGroup (M k)] [∀ k, Module R (M k)] (e : ι ↪ κ)
    (x : ⨁ i, M (e i)) (i : ι) : embeddingLinearMap (R := R) M e x (e i) = x i := by
  classical
  have h : (component R κ M (e i)).comp (embeddingLinearMap (R := R) M e) =
      component R ι (fun i => M (e i)) i := by
    apply linearMap_ext
    intro j
    apply LinearMap.ext
    intro a
    simp only [LinearMap.comp_apply, embeddingLinearMap, toModule_lof]
    by_cases hji : j = i
    · subst j
      simp
    · have hji' : e j ≠ e i := fun h => hji (e.injective h)
      simp only [component.of, dite_eq_right hji, dite_eq_right hji']
  exact LinearMap.congr_fun h x

@[simp]
theorem embeddingLinearMap_apply_off (M : κ → Type a)
    [∀ k, AddCommGroup (M k)] [∀ k, Module R (M k)] (e : ι ↪ κ)
    (x : ⨁ i, M (e i)) (k : κ) (hk : k ∉ Set.range e) :
    embeddingLinearMap (R := R) M e x k = 0 := by
  classical
  have h : (component R κ M k).comp (embeddingLinearMap (R := R) M e) = 0 := by
    apply linearMap_ext
    intro i
    apply LinearMap.ext
    intro a
    have hi : e i ≠ k := fun h => hk ⟨i, h⟩
    simp only [LinearMap.comp_apply, embeddingLinearMap, toModule_lof,
      component.of, dite_eq_right hi, LinearMap.zero_apply]
  exact LinearMap.congr_fun h x

/-- Each original coproduct generator keeps its original value under the embedding. -/
private theorem embeddingLinearMap_lof [DecidableEq ι] [DecidableEq κ] (M : κ → Type a)
    [∀ k, AddCommGroup (M k)] [∀ k, Module R (M k)] (e : ι ↪ κ)
    (i : ι) (x : M (e i)) :
    embeddingLinearMap (R := R) M e (lof R ι (fun i => M (e i)) i x) =
      lof R κ M (e i) x := by
  classical
  apply DFinsupp.ext
  intro k
  by_cases hk : k ∈ Set.range e
  · obtain ⟨j, rfl⟩ := hk
    rw [embeddingLinearMap_apply]
    by_cases hj : j = i
    · subst j
      simp only [lof_apply]
    · have hi : i ≠ j := Ne.symm hj
      have hij : e i ≠ e j := fun h => hi (e.injective h)
      change (component R ι (fun l => M (e l)) j) (lof R ι (fun l => M (e l)) i x) =
        (component R κ M (e j)) (lof R κ M (e i) x)
      simp only [component.of, dite_eq_right hi, dite_eq_right hij]
  · rw [embeddingLinearMap_apply_off M e _ k hk]
    have hi : e i ≠ k := fun h => hk ⟨i, h⟩
    change 0 = (component R κ M k) (lof R κ M (e i) x)
    simp only [component.of, dite_eq_right hi]

/-- Inclusion has no kernel on the original coordinates. -/
theorem embeddingLinearMap_injective (M : κ → Type a)
    [∀ k, AddCommGroup (M k)] [∀ k, Module R (M k)] (e : ι ↪ κ) :
    Function.Injective (embeddingLinearMap (R := R) M e) := by
  intro x y h
  apply DFinsupp.ext
  intro i
  simpa only [embeddingLinearMap_apply] using congrArg (fun z => z (e i)) h

/-- A vector supported on the embedded indices is reconstructed by its actual projection. -/
theorem embeddingLinearMap_projection (M : κ → Type a)
    [∀ k, AddCommGroup (M k)] [∀ k, Module R (M k)] (e : ι ↪ κ)
    (x : ⨁ k, M k) (hx : ∀ k, k ∉ Set.range e → x k = 0) :
    embeddingLinearMap (R := R) M e (embeddingProjection (R := R) M e x) = x := by
  classical
  apply DFinsupp.ext
  intro k
  by_cases hk : k ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hk
    rw [embeddingLinearMap_apply]
    rfl
  · rw [embeddingLinearMap_apply_off M e _ k hk, hx k hk]

/-- A whole coordinate map commutes with the original coproduct embedding. -/
theorem lmap_comp_embeddingLinearMap
    {M : κ → Type a} {N : κ → Type b}
    [∀ k, AddCommGroup (M k)] [∀ k, Module R (M k)]
    [∀ k, AddCommGroup (N k)] [∀ k, Module R (N k)]
    (e : ι ↪ κ) (f : ∀ k, M k →ₗ[R] N k) :
    (lmap f).comp (embeddingLinearMap (R := R) M e) =
      (embeddingLinearMap (R := R) N e).comp (lmap (fun i => f (e i))) := by
  classical
  apply linearMap_ext
  intro i
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, embeddingLinearMap, toModule_lof, lmap_lof]

/-- Coordinatewise exactness gives exactness of the original direct-sum maps. -/
theorem exact_lmap
    {L : ι → Type a} {M : ι → Type b} {N : ι → Type c}
    [∀ i, AddCommGroup (L i)] [∀ i, Module R (L i)]
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
    (f : ∀ i, L i →ₗ[R] M i) (g : ∀ i, M i →ₗ[R] N i)
    (h : ∀ i, Function.Exact (f i) (g i)) : Function.Exact (lmap f) (lmap g) := by
  rw [LinearMap.exact_iff, ker_lmap, range_lmap]
  congr 2
  funext i
  exact LinearMap.exact_iff.mp (h i)

/-- Exactness after an index embedding only requires injectivity at the missing indices. -/
theorem exact_embedding_lmap
    {L : ι → Type a} {M : κ → Type b} {N : κ → Type c}
    [∀ i, AddCommGroup (L i)] [∀ i, Module R (L i)]
    [∀ k, AddCommGroup (M k)] [∀ k, Module R (M k)]
    [∀ k, AddCommGroup (N k)] [∀ k, Module R (N k)]
    (e : ι ↪ κ) (f : ∀ i, L i →ₗ[R] M (e i)) (g : ∀ k, M k →ₗ[R] N k)
    (h : ∀ i, Function.Exact (f i) (g (e i)))
    (hzero : ∀ k, k ∉ Set.range e → Function.Injective (g k)) :
    Function.Exact ((embeddingLinearMap (R := R) M e).comp (lmap f)) (lmap g) := by
  classical
  have hex := exact_lmap f (fun i => g (e i)) h
  intro y
  constructor
  · intro hy
    have hys : ∀ k, k ∉ Set.range e → y k = 0 := by
      intro k hk
      apply hzero k hk
      simpa only [map_zero, lmap_apply, DFinsupp.zero_apply] using
        congrArg (fun z => z k) hy
    have hyp : lmap (fun i => g (e i)) (embeddingProjection (R := R) M e y) = 0 := by
      apply DFinsupp.ext
      intro i
      change g (e i) (y (e i)) = 0
      simpa only [lmap_apply, DFinsupp.zero_apply] using congrArg (fun z => z (e i)) hy
    obtain ⟨x, hx⟩ := (hex _).mp hyp
    refine ⟨x, ?_⟩
    change embeddingLinearMap (R := R) M e (lmap f x) = y
    rw [hx, embeddingLinearMap_projection M e y hys]
  · rintro ⟨x, rfl⟩
    change ((lmap g).comp ((embeddingLinearMap (R := R) M e).comp (lmap f))) x = 0
    rw [← LinearMap.comp_assoc, lmap_comp_embeddingLinearMap, LinearMap.comp_assoc]
    change embeddingLinearMap (R := R) N e (lmap (fun i => g (e i)) (lmap f x)) = 0
    rw [(hex _).mpr ⟨x, rfl⟩, map_zero]

end DirectSum

namespace Kunneth.MayerVietoris

variable {R : Type r} [CommRing R]

/-- Koszul multiplication is its own inverse in every characteristic. -/
theorem koszul_smul_smul {M : Type a} [AddCommGroup M] [Module R M] (p : ℕ) (x : M) :
    ((-1 : R) ^ p) • (((-1 : R) ^ p) • x) = x := by
  rw [smul_smul, ← mul_pow]
  simp

/-- The Koszul factor does not change a kernel. -/
theorem koszul_smul_eq_zero_iff {M : Type a} [AddCommGroup M] [Module R M]
    (p : ℕ) (x : M) : ((-1 : R) ^ p) • x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have h' := congrArg (fun z => ((-1 : R) ^ p) • z) h
    simpa only [koszul_smul_smul, smul_zero] using h'
  · rintro rfl
    exact smul_zero _

/-- Multiplying the second map by its Koszul unit preserves exactness. -/
theorem exact_koszul_right {L : Type a} {M : Type b} {N : Type c}
    [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (p : ℕ) (f : L →ₗ[R] M) (g : M →ₗ[R] N)
    (h : Function.Exact f g) : Function.Exact f (((-1 : R) ^ p) • g) := by
  intro x
  change ((-1 : R) ^ p) • g x = 0 ↔ _
  rw [koszul_smul_eq_zero_iff]
  exact h x

/-- Multiplying the first map by its Koszul unit preserves exactness. -/
theorem exact_koszul_left {L : Type a} {M : Type b} {N : Type c}
    [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (p : ℕ) (f : L →ₗ[R] M) (g : M →ₗ[R] N)
    (h : Function.Exact f g) : Function.Exact (((-1 : R) ^ p) • f) g := by
  intro y
  constructor
  · intro hy
    obtain ⟨x, hx⟩ := (h y).mp hy
    refine ⟨((-1 : R) ^ p) • x, ?_⟩
    simpa only [LinearMap.smul_apply, map_smul, koszul_smul_smul] using hx
  · rintro ⟨x, rfl⟩
    change g (((-1 : R) ^ p) • f x) = 0
    rw [map_smul, (h _).mpr ⟨x, rfl⟩, smul_zero]

/-- Shift precisely the second coordinate of the native finite antidiagonal. -/
def rightSuccessor (n : ℕ) : HomologicalComplex₂.TotalDegree n ↪
    HomologicalComplex₂.TotalDegree (n + 1) where
  toFun s := ⟨(s.val.1, s.val.2 + 1), by
    have hs : s.val.1 + s.val.2 = n := s.property
    change s.val.1 + (s.val.2 + 1) = n + 1
    omega⟩
  inj' := by
    intro s t h
    apply Subtype.ext
    have h₁ := congrArg (fun z => z.val.1) h
    have h₂ := congrArg (fun z => z.val.2) h
    apply Prod.ext
    · exact h₁
    · change s.val.2 + 1 = t.val.2 + 1 at h₂
      omega

/-- The only missing coordinate is second degree zero. -/
theorem mem_range_rightSuccessor (n : ℕ) (t : HomologicalComplex₂.TotalDegree (n + 1)) :
    t ∈ Set.range (rightSuccessor n) ↔ 0 < t.val.2 := by
  constructor
  · rintro ⟨s, rfl⟩
    exact Nat.zero_lt_succ _
  · intro ht
    refine ⟨⟨(t.val.1, t.val.2 - 1), ?_⟩, ?_⟩
    · have h : t.val.1 + t.val.2 = n + 1 := t.property
      change t.val.1 + (t.val.2 - 1) = n
      omega
    · apply Subtype.ext
      apply Prod.ext
      · rfl
      · change t.val.2 - 1 + 1 = t.val.2
        omega

variable (M : ℕ → Type m) [∀ p, AddCommGroup (M p)] [∀ p, Module R (M p)]

/-- The original finite-antidiagonal tensor source. -/
abbrev tensorSum (A : ℕ → Type a) [∀ q, AddCommGroup (A q)] [∀ q, Module R (A q)] (n : ℕ) :=
  ⨁ s : HomologicalComplex₂.TotalDegree n, M s.val.1 ⊗[R] A s.val.2

/-- The original coordinate tensor map in a fixed total degree. -/
def tensorMap {A : ℕ → Type a} {B : ℕ → Type b}
    [∀ q, AddCommGroup (A q)] [∀ q, Module R (A q)]
    [∀ q, AddCommGroup (B q)] [∀ q, Module R (B q)]
    (f : ∀ q, A q →ₗ[R] B q) (n : ℕ) : tensorSum (R := R) M A n →ₗ[R] tensorSum (R := R) M B n :=
  DirectSum.lmap (fun s => (f s.val.2).lTensor (M s.val.1))

/-- The actual boundary shifts q to q+1 and uses the degree-p Koszul unit. -/
def tensorBoundary {A : ℕ → Type a} {B : ℕ → Type b}
    [∀ q, AddCommGroup (A q)] [∀ q, Module R (A q)]
    [∀ q, AddCommGroup (B q)] [∀ q, Module R (B q)]
    (δ : ∀ q, A q →ₗ[R] B (q + 1)) (n : ℕ) :
    tensorSum (R := R) M A n →ₗ[R] tensorSum (R := R) M B (n + 1) :=
  (DirectSum.embeddingLinearMap (R := R)
    (fun t : HomologicalComplex₂.TotalDegree (n + 1) => M t.val.1 ⊗[R] B t.val.2)
    (rightSuccessor n)).comp
      (DirectSum.lmap (fun s : HomologicalComplex₂.TotalDegree n =>
        ((-1 : R) ^ s.val.1) • (δ s.val.2).lTensor (M s.val.1)))

/-- Every native antidiagonal injection retains the original coordinate tensor map. -/
@[simp]
theorem tensorMap_lof {A : ℕ → Type a} {B : ℕ → Type b}
    [∀ q, AddCommGroup (A q)] [∀ q, Module R (A q)]
    [∀ q, AddCommGroup (B q)] [∀ q, Module R (B q)]
    (f : ∀ q, A q →ₗ[R] B q) (n : ℕ) (s : HomologicalComplex₂.TotalDegree n)
    (x : M s.val.1 ⊗[R] A s.val.2) :
    tensorMap (R := R) M f n (DirectSum.lof R _ _ s x) =
      DirectSum.lof R _ _ s ((f s.val.2).lTensor (M s.val.1) x) := by
  classical
  exact DirectSum.lmap_lof
    (fun t : HomologicalComplex₂.TotalDegree n => (f t.val.2).lTensor (M t.val.1)) s x

/-- Every boundary summand has the literal original shifted tensor value and Koszul sign. -/
@[simp]
theorem tensorBoundary_lof {A : ℕ → Type a} {B : ℕ → Type b}
    [∀ q, AddCommGroup (A q)] [∀ q, Module R (A q)]
    [∀ q, AddCommGroup (B q)] [∀ q, Module R (B q)]
    (δ : ∀ q, A q →ₗ[R] B (q + 1)) (n : ℕ) (s : HomologicalComplex₂.TotalDegree n)
    (x : M s.val.1 ⊗[R] A s.val.2) :
    tensorBoundary (R := R) M δ n (DirectSum.lof R _ _ s x) =
      DirectSum.lof R _ _ (rightSuccessor n s)
        (((-1 : R) ^ s.val.1) • (δ s.val.2).lTensor (M s.val.1) x) := by
  classical
  let f (t : HomologicalComplex₂.TotalDegree n) :
      M t.val.1 ⊗[R] A t.val.2 →ₗ[R] M t.val.1 ⊗[R] B (t.val.2 + 1) :=
    ((-1 : R) ^ t.val.1) • (δ t.val.2).lTensor (M t.val.1)
  have hMap := DirectSum.lmap_lof f s x
  have hEmbed := DirectSum.embeddingLinearMap_lof (R := R)
    (fun t : HomologicalComplex₂.TotalDegree (n + 1) => M t.val.1 ⊗[R] B t.val.2)
    (rightSuccessor n) s (f s x)
  have hFinal := (congrArg (DirectSum.embeddingLinearMap (R := R)
    (fun t : HomologicalComplex₂.TotalDegree (n + 1) => M t.val.1 ⊗[R] B t.val.2)
    (rightSuccessor n)) hMap).trans hEmbed
  exact hFinal

/-- The degree-zero total restriction is injective from its original degree-zero coordinate. -/
theorem tensorMap_zero_injective [∀ p, Module.Flat R (M p)]
    {A : ℕ → Type a} {B : ℕ → Type b}
    [∀ q, AddCommGroup (A q)] [∀ q, Module R (A q)]
    [∀ q, AddCommGroup (B q)] [∀ q, Module R (B q)]
    (f : ∀ q, A q →ₗ[R] B q) (hzero : Function.Injective (f 0)) :
    Function.Injective (tensorMap (R := R) M f 0) := by
  apply (DirectSum.lmap_injective _).mpr
  intro s
  have hs : s.val.1 + s.val.2 = 0 := s.property
  have hq : s.val.2 = 0 := by omega
  change Function.Injective ((f s.val.2).lTensor (M s.val.1))
  rw [hq]
  exact Module.Flat.lTensor_preserves_injective_linearMap _ hzero

/-- Flat first factors preserve each exact finite antidiagonal. -/
theorem tensorMap_exact [∀ p, Module.Flat R (M p)]
    {A : ℕ → Type a} {B : ℕ → Type b} {C : ℕ → Type c}
    [∀ q, AddCommGroup (A q)] [∀ q, Module R (A q)]
    [∀ q, AddCommGroup (B q)] [∀ q, Module R (B q)]
    [∀ q, AddCommGroup (C q)] [∀ q, Module R (C q)]
    (f : ∀ q, A q →ₗ[R] B q) (g : ∀ q, B q →ₗ[R] C q)
    (h : ∀ q, Function.Exact (f q) (g q)) (n : ℕ) :
    Function.Exact (tensorMap (R := R) M f n) (tensorMap (R := R) M g n) :=
  DirectSum.exact_lmap _ _ (fun s => Module.Flat.lTensor_exact (M s.val.1) (h s.val.2))

/-- The kernel of the shifted signed boundary is the original restriction image. -/
theorem tensorMap_tensorBoundary_exact [∀ p, Module.Flat R (M p)]
    {A : ℕ → Type a} {B : ℕ → Type b} {C : ℕ → Type c}
    [∀ q, AddCommGroup (A q)] [∀ q, Module R (A q)]
    [∀ q, AddCommGroup (B q)] [∀ q, Module R (B q)]
    [∀ q, AddCommGroup (C q)] [∀ q, Module R (C q)]
    (f : ∀ q, A q →ₗ[R] B q) (δ : ∀ q, B q →ₗ[R] C (q + 1))
    (h : ∀ q, Function.Exact (f q) (δ q)) (n : ℕ) :
    Function.Exact (tensorMap (R := R) M f n) (tensorBoundary (R := R) M δ n) := by
  let d : tensorSum (R := R) M B n →ₗ[R]
      ⨁ s : HomologicalComplex₂.TotalDegree n, M s.val.1 ⊗[R] C (s.val.2 + 1) :=
    DirectSum.lmap (fun s : HomologicalComplex₂.TotalDegree n =>
      ((-1 : R) ^ s.val.1) • (δ s.val.2).lTensor (M s.val.1))
  let E : (⨁ s : HomologicalComplex₂.TotalDegree n, M s.val.1 ⊗[R] C (s.val.2 + 1)) →ₗ[R]
      tensorSum (R := R) M C (n + 1) :=
    DirectSum.embeddingLinearMap (R := R)
      (fun t : HomologicalComplex₂.TotalDegree (n + 1) => M t.val.1 ⊗[R] C t.val.2)
      (rightSuccessor n)
  have hNative := DirectSum.exact_lmap
    (fun s : HomologicalComplex₂.TotalDegree n => (f s.val.2).lTensor (M s.val.1))
    (fun s : HomologicalComplex₂.TotalDegree n =>
      ((-1 : R) ^ s.val.1) • (δ s.val.2).lTensor (M s.val.1))
    (fun s => exact_koszul_right s.val.1 _ _
      (Module.Flat.lTensor_exact (M s.val.1) (h s.val.2)))
  have hex : Function.Exact (tensorMap (R := R) M f n) d := hNative
  have hinj : Function.Injective E := DirectSum.embeddingLinearMap_injective (R := R)
    (fun t : HomologicalComplex₂.TotalDegree (n + 1) => M t.val.1 ⊗[R] C t.val.2)
    (rightSuccessor n)
  intro y
  change E (d y) = 0 ↔ _
  constructor
  · intro hy
    have hd : d y = 0 := hinj (hy.trans (map_zero E).symm)
    exact (hex y).mp hd
  · intro hy
    have hd : d y = 0 := (hex y).mpr hy
    rw [hd, map_zero]

/-- After the boundary, exactness uses the original injective degree-zero restriction. -/
theorem tensorBoundary_tensorMap_exact [∀ p, Module.Flat R (M p)]
    {A : ℕ → Type a} {B : ℕ → Type b} {C : ℕ → Type c}
    [∀ q, AddCommGroup (A q)] [∀ q, Module R (A q)]
    [∀ q, AddCommGroup (B q)] [∀ q, Module R (B q)]
    [∀ q, AddCommGroup (C q)] [∀ q, Module R (C q)]
    (δ : ∀ q, A q →ₗ[R] B (q + 1)) (f : ∀ q, B q →ₗ[R] C q)
    (h : ∀ q, Function.Exact (δ q) (f (q + 1))) (hzero : Function.Injective (f 0)) (n : ℕ) :
    Function.Exact (tensorBoundary (R := R) M δ n) (tensorMap (R := R) M f (n + 1)) := by
  apply DirectSum.exact_embedding_lmap
  · intro s
    exact exact_koszul_left s.val.1 _ _
      (Module.Flat.lTensor_exact (M s.val.1) (h s.val.2))
  · intro t ht
    have hq : t.val.2 = 0 := by
      have h := (mem_range_rightSuccessor n t).not.mp ht
      omega
    rw [hq]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ hzero

end Kunneth.MayerVietoris
