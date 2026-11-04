/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Graded.TensorProduct.Coherence
public import Aglib.Algebra.Graded.TensorProduct.TotalValues

/-! # Whole tensor diagrams from the original homogeneous values

This interface constructs the original total cup map and assembles the original
degreewise pullbacks by DirectSum.lmap.
Tensor generation, augmentation evaluation and coherence are proved over
variable module families before any geometric specialization.
-/

@[expose] public noncomputable section

open scoped TensorProduct DirectSum

universe u m n o p q s t m' n' p'

namespace DirectSum

variable {R : Type u} [CommSemiring R]

/-- The original total map has the original bundled cup values on every homogeneous tensor. -/
def TotalCupValues
    (M : ℕ → Type m) (N : ℕ → Type n) (P : ℕ → Type p)
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
    [∀ i, AddCommMonoid (P i)] [∀ i, Module R (P i)]
    (L : ((⨁ i, M i) ⊗[R] ⨁ j, N j) →ₗ[R] ⨁ d, P d)
    (cup : ∀ i j d, i + j = d → M i →ₗ[R] N j →ₗ[R] P d) : Prop :=
  ∀ (i j d : ℕ) (h : i + j = d) (x : M i) (y : N j),
    L (lof R ℕ M i x ⊗ₜ[R] lof R ℕ N j y) = lof R ℕ P d (cup i j d h x y)

section Augmentation

variable (M : ℕ → Type m)
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

/-- The given zero-component equation supplies both augmentation value families. -/
private theorem augmentationValuesOfZeroComponent
    (ε : (⨁ i, M i) →ₗ[R] R) (ε₀ : M 0 → R)
    (hε : ∀ a : (⨁ i, M i), ε a = ε₀ (a 0)) :
    (∀ x : M 0, ε (lof R ℕ M 0 x) = ε₀ x) ∧
      ∀ i (x : M (i + 1)), ε (lof R ℕ M (i + 1) x) = 0 := by
  have hzero : ε₀ 0 = 0 := by
    simpa only [map_zero, DFinsupp.zero_apply] using (hε 0).symm
  constructor
  · intro x
    rw [hε]
    change ε₀ ((DirectSum.of M 0 x) 0) = ε₀ x
    rw [DirectSum.of_eq_same]
  · intro i x
    rw [hε]
    change ε₀ ((DirectSum.of M (i + 1) x) 0) = 0
    rw [DirectSum.of_eq_of_ne (i + 1) 0 x (by simp)]
    exact hzero


end Augmentation

section Point

variable (M : ℕ → Type m) (N : ℕ → Type n) (P : ℕ → Type p)
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
  [∀ i, AddCommMonoid (P i)] [∀ i, Module R (P i)]

/-- The complete left point equation on the supplied original maps. -/
private def tensorPointLeftDiagramWithMap
    (L : ((⨁ i, M i) ⊗[R] ⨁ j, N j) →ₗ[R] ⨁ d, P d)
    (vₙ : ∀ d, P d →ₗ[R] N d) (ε : (⨁ i, M i) →ₗ[R] R) : Prop :=
  lmap vₙ ∘ₗ L =
    (TensorProduct.lid R (⨁ j, N j)).toLinearMap ∘ₗ ε.rTensor (⨁ j, N j)

/-- The complete right point equation on the supplied original maps. -/
private def tensorPointRightDiagramWithMap
    (L : ((⨁ i, M i) ⊗[R] ⨁ j, N j) →ₗ[R] ⨁ d, P d)
    (vₙ : ∀ d, P d →ₗ[R] M d) (ε : (⨁ j, N j) →ₗ[R] R) : Prop :=
  lmap vₙ ∘ₗ L =
    (TensorProduct.rid R (⨁ i, M i)).toLinearMap ∘ₗ ε.lTensor (⨁ i, M i)

/-- Homogeneous geometric values and the original augmentation give the whole left diagram. -/
private theorem tensorPointLeftDiagramWithMapOfValues
    (L : ((⨁ i, M i) ⊗[R] ⨁ j, N j) →ₗ[R] ⨁ d, P d)
    (vₙ : ∀ d, P d →ₗ[R] N d) (ε : (⨁ i, M i) →ₗ[R] R)
    (F : ∀ i j d, i + j = d → M i →ₗ[R] N j →ₗ[R] P d) (ε₀ : M 0 → R)
    (hL : TotalCupValues (R := R) M N P L F)
    (hε : ∀ a : (⨁ i, M i), ε a = ε₀ (a 0))
    (h₀ : ∀ j (x : M 0) (y : N j),
      vₙ j (F 0 j j (Nat.zero_add j) x y) = ε₀ x • y)
    (hSucc : ∀ i j (x : M (i + 1)) (y : N j),
      vₙ (i + 1 + j) (F (i + 1) j (i + 1 + j) rfl x y) = 0) :
    tensorPointLeftDiagramWithMap (R := R) M N P L vₙ ε := by
  unfold TotalCupValues at hL
  obtain ⟨hε₀, hεSucc⟩ := augmentationValuesOfZeroComponent M ε ε₀ hε
  unfold tensorPointLeftDiagramWithMap
  apply tensorDirectSum_ext (R := R) M N
  intro i j x y
  simp only [LinearMap.comp_apply, LinearMap.rTensor, TensorProduct.map_tmul,
    LinearMap.id_apply]
  cases i with
  | zero =>
    rw [hL 0 j j (Nat.zero_add j) x y, lmap_lof, h₀, hε₀, LinearMap.map_smul]
    exact (TensorProduct.lid_tmul (lof R ℕ N j y) (ε₀ x)).symm
  | succ i =>
    rw [hL (i + 1) j (i + 1 + j) rfl x y, lmap_lof, hSucc, map_zero, hεSucc,
      TensorProduct.zero_tmul]
    exact ((TensorProduct.lid R (⨁ j, N j)).toLinearMap.map_zero).symm

/-- Homogeneous geometric values and the original augmentation give the whole right diagram. -/
private theorem tensorPointRightDiagramWithMapOfValues
    (L : ((⨁ i, M i) ⊗[R] ⨁ j, N j) →ₗ[R] ⨁ d, P d)
    (vₙ : ∀ d, P d →ₗ[R] M d) (ε : (⨁ j, N j) →ₗ[R] R)
    (F : ∀ i j d, i + j = d → M i →ₗ[R] N j →ₗ[R] P d) (ε₀ : N 0 → R)
    (hL : TotalCupValues (R := R) M N P L F)
    (hε : ∀ a : (⨁ j, N j), ε a = ε₀ (a 0))
    (h₀ : ∀ i (x : M i) (y : N 0),
      vₙ i (F i 0 i (Nat.add_zero i) x y) = ε₀ y • x)
    (hSucc : ∀ i j (x : M i) (y : N (j + 1)),
      vₙ (i + (j + 1)) (F i (j + 1) (i + (j + 1)) rfl x y) = 0) :
    tensorPointRightDiagramWithMap (R := R) M N P L vₙ ε := by
  unfold TotalCupValues at hL
  obtain ⟨hε₀, hεSucc⟩ := augmentationValuesOfZeroComponent N ε ε₀ hε
  unfold tensorPointRightDiagramWithMap
  apply tensorDirectSum_ext (R := R) M N
  intro i j x y
  simp only [LinearMap.comp_apply, LinearMap.lTensor, TensorProduct.map_tmul,
    LinearMap.id_apply]
  cases j with
  | zero =>
    rw [hL i 0 i (Nat.add_zero i) x y, lmap_lof, h₀, hε₀, LinearMap.map_smul]
    exact (TensorProduct.rid_tmul (lof R ℕ M i x) (ε₀ y)).symm
  | succ j =>
    rw [hL i (j + 1) (i + (j + 1)) rfl x y, lmap_lof, hSucc, map_zero, hεSucc,
      TensorProduct.tmul_zero]
    exact ((TensorProduct.rid R (⨁ i, M i)).toLinearMap.map_zero).symm

end Point

section Naturality

variable (M : ℕ → Type m) (N : ℕ → Type n) (P : ℕ → Type p)
  (M' : ℕ → Type m') (N' : ℕ → Type n') (P' : ℕ → Type p')
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
  [∀ i, AddCommMonoid (P i)] [∀ i, Module R (P i)]
  [∀ i, AddCommMonoid (M' i)] [∀ i, Module R (M' i)]
  [∀ i, AddCommMonoid (N' i)] [∀ i, Module R (N' i)]
  [∀ i, AddCommMonoid (P' i)] [∀ i, Module R (P' i)]

/-- The original naturality equation with its degreewise maps assembled once. -/
private def tensorNaturalityDiagramWithMaps
    (L : ((⨁ i, M i) ⊗[R] ⨁ j, N j) →ₗ[R] ⨁ d, P d)
    (L' : ((⨁ i, M' i) ⊗[R] ⨁ j, N' j) →ₗ[R] ⨁ d, P' d)
    (fₙ : ∀ i, M i →ₗ[R] M' i) (gₙ : ∀ j, N j →ₗ[R] N' j)
    (vₙ : ∀ d, P d →ₗ[R] P' d) : Prop :=
  lmap vₙ ∘ₗ L = L' ∘ₗ TensorProduct.map (lmap fₙ) (lmap gₙ)

/-- Original homogeneous values and geometric compatibility give the entire naturality diagram. -/
private theorem tensorNaturalityDiagramWithMapsOfValues
    (L : ((⨁ i, M i) ⊗[R] ⨁ j, N j) →ₗ[R] ⨁ d, P d)
    (L' : ((⨁ i, M' i) ⊗[R] ⨁ j, N' j) →ₗ[R] ⨁ d, P' d)
    (fₙ : ∀ i, M i →ₗ[R] M' i) (gₙ : ∀ j, N j →ₗ[R] N' j)
    (vₙ : ∀ d, P d →ₗ[R] P' d)
    (F : ∀ i j d, i + j = d → M i →ₗ[R] N j →ₗ[R] P d)
    (F' : ∀ i j d, i + j = d → M' i →ₗ[R] N' j →ₗ[R] P' d)
    (hL : TotalCupValues (R := R) M N P L F)
    (hL' : TotalCupValues (R := R) M' N' P' L' F')
    (hF : ∀ i j d (h : i + j = d) (x : M i) (y : N j),
      vₙ d (F i j d h x y) = F' i j d h (fₙ i x) (gₙ j y)) :
    tensorNaturalityDiagramWithMaps (R := R) M N P M' N' P' L L' fₙ gₙ vₙ := by
  unfold TotalCupValues at hL hL'
  unfold tensorNaturalityDiagramWithMaps
  apply tensorDirectSum_ext (R := R) M N
  intro i j x y
  change lmap vₙ (L (lof R ℕ M i x ⊗ₜ[R] lof R ℕ N j y)) =
    L' (lmap fₙ (lof R ℕ M i x) ⊗ₜ[R] lmap gₙ (lof R ℕ N j y))
  rw [hL i j (i + j) rfl x y, lmap_lof vₙ, lmap_lof fₙ, lmap_lof gₙ,
    hL' i j (i + j) rfl (fₙ i x) (gₙ j y)]
  exact congrArg (lof R ℕ P' (i + j)) (hF i j (i + j) rfl x y)

end Naturality

section Associativity

variable (M : ℕ → Type m) (N : ℕ → Type n) (O : ℕ → Type o)
  (P : ℕ → Type p) (Q : ℕ → Type q) (S : ℕ → Type s) (T : ℕ → Type t)
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
  [∀ i, AddCommMonoid (O i)] [∀ i, Module R (O i)]
  [∀ i, AddCommMonoid (P i)] [∀ i, Module R (P i)]
  [∀ i, AddCommMonoid (Q i)] [∀ i, Module R (Q i)]
  [∀ i, AddCommMonoid (S i)] [∀ i, Module R (S i)]
  [∀ i, AddCommMonoid (T i)] [∀ i, Module R (T i)]

/-- The original associativity equation with the given associator pullbacks assembled once. -/
private def tensorAssociativityDiagramWithMaps
    (L_MN : ((⨁ i, M i) ⊗[R] ⨁ j, N j) →ₗ[R] ⨁ d, P d)
    (L_PO : ((⨁ d, P d) ⊗[R] ⨁ r, O r) →ₗ[R] ⨁ n, T n)
    (L_NO : ((⨁ j, N j) ⊗[R] ⨁ r, O r) →ₗ[R] ⨁ d, Q d)
    (L_MQ : ((⨁ i, M i) ⊗[R] ⨁ d, Q d) →ₗ[R] ⨁ n, S n)
    (aₙ : ∀ n, S n →ₗ[R] T n) : Prop :=
  L_PO ∘ₗ L_MN.rTensor (⨁ r, O r) =
    lmap aₙ ∘ₗ L_MQ ∘ₗ L_NO.lTensor (⨁ i, M i) ∘ₗ
      (TensorProduct.assoc R (⨁ i, M i) (⨁ j, N j) (⨁ r, O r)).toLinearMap

/-- Original homogeneous associativity gives the entire supplied-map diagram. -/
private theorem tensorAssociativityDiagramWithMapsOfValues
    (L_MN : ((⨁ i, M i) ⊗[R] ⨁ j, N j) →ₗ[R] ⨁ d, P d)
    (L_PO : ((⨁ d, P d) ⊗[R] ⨁ r, O r) →ₗ[R] ⨁ n, T n)
    (L_NO : ((⨁ j, N j) ⊗[R] ⨁ r, O r) →ₗ[R] ⨁ d, Q d)
    (L_MQ : ((⨁ i, M i) ⊗[R] ⨁ d, Q d) →ₗ[R] ⨁ n, S n)
    (aₙ : ∀ n, S n →ₗ[R] T n)
    (F_MN : ∀ i j d, i + j = d → M i →ₗ[R] N j →ₗ[R] P d)
    (F_PO : ∀ d r n, d + r = n → P d →ₗ[R] O r →ₗ[R] T n)
    (F_NO : ∀ j r d, j + r = d → N j →ₗ[R] O r →ₗ[R] Q d)
    (F_MQ : ∀ i d n, i + d = n → M i →ₗ[R] Q d →ₗ[R] S n)
    (hMN : TotalCupValues (R := R) M N P L_MN F_MN)
    (hPO : TotalCupValues (R := R) P O T L_PO F_PO)
    (hNO : TotalCupValues (R := R) N O Q L_NO F_NO)
    (hMQ : TotalCupValues (R := R) M Q S L_MQ F_MQ)
    (hassoc : ∀ i j r (x : M i) (y : N j) (z : O r),
      aₙ (i + j + r)
          (F_MQ i (j + r) (i + j + r) (Nat.add_assoc i j r).symm x
            (F_NO j r (j + r) rfl y z)) =
        F_PO (i + j) r (i + j + r) rfl (F_MN i j (i + j) rfl x y) z) :
    tensorAssociativityDiagramWithMaps (R := R) M N O P Q S T L_MN L_PO L_NO L_MQ aₙ := by
  unfold TotalCupValues at hMN hPO hNO hMQ
  unfold tensorAssociativityDiagramWithMaps
  exact tensorTotalMap_assoc_of_values (R := R) M N O P Q S T
    L_MN L_PO L_NO L_MQ (lmap aₙ)
    (fun i j d h x y => F_MN i j d h x y)
    (fun d r n h x z => F_PO d r n h x z)
    (fun j r d h y z => F_NO j r d h y z)
    (fun i d n h x y => F_MQ i d n h x y) aₙ
    hMN hPO hNO hMQ (fun n x => lmap_lof aₙ n x)
    (fun i j r x y z => (hassoc i j r x y z).symm)

end Associativity

end DirectSum

namespace DirectSum

/-- The given total-source presentation supplies the complete original homogeneous value law. -/
theorem totalCupValuesOfMapAfterEquivOfCup
    {R : Type u} [Field R]
    (M : ℕ → Type m) (N : ℕ → Type n) (P : ℕ → Type p)
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
    [∀ i, AddCommMonoid (P i)] [∀ i, Module R (P i)]
    (E : ((⨁ i, M i) ⊗[R] ⨁ j, N j) ≃ₗ[R]
      ⨁ n, ⨁ s : HomologicalComplex₂.TotalDegree n, M s.val.1 ⊗[R] N s.val.2)
    (hE : E = tensorFiberEquiv (R := R) M N
      (ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ)))
    (cup : ∀ i j d, i + j = d → M i →ₗ[R] N j →ₗ[R] P d)
    (L : ((⨁ i, M i) ⊗[R] ⨁ j, N j) →ₗ[R] ⨁ d, P d)
    (hL : L = mapAfterEquivOfCup E cup) :
    TotalCupValues (R := R) M N P L cup := by
  unfold TotalCupValues
  intro i j d h x y
  exact mapAfterEquivOfCup_tmul (R := R) (M := M) (N := N) (P := P)
    hE cup hL h x y

end DirectSum

namespace DirectSum

variable {R : Type u} [Field R]

section CanonicalTotalMap

variable (M : ℕ → Type m) (N : ℕ → Type n) (P : ℕ → Type p)
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
  [∀ i, AddCommMonoid (P i)] [∀ i, Module R (P i)]

/-- The original total cup operator with its original total-degree distribution. -/
def canonicalTotalCupMap
    (cup : ∀ i j d, i + j = d → M i →ₗ[R] N j →ₗ[R] P d) :
    ((⨁ i, M i) ⊗[R] ⨁ j, N j) →ₗ[R] ⨁ d, P d :=
  mapAfterEquivOfCup (totalDegreeSourceEquiv (R := R) (M := M) (N := N)) cup

/-- The original constructor provides its entire homogeneous value family generically. -/
private theorem canonicalTotalCupMapValues
    (cup : ∀ i j d, i + j = d → M i →ₗ[R] N j →ₗ[R] P d) :
    TotalCupValues (R := R) M N P (canonicalTotalCupMap M N P cup) cup := by
  exact totalCupValuesOfMapAfterEquivOfCup M N P
    (totalDegreeSourceEquiv (R := R) (M := M) (N := N)) rfl cup
    (canonicalTotalCupMap M N P cup) rfl

/-- The original left point diagram, with its total cup and pullback maps assembled once. -/
def tensorPointLeftDiagram
    (cup : ∀ i j d, i + j = d → M i →ₗ[R] N j →ₗ[R] P d)
    (vₙ : ∀ d, P d →ₗ[R] N d) (ε : (⨁ i, M i) →ₗ[R] R) : Prop :=
  lmap vₙ ∘ₗ canonicalTotalCupMap M N P cup =
    (TensorProduct.lid R (⨁ j, N j)).toLinearMap ∘ₗ ε.rTensor (⨁ j, N j)

/-- The original right point diagram, with its total cup and pullback maps assembled once. -/
def tensorPointRightDiagram
    (cup : ∀ i j d, i + j = d → M i →ₗ[R] N j →ₗ[R] P d)
    (vₙ : ∀ d, P d →ₗ[R] M d) (ε : (⨁ j, N j) →ₗ[R] R) : Prop :=
  lmap vₙ ∘ₗ canonicalTotalCupMap M N P cup =
    (TensorProduct.rid R (⨁ i, M i)).toLinearMap ∘ₗ ε.lTensor (⨁ i, M i)

/-- Geometric point compatibility supplies the complete original left diagram. -/
theorem tensorPointLeftDiagramOfValues
    (cup : ∀ i j d, i + j = d → M i →ₗ[R] N j →ₗ[R] P d)
    (vₙ : ∀ d, P d →ₗ[R] N d) (ε : (⨁ i, M i) →ₗ[R] R) (ε₀ : M 0 → R)
    (hε : ∀ a : (⨁ i, M i), ε a = ε₀ (a 0))
    (h₀ : ∀ j (x : M 0) (y : N j),
      vₙ j (cup 0 j j (Nat.zero_add j) x y) = ε₀ x • y)
    (hSucc : ∀ i j (x : M (i + 1)) (y : N j),
      vₙ (i + 1 + j) (cup (i + 1) j (i + 1 + j) rfl x y) = 0) :
    tensorPointLeftDiagram (R := R) M N P cup vₙ ε := by
  unfold tensorPointLeftDiagram
  exact tensorPointLeftDiagramWithMapOfValues (R := R) M N P
    (canonicalTotalCupMap M N P cup) vₙ ε cup ε₀
    (canonicalTotalCupMapValues M N P cup) hε h₀ hSucc

/-- Geometric point compatibility supplies the complete original right diagram. -/
theorem tensorPointRightDiagramOfValues
    (cup : ∀ i j d, i + j = d → M i →ₗ[R] N j →ₗ[R] P d)
    (vₙ : ∀ d, P d →ₗ[R] M d) (ε : (⨁ j, N j) →ₗ[R] R) (ε₀ : N 0 → R)
    (hε : ∀ a : (⨁ j, N j), ε a = ε₀ (a 0))
    (h₀ : ∀ i (x : M i) (y : N 0),
      vₙ i (cup i 0 i (Nat.add_zero i) x y) = ε₀ y • x)
    (hSucc : ∀ i j (x : M i) (y : N (j + 1)),
      vₙ (i + (j + 1)) (cup i (j + 1) (i + (j + 1)) rfl x y) = 0) :
    tensorPointRightDiagram (R := R) M N P cup vₙ ε := by
  unfold tensorPointRightDiagram
  exact tensorPointRightDiagramWithMapOfValues (R := R) M N P
    (canonicalTotalCupMap M N P cup) vₙ ε cup ε₀
    (canonicalTotalCupMapValues M N P cup) hε h₀ hSucc

end CanonicalTotalMap

section CanonicalNaturality

variable (M : ℕ → Type m) (N : ℕ → Type n) (P : ℕ → Type p)
  (M' : ℕ → Type m') (N' : ℕ → Type n') (P' : ℕ → Type p')
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
  [∀ i, AddCommMonoid (P i)] [∀ i, Module R (P i)]
  [∀ i, AddCommMonoid (M' i)] [∀ i, Module R (M' i)]
  [∀ i, AddCommMonoid (N' i)] [∀ i, Module R (N' i)]
  [∀ i, AddCommMonoid (P' i)] [∀ i, Module R (P' i)]

/-- The original naturality diagram with both given total cup maps constructed generically. -/
def tensorNaturalityDiagram
    (cup : ∀ i j d, i + j = d → M i →ₗ[R] N j →ₗ[R] P d)
    (cup' : ∀ i j d, i + j = d → M' i →ₗ[R] N' j →ₗ[R] P' d)
    (fₙ : ∀ i, M i →ₗ[R] M' i) (gₙ : ∀ j, N j →ₗ[R] N' j)
    (vₙ : ∀ d, P d →ₗ[R] P' d) : Prop :=
  lmap vₙ ∘ₗ canonicalTotalCupMap M N P cup =
    canonicalTotalCupMap M' N' P' cup' ∘ₗ TensorProduct.map (lmap fₙ) (lmap gₙ)

/-- The given geometric cup compatibility proves the entire original naturality diagram. -/
theorem tensorNaturalityDiagramOfValues
    (cup : ∀ i j d, i + j = d → M i →ₗ[R] N j →ₗ[R] P d)
    (cup' : ∀ i j d, i + j = d → M' i →ₗ[R] N' j →ₗ[R] P' d)
    (fₙ : ∀ i, M i →ₗ[R] M' i) (gₙ : ∀ j, N j →ₗ[R] N' j)
    (vₙ : ∀ d, P d →ₗ[R] P' d)
    (hF : ∀ i j d (h : i + j = d) (x : M i) (y : N j),
      vₙ d (cup i j d h x y) = cup' i j d h (fₙ i x) (gₙ j y)) :
    tensorNaturalityDiagram (R := R) M N P M' N' P' cup cup' fₙ gₙ vₙ := by
  unfold tensorNaturalityDiagram
  exact tensorNaturalityDiagramWithMapsOfValues (R := R) M N P M' N' P'
    (canonicalTotalCupMap M N P cup) (canonicalTotalCupMap M' N' P' cup')
    fₙ gₙ vₙ cup cup' (canonicalTotalCupMapValues M N P cup)
    (canonicalTotalCupMapValues M' N' P' cup') hF

end CanonicalNaturality

section CanonicalAssociativity

variable (M : ℕ → Type m) (N : ℕ → Type n) (O : ℕ → Type o)
  (P : ℕ → Type p) (Q : ℕ → Type q) (S : ℕ → Type s) (T : ℕ → Type t)
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
  [∀ i, AddCommMonoid (O i)] [∀ i, Module R (O i)]
  [∀ i, AddCommMonoid (P i)] [∀ i, Module R (P i)]
  [∀ i, AddCommMonoid (Q i)] [∀ i, Module R (Q i)]
  [∀ i, AddCommMonoid (S i)] [∀ i, Module R (S i)]
  [∀ i, AddCommMonoid (T i)] [∀ i, Module R (T i)]

/-- The original associativity diagram with all four given total cup maps constructed once. -/
def tensorAssociativityDiagram
    (cup_MN : ∀ i j d, i + j = d → M i →ₗ[R] N j →ₗ[R] P d)
    (cup_PO : ∀ d r n, d + r = n → P d →ₗ[R] O r →ₗ[R] T n)
    (cup_NO : ∀ j r d, j + r = d → N j →ₗ[R] O r →ₗ[R] Q d)
    (cup_MQ : ∀ i d n, i + d = n → M i →ₗ[R] Q d →ₗ[R] S n)
    (aₙ : ∀ n, S n →ₗ[R] T n) : Prop :=
  canonicalTotalCupMap P O T cup_PO ∘ₗ (canonicalTotalCupMap M N P cup_MN).rTensor
      (⨁ r, O r) =
    lmap aₙ ∘ₗ canonicalTotalCupMap M Q S cup_MQ ∘ₗ
      (canonicalTotalCupMap N O Q cup_NO).lTensor (⨁ i, M i) ∘ₗ
      (TensorProduct.assoc R (⨁ i, M i) (⨁ j, N j) (⨁ r, O r)).toLinearMap

/-- Geometric associativity proves the entire original diagram after the shared construction. -/
theorem tensorAssociativityDiagramOfValues
    (cup_MN : ∀ i j d, i + j = d → M i →ₗ[R] N j →ₗ[R] P d)
    (cup_PO : ∀ d r n, d + r = n → P d →ₗ[R] O r →ₗ[R] T n)
    (cup_NO : ∀ j r d, j + r = d → N j →ₗ[R] O r →ₗ[R] Q d)
    (cup_MQ : ∀ i d n, i + d = n → M i →ₗ[R] Q d →ₗ[R] S n)
    (aₙ : ∀ n, S n →ₗ[R] T n)
    (hassoc : ∀ i j r (x : M i) (y : N j) (z : O r),
      aₙ (i + j + r)
          (cup_MQ i (j + r) (i + j + r) (Nat.add_assoc i j r).symm x
            (cup_NO j r (j + r) rfl y z)) =
        cup_PO (i + j) r (i + j + r) rfl (cup_MN i j (i + j) rfl x y) z) :
    tensorAssociativityDiagram (R := R) M N O P Q S T cup_MN cup_PO cup_NO cup_MQ aₙ := by
  unfold tensorAssociativityDiagram
  exact tensorAssociativityDiagramWithMapsOfValues (R := R) M N O P Q S T
    (canonicalTotalCupMap M N P cup_MN) (canonicalTotalCupMap P O T cup_PO)
    (canonicalTotalCupMap N O Q cup_NO) (canonicalTotalCupMap M Q S cup_MQ)
    aₙ cup_MN cup_PO cup_NO cup_MQ
    (canonicalTotalCupMapValues M N P cup_MN) (canonicalTotalCupMapValues P O T cup_PO)
    (canonicalTotalCupMapValues N O Q cup_NO) (canonicalTotalCupMapValues M Q S cup_MQ) hassoc

end CanonicalAssociativity

end DirectSum
