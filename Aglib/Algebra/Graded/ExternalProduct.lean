/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Graded.DirectSum
public import Mathlib.LinearAlgebra.TensorProduct.Graded.Internal

/-!
# Signed external products of native graded direct sums

The entire operational construction is made over variable graded families.
The two actual algebra maps and their degreewise formulas, together with the
original target cup and its signed crossing law, supply Mathlib's native
signed-tensor lift. The original summand inclusions and tensor maps remain
its homogeneous and whole underlying-linear formulas.
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u v₁ v₂ v₃

namespace AlgHom

universe a₁ a₂ a₃ a₄ a₅ a₆ a₇

/-- The literal tensor equation retains the given algebra map and source equivalence. -/
theorem comp_linearEquiv_map_eq_of_values
    {R : Type u} [CommSemiring R]
    {A : Type a₁} [AddCommMonoid A] [Module R A]
    {B : Type a₂} [AddCommMonoid B] [Module R B]
    {C : Type a₃} [Semiring C] [Algebra R C]
    {S : Type a₄} [Semiring S] [Algebra R S]
    {M : Type a₅} [AddCommMonoid M] [Module R M]
    {N : Type a₆} [AddCommMonoid N] [Module R N]
    {P : Type a₇} [AddCommMonoid P] [Module R P]
    (Φ : S →ₐ[R] C) (s : A ⊗[R] B ≃ₗ[R] S)
    (I_M : M →ₗ[R] A) (I_N : N →ₗ[R] B) (I_P : P →ₗ[R] C)
    (T : M ⊗[R] N →ₗ[R] P) (pure : A → B → S) (e : M → N → P)
    (hs : ∀ a b, s (a ⊗ₜ[R] b) = pure a b)
    (hΦ : ∀ x y, Φ (pure (I_M x) (I_N y)) = I_P (e x y))
    (hT : ∀ x y, T (x ⊗ₜ[R] y) = e x y) :
    Φ.toLinearMap ∘ₗ s.toLinearMap ∘ₗ TensorProduct.map I_M I_N = I_P ∘ₗ T := by
  apply TensorProduct.ext'
  intro x y
  exact (congrArg Φ (hs (I_M x) (I_N y))).trans
    ((hΦ x y).trans (congrArg I_P (hT x y).symm))

end AlgHom

namespace GradedTensorProduct

section AmbientExternalProduct

universe a b c m n p

variable {R : Type u} [CommRing R]
  {A : Type a} [Ring A] [Algebra R A]
  {B : Type b} [Ring B] [Algebra R B]
  {C : Type c} [Ring C] [Algebra R C]
  {𝒜 : ℕ → Submodule R A} [gradedA : GradedAlgebra 𝒜]
  {ℬ : ℕ → Submodule R B} [gradedB : GradedAlgebra ℬ]

/-- The canonical source uses the given actual algebras and their chosen grades. -/
def externalProductSourceEquiv : (A ⊗[R] B) ≃ₗ[R] GradedTensorProduct R 𝒜 ℬ :=
  GradedTensorProduct.of R 𝒜 ℬ

/-- The chosen source retains every original pure tensor. -/
theorem externalProductSourceEquiv_tmul (a : A) (b : B) :
    externalProductSourceEquiv (R := R) (𝒜 := 𝒜) (ℬ := ℬ) (a ⊗ₜ[R] b) = a ᵍ⊗ₜ[R] b := rfl

/-- The chosen source retains the actual unit. -/
theorem externalProductSourceEquiv_one :
    externalProductSourceEquiv (R := R) (𝒜 := 𝒜) (ℬ := ℬ) ((1 : A) ⊗ₜ[R] (1 : B)) = 1 := rfl

/-- The complete pure-value equation keeps the given actual algebra parents. -/
def ExternalProductPureEq (Φ : GradedTensorProduct R 𝒜 ℬ →ₐ[R] C)
    (f : A →ₐ[R] C) (g : B →ₐ[R] C) : Prop :=
  ∀ (a : A) (b : B), Φ (a ᵍ⊗ₜ[R] b) = f a * g b

variable {M : ℕ → Type m} {N : ℕ → Type n} {P : ℕ → Type p}
  [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
  [∀ i, AddCommGroup (P i)] [∀ i, Module R (P i)]

/-- Literal homogeneous values on the supplied inclusion maps, without rebuilt algebras. -/
def ExternalProductHomogeneousEq (Φ : GradedTensorProduct R 𝒜 ℬ →ₐ[R] C)
    (I_M : ∀ i, M i →ₗ[R] A) (I_N : ∀ i, N i →ₗ[R] B) (I_P : ∀ i, P i →ₗ[R] C)
    (e : ∀ {i j d : ℕ}, i + j = d → M i →ₗ[R] N j →ₗ[R] P d) : Prop :=
  ∀ {i j d : ℕ} (h : i + j = d) (x : M i) (y : N j),
    Φ (I_M i x ᵍ⊗ₜ[R] I_N j y) = I_P d (e h x y)

variable (I_M : ∀ i, M i →ₗ[R] A) (I_N : ∀ i, N i →ₗ[R] B)
  (I_P : ∀ i, P i →ₗ[R] C)
  (hM : ∀ i (a : 𝒜 i), ∃ x : M i, I_M i x = (a : A))
  (hN : ∀ i (b : ℬ i), ∃ y : N i, I_N i y = (b : B))
  (cup : ∀ {i j d : ℕ}, i + j = d → P i →ₗ[R] P j →ₗ[R] P d)
  (hMul : ∀ {i j : ℕ} (x : P i) (y : P j),
    I_P i x * I_P j y = I_P (i + j) (cup rfl x y))
  (f : A →ₐ[R] C) (g : B →ₐ[R] C)
  (fDegree : ∀ i, M i →ₗ[R] P i) (gDegree : ∀ i, N i →ₗ[R] P i)
  (hf : ∀ i (x : M i), f (I_M i x) = I_P i (fDegree i x))
  (hg : ∀ i (y : N i), g (I_N i y) = I_P i (gDegree i y))
  (hComm : ∀ {i j d : ℕ} (h : i + j = d) (x : M i) (y : N j),
    cup h (fDegree i x) (gDegree j y) = ((-1 : ℤ) ^ (i * j)) •
      cup ((Nat.add_comm j i).trans h) (gDegree j y) (fDegree i x))

omit gradedA gradedB in
include hM hN hMul hf hg hComm in
/-- Generation by the actual inclusions gives signed commutation in the actual target. -/
theorem externalProduct_anticommutes {i j : ℕ} (a : 𝒜 i) (b : ℬ j) :
    f a * g b = ((-1 : ℤˣ) ^ (j * i)) • (g b * f a) := by
  obtain ⟨x, hx⟩ := hM i a
  obtain ⟨y, hy⟩ := hN j b
  have hCup {i j d : ℕ} (h : i + j = d) (x : P i) (y : P j) :
      I_P d (cup h x y) = I_P i x * I_P j y := by
    subst d
    exact (hMul x y).symm
  rw [← hx, ← hy, hf, hg, hMul, hComm, map_zsmul, hCup]
  simp only [Units.smul_def, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
    Nat.mul_comm]

/-- The whole signed construction uses only the supplied actual algebras and maps. -/
def externalProductAlgHom : GradedTensorProduct R 𝒜 ℬ →ₐ[R] C :=
  GradedTensorProduct.lift 𝒜 ℬ f g (fun {_i _j} a b =>
    externalProduct_anticommutes
      (I_M := I_M) (I_N := I_N) (I_P := I_P) (hM := hM) (hN := hN)
      (cup := cup) (hMul := hMul) (f := f) (g := g)
      (fDegree := fDegree) (gDegree := gDegree)
      (hf := hf) (hg := hg) (hComm := hComm) a b)

/-- The same constructed map has its literal whole pure-value formula. -/
theorem externalProductAlgHom_pureEq :
    ExternalProductPureEq
      (externalProductAlgHom I_M I_N I_P hM hN cup hMul f g fDegree gDegree hf hg hComm) f g :=
  fun _ _ => rfl

/-- Actual pure values give the whole homogeneous family on the supplied inclusion maps. -/
theorem ExternalProductPureEq.toHomogeneousEq
    {Φ : GradedTensorProduct R 𝒜 ℬ →ₐ[R] C} {f : A →ₐ[R] C} {g : B →ₐ[R] C}
    (hΦ : ExternalProductPureEq Φ f g)
    (cup : ∀ {i j d : ℕ}, i + j = d → P i →ₗ[R] P j →ₗ[R] P d)
    (hMul : ∀ {i j : ℕ} (x : P i) (y : P j),
      I_P i x * I_P j y = I_P (i + j) (cup rfl x y))
    (fDegree : ∀ i, M i →ₗ[R] P i) (gDegree : ∀ i, N i →ₗ[R] P i)
    (hf : ∀ i (x : M i), f (I_M i x) = I_P i (fDegree i x))
    (hg : ∀ i (y : N i), g (I_N i y) = I_P i (gDegree i y))
    (e : ∀ {i j d : ℕ}, i + j = d → M i →ₗ[R] N j →ₗ[R] P d)
    (he : ∀ {i j d : ℕ} (h : i + j = d) (x : M i) (y : N j),
      e h x y = cup h (fDegree i x) (gDegree j y)) :
    ExternalProductHomogeneousEq Φ I_M I_N I_P e := by
  intro i j d h x y
  have h₁ := hΦ (I_M i x) (I_N j y)
  have h₂ := congrArg₂ (fun a b : C => a * b) (hf i x) (hg j y)
  have h₃ : I_P i (fDegree i x) * I_P j (gDegree j y) =
      I_P d (cup h (fDegree i x) (gDegree j y)) := by
    subst d
    exact hMul _ _
  have h₄ := congrArg (I_P d) (he h x y).symm
  exact h₁.trans (h₂.trans (h₃.trans h₄))

/-- Evaluate the same actual homogeneous family without rebuilding its source or target. -/
theorem ExternalProductHomogeneousEq.apply
    {Φ : GradedTensorProduct R 𝒜 ℬ →ₐ[R] C}
    {e : ∀ {i j d : ℕ}, i + j = d → M i →ₗ[R] N j →ₗ[R] P d}
    (hΦ : ExternalProductHomogeneousEq Φ I_M I_N I_P e)
    {i j d : ℕ} (h : i + j = d) (x : M i) (y : N j) :
    Φ (I_M i x ᵍ⊗ₜ[R] I_N j y) = I_P d (e h x y) := hΦ h x y

/-- Whole tensor normalization retains the actual Phi, inclusions and original tensor map. -/
theorem ExternalProductHomogeneousEq.tensor
    {Φ : GradedTensorProduct R 𝒜 ℬ →ₐ[R] C}
    {e : ∀ {i j d : ℕ}, i + j = d → M i →ₗ[R] N j →ₗ[R] P d}
    (hΦ : ExternalProductHomogeneousEq Φ I_M I_N I_P e)
    {i j d : ℕ} (h : i + j = d) (T : M i ⊗[R] N j →ₗ[R] P d)
    (hT : ∀ x y, T (x ⊗ₜ[R] y) = e h x y) :
    Φ.toLinearMap ∘ₗ
        (externalProductSourceEquiv (R := R) (𝒜 := 𝒜) (ℬ := ℬ)).toLinearMap ∘ₗ
        TensorProduct.map (I_M i) (I_N j) = I_P d ∘ₗ T := by
  exact AlgHom.comp_linearEquiv_map_eq_of_values Φ
    (externalProductSourceEquiv (R := R) (𝒜 := 𝒜) (ℬ := ℬ)) (I_M i) (I_N j) (I_P d) T
    (fun a b => a ᵍ⊗ₜ[R] b) (fun x y => e h x y)
    externalProductSourceEquiv_tmul (hΦ h) hT

end AmbientExternalProduct

end GradedTensorProduct

namespace DirectSum

variable {R : Type u} [CommRing R]
  {M : ℕ → Type v₁} {N : ℕ → Type v₂} {P : ℕ → Type v₃}
  [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  [∀ n, AddCommGroup (N n)] [∀ n, Module R (N n)]
  [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)]
  [GRing M] [GAlgebra R M] [GRing N] [GAlgebra R N] [GRing P] [GAlgebra R P]
  [gradeM : GradedAlgebra (summandSubmodule (R := R) M)]
  [gradeN : GradedAlgebra (summandSubmodule (R := R) N)]

/-- The original native tensor identification retains the exact selected summand grading. -/
def externalProductSourceEquiv :
    (DirectSum ℕ M ⊗[R] DirectSum ℕ N) ≃ₗ[R]
      GradedTensorProduct R (summandSubmodule (R := R) M) (summandSubmodule (R := R) N) :=
  GradedTensorProduct.of R (summandSubmodule (R := R) M) (summandSubmodule (R := R) N)

/-- The shared source identification is the original pure signed tensor. -/
@[simp]
theorem externalProductSourceEquiv_tmul (a : DirectSum ℕ M) (b : DirectSum ℕ N) :
    externalProductSourceEquiv (R := R) (M := M) (N := N) (a ⊗ₜ[R] b) = a ᵍ⊗ₜ[R] b := rfl

/-- The selected native source equivalence preserves the actual tensor unit. -/
theorem externalProductSourceEquiv_one :
    externalProductSourceEquiv (R := R) (M := M) (N := N)
      ((1 : DirectSum ℕ M) ⊗ₜ[R] (1 : DirectSum ℕ N)) = 1 := rfl

/-- A regular whole pure-product equation on the original three actual maps. -/
def ExternalProductPureEq
    (Φ : GradedTensorProduct R (summandSubmodule (R := R) M)
      (summandSubmodule (R := R) N) →ₐ[R] DirectSum ℕ P)
    (f₀ : DirectSum ℕ M →ₐ[R] DirectSum ℕ P)
    (g₀ : DirectSum ℕ N →ₐ[R] DirectSum ℕ P) : Prop :=
  ∀ (a : DirectSum ℕ M) (b : DirectSum ℕ N), Φ (a ᵍ⊗ₜ[R] b) = f₀ a * g₀ b

/-- Evaluate the whole original equation without rebuilding its concrete constructor. -/
theorem ExternalProductPureEq.apply
    {Φ : GradedTensorProduct R (summandSubmodule (R := R) M)
      (summandSubmodule (R := R) N) →ₐ[R] DirectSum ℕ P}
    {f₀ : DirectSum ℕ M →ₐ[R] DirectSum ℕ P}
    {g₀ : DirectSum ℕ N →ₐ[R] DirectSum ℕ P}
    (h : ExternalProductPureEq Φ f₀ g₀) (a : DirectSum ℕ M) (b : DirectSum ℕ N) :
    Φ (a ᵍ⊗ₜ[R] b) = f₀ a * g₀ b := h a b

/-- The complete homogeneous family equation on the actual map and bilinear family. -/
def ExternalProductHomogeneousEq
    (Φ : GradedTensorProduct R (summandSubmodule (R := R) M)
      (summandSubmodule (R := R) N) →ₐ[R] DirectSum ℕ P)
    (e : ∀ {p q n : ℕ}, p + q = n → M p →ₗ[R] N q →ₗ[R] P n) : Prop :=
  ∀ {p q n : ℕ} (h : p + q = n) (x : M p) (y : N q),
    Φ (homogeneousInclusion (R := R) M p x ᵍ⊗ₜ[R]
      homogeneousInclusion (R := R) N q y) = homogeneousInclusion (R := R) P n (e h x y)

/-- The whole family is evaluated without expanding the actual algebra map or coefficient family. -/
theorem ExternalProductHomogeneousEq.apply
    {Φ : GradedTensorProduct R (summandSubmodule (R := R) M)
      (summandSubmodule (R := R) N) →ₐ[R] DirectSum ℕ P}
    {e : ∀ {p q n : ℕ}, p + q = n → M p →ₗ[R] N q →ₗ[R] P n}
    (he : ExternalProductHomogeneousEq Φ e) {p q n : ℕ} (h : p + q = n)
    (x : M p) (y : N q) :
    Φ (homogeneousInclusion (R := R) M p x ᵍ⊗ₜ[R]
      homogeneousInclusion (R := R) N q y) = homogeneousInclusion (R := R) P n (e h x y) :=
  he h x y

/-- The entire original homogeneous tensor map follows from that same complete family. -/
theorem ExternalProductHomogeneousEq.tensor
    {Φ : GradedTensorProduct R (summandSubmodule (R := R) M)
      (summandSubmodule (R := R) N) →ₐ[R] DirectSum ℕ P}
    {e : ∀ {p q n : ℕ}, p + q = n → M p →ₗ[R] N q →ₗ[R] P n}
    (he : ExternalProductHomogeneousEq Φ e) {p q n : ℕ} (h : p + q = n)
    (t : M p ⊗[R] N q →ₗ[R] P n)
    (ht : ∀ (x : M p) (y : N q), t (x ⊗ₜ[R] y) = e h x y) :
    Φ.toLinearMap ∘ₗ (externalProductSourceEquiv (R := R) (M := M) (N := N)).toLinearMap ∘ₗ
        TensorProduct.map (homogeneousInclusion (R := R) M p)
          (homogeneousInclusion (R := R) N q) =
      homogeneousInclusion (R := R) P n ∘ₗ t := by
  apply TensorProduct.ext'
  intro x y
  exact (he.apply h x y).trans
    (congrArg (homogeneousInclusion (R := R) P n) (ht x y).symm)

variable
  (cup : ∀ {p q n : ℕ}, p + q = n → P p →ₗ[R] P q →ₗ[R] P n)
  (hMul : ∀ {p q : ℕ} (x : P p) (y : P q),
    homogeneousInclusion (R := R) P p x * homogeneousInclusion (R := R) P q y =
      homogeneousInclusion (R := R) P (p + q) (cup rfl x y))
  (f : DirectSum ℕ M →ₐ[R] DirectSum ℕ P)
  (g : DirectSum ℕ N →ₐ[R] DirectSum ℕ P)
  (fDegree : ∀ n, M n →ₗ[R] P n) (gDegree : ∀ n, N n →ₗ[R] P n)
  (hf : ∀ n (x : M n), f (homogeneousInclusion (R := R) M n x) =
    homogeneousInclusion (R := R) P n (fDegree n x))
  (hg : ∀ n (y : N n), g (homogeneousInclusion (R := R) N n y) =
    homogeneousInclusion (R := R) P n (gDegree n y))
  (hComm : ∀ {p q n : ℕ} (h : p + q = n) (x : M p) (y : N q),
    cup h (fDegree p x) (gDegree q y) = ((-1 : ℤ) ^ (p * q)) •
      cup ((Nat.add_comm q p).trans h) (gDegree q y) (fDegree p x))

omit [GAlgebra R P] in
include hMul in
/-- The original cup equation with an arbitrary displayed total degree. -/
theorem externalProduct_inclusion_cup {p q n : ℕ} (h : p + q = n)
    (x : P p) (y : P q) :
    homogeneousInclusion (R := R) P n (cup h x y) =
      homogeneousInclusion (R := R) P p x * homogeneousInclusion (R := R) P q y := by
  subst n
  exact (hMul x y).symm

omit gradeM gradeN in
include hMul hf hg hComm in
/-- The two actual algebra maps anticommute on the canonical homogeneous ranges. -/
theorem externalProduct_anticommutes {p q : ℕ}
    (a : summandSubmodule (R := R) M p) (b : summandSubmodule (R := R) N q) :
    f a * g b = ((-1 : ℤˣ) ^ (q * p)) • (g b * f a) := by
  obtain ⟨a, ha⟩ := a
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨b, hb⟩ := b
  obtain ⟨y, rfl⟩ := hb
  rw [hf, hg, hMul, hComm, map_zsmul, externalProduct_inclusion_cup cup hMul]
  simp only [Units.smul_def, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
    Nat.mul_comm]

/-- The native signed-tensor algebra map, constructed once with its complete
homogeneous proof before any concrete realization of the graded families. -/
def externalProductAlgHom :
    GradedTensorProduct R (summandSubmodule (R := R) M) (summandSubmodule (R := R) N) →ₐ[R]
      DirectSum ℕ P :=
  GradedTensorProduct.lift (summandSubmodule (R := R) M) (summandSubmodule (R := R) N)
    f g (fun {p q} a b =>
      externalProduct_anticommutes cup hMul f g fDegree gDegree hf hg hComm (p := p) (q := q) a b)

/-- The complete original constructor satisfies the same regular whole equation. -/
theorem externalProductAlgHom_pureEq :
    ExternalProductPureEq (externalProductAlgHom cup hMul f g fDegree gDegree hf hg hComm) f g :=
  fun _ _ => rfl

/-- The full pure-tensor formula retains precisely the two original algebra maps. -/
@[simp]
theorem externalProductAlgHom_tmul (a : DirectSum ℕ M) (b : DirectSum ℕ N) :
    externalProductAlgHom cup hMul f g fDegree gDegree hf hg hComm (a ᵍ⊗ₜ[R] b) =
      f a * g b := rfl

/-- On homogeneous elements this is the original target cup of the original degreewise maps. -/
theorem externalProductAlgHom_homogeneous {p q n : ℕ} (h : p + q = n)
    (x : M p) (y : N q) :
    externalProductAlgHom cup hMul f g fDegree gDegree hf hg hComm
        (homogeneousInclusion (R := R) M p x ᵍ⊗ₜ[R] homogeneousInclusion (R := R) N q y) =
      homogeneousInclusion (R := R) P n (cup h (fDegree p x) (gDegree q y)) := by
  rw [externalProductAlgHom_tmul, hf, hg, ← externalProduct_inclusion_cup cup hMul h]

/-- The original constructor retains the supplied original external family and its value law. -/
theorem externalProductAlgHom_homogeneousEq
    (e : ∀ {p q n : ℕ}, p + q = n → M p →ₗ[R] N q →ₗ[R] P n)
    (he : ∀ {p q n : ℕ} (h : p + q = n) (x : M p) (y : N q),
      e h x y = cup h (fDegree p x) (gDegree q y)) :
    ExternalProductHomogeneousEq
      (externalProductAlgHom cup hMul f g fDegree gDegree hf hg hComm) e :=
  fun {_p _q n} h x y =>
    (externalProductAlgHom_homogeneous cup hMul f g fDegree gDegree hf hg hComm h x y).trans
      (congrArg (homogeneousInclusion (R := R) P n) (he h x y).symm)

/-- The entire underlying linear map is the original native tensor map followed
by original multiplication, with only the native signed-tensor identification. -/
theorem externalProductAlgHom_toLinearMap :
    (externalProductAlgHom cup hMul f g fDegree gDegree hf hg hComm).toLinearMap =
      LinearMap.mul' R (DirectSum ℕ P) ∘ₗ TensorProduct.map f.toLinearMap g.toLinearMap ∘ₗ
        (GradedTensorProduct.of R (summandSubmodule (R := R) M)
          (summandSubmodule (R := R) N)).symm.toLinearMap := rfl

/-- Whole homogeneous-tensor normalization, over arbitrary module universes. -/
theorem externalProductAlgHom_tensor {p q n : ℕ} (h : p + q = n) :
    (externalProductAlgHom cup hMul f g fDegree gDegree hf hg hComm).toLinearMap ∘ₗ
        (GradedTensorProduct.of R (summandSubmodule (R := R) M)
          (summandSubmodule (R := R) N)).toLinearMap ∘ₗ
        TensorProduct.map (homogeneousInclusion (R := R) M p)
          (homogeneousInclusion (R := R) N q) =
      homogeneousInclusion (R := R) P n ∘ₗ
        TensorProduct.lift ((cup h).compl₁₂ (fDegree p) (gDegree q)) := by
  apply TensorProduct.ext'
  intro x y
  change externalProductAlgHom cup hMul f g fDegree gDegree hf hg hComm
      (homogeneousInclusion (R := R) M p x ᵍ⊗ₜ[R] homogeneousInclusion (R := R) N q y) =
    homogeneousInclusion (R := R) P n (cup h (fDegree p x) (gDegree q y))
  exact externalProductAlgHom_homogeneous cup hMul f g fDegree gDegree hf hg hComm h x y

/-- No computed constructor occurs in this conclusion: Phi is the same given map. -/
theorem ExternalProductPureEq.toHomogeneousEq
    {Φ : GradedTensorProduct R (summandSubmodule (R := R) M)
      (summandSubmodule (R := R) N) →ₐ[R] DirectSum ℕ P}
    {f : DirectSum ℕ M →ₐ[R] DirectSum ℕ P}
    {g : DirectSum ℕ N →ₐ[R] DirectSum ℕ P}
    (hΦ : ExternalProductPureEq Φ f g)
    (cup : ∀ {i j d : ℕ}, i + j = d → P i →ₗ[R] P j →ₗ[R] P d)
    (hMul : ∀ {i j : ℕ} (x : P i) (y : P j),
      homogeneousInclusion (R := R) P i x * homogeneousInclusion (R := R) P j y =
        homogeneousInclusion (R := R) P (i + j) (cup rfl x y))
    (fDegree : ∀ i, M i →ₗ[R] P i) (gDegree : ∀ j, N j →ₗ[R] P j)
    (hf : ∀ i (x : M i), f (homogeneousInclusion (R := R) M i x) =
      homogeneousInclusion (R := R) P i (fDegree i x))
    (hg : ∀ j (y : N j), g (homogeneousInclusion (R := R) N j y) =
      homogeneousInclusion (R := R) P j (gDegree j y))
    (e : ∀ {i j d : ℕ}, i + j = d → M i →ₗ[R] N j →ₗ[R] P d)
    (he : ∀ {i j d : ℕ} (h : i + j = d) (x : M i) (y : N j),
      e h x y = cup h (fDegree i x) (gDegree j y)) :
    ExternalProductHomogeneousEq Φ e := by
  intro i j d h x y
  have h₁ := hΦ.apply (homogeneousInclusion (R := R) M i x)
    (homogeneousInclusion (R := R) N j y)
  have h₂ := congrArg₂ (fun a b : DirectSum ℕ P => a * b) (hf i x) (hg j y)
  have h₃ := (externalProduct_inclusion_cup cup hMul h (fDegree i x) (gDegree j y)).symm
  have h₄ := congrArg (homogeneousInclusion (R := R) P d) (he h x y).symm
  exact h₁.trans (h₂.trans (h₃.trans h₄))

/-- The same Phi and same actual source map also give the literal tensor equation. -/
theorem ExternalProductHomogeneousEq.tensorWithSource
    {Φ : GradedTensorProduct R (summandSubmodule (R := R) M)
      (summandSubmodule (R := R) N) →ₐ[R] DirectSum ℕ P}
    {e : ∀ {i j d : ℕ}, i + j = d → M i →ₗ[R] N j →ₗ[R] P d}
    (hΦ : ExternalProductHomogeneousEq Φ e)
    (s : (DirectSum ℕ M ⊗[R] DirectSum ℕ N) →ₗ[R]
      GradedTensorProduct R (summandSubmodule (R := R) M) (summandSubmodule (R := R) N))
    (hs : ∀ (a : DirectSum ℕ M) (b : DirectSum ℕ N), s (a ⊗ₜ[R] b) = a ᵍ⊗ₜ[R] b)
    {i j d : ℕ} (h : i + j = d)
    (T : M i ⊗[R] N j →ₗ[R] P d)
    (hT : ∀ (x : M i) (y : N j), T (x ⊗ₜ[R] y) = e h x y) :
    Φ.toLinearMap ∘ₗ s ∘ₗ TensorProduct.map
        (homogeneousInclusion (R := R) M i) (homogeneousInclusion (R := R) N j) =
      homogeneousInclusion (R := R) P d ∘ₗ T := by
  apply TensorProduct.ext'
  intro x y
  have h₁ := congrArg Φ (hs (homogeneousInclusion (R := R) M i x)
    (homogeneousInclusion (R := R) N j y))
  have h₂ := hΦ.apply h x y
  have h₃ := congrArg (homogeneousInclusion (R := R) P d) (hT x y).symm
  have hFinal := h₁.trans (h₂.trans h₃)
  simpa only [LinearMap.comp_apply, TensorProduct.map_tmul,
    AlgHom.toLinearMap_apply] using hFinal


section CanonicalInverse

variable
  (φ : GradedTensorProduct R (summandSubmodule (R := R) M)
    (summandSubmodule (R := R) N) →ₐ[R] DirectSum ℕ P)
  (e : (DirectSum ℕ M ⊗[R] DirectSum ℕ N) ≃ₗ[R] DirectSum ℕ P)
  (he : φ.toLinearMap ∘ₗ (externalProductSourceEquiv (R := R) (M := M) (N := N)).toLinearMap =
    e.toLinearMap)

include he in
/-- The one given linear equivalence has exactly the original signed forward map. -/
theorem externalProductLinearEquiv_apply
    (a : GradedTensorProduct R (summandSubmodule (R := R) M)
      (summandSubmodule (R := R) N)) :
    ((externalProductSourceEquiv (R := R) (M := M) (N := N)).symm.trans e) a = φ a := by
  have hNative := LinearMap.congr_fun he
    ((externalProductSourceEquiv (R := R) (M := M) (N := N)).symm a)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply] at hNative
  exact hNative.symm

/-- Promote the one original inverse; no second bijective-map inverse is selected. -/
def externalProductAlgEquiv :
    GradedTensorProduct R (summandSubmodule (R := R) M)
      (summandSubmodule (R := R) N) ≃ₐ[R] DirectSum ℕ P :=
  AlgEquiv.ofLinearEquiv
    ((externalProductSourceEquiv (R := R) (M := M) (N := N)).symm.trans e)
    (by rw [externalProductLinearEquiv_apply φ e he, map_one])
    (by
      intro a b
      rw [externalProductLinearEquiv_apply φ e he, externalProductLinearEquiv_apply φ e he,
        externalProductLinearEquiv_apply φ e he, map_mul])

/-- The full forward algebra homomorphism remains the given original map. -/
theorem externalProductAlgEquiv_toAlgHom :
    (externalProductAlgEquiv φ e he).toAlgHom = φ := by
  apply AlgHom.ext
  intro a
  exact externalProductLinearEquiv_apply φ e he a

/-- The inverse is the given original inverse followed by the existing source identification. -/
theorem externalProductAlgEquiv_symm_apply (z : DirectSum ℕ P) :
    (externalProductAlgEquiv φ e he).symm z =
      externalProductSourceEquiv (R := R) (M := M) (N := N) (e.symm z) := rfl


end CanonicalInverse

end DirectSum
