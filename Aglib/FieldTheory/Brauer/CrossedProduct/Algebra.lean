/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.Brauer.CrossedProduct.MatrixOperators
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# The crossed product as a native matrix subalgebra

The span of diagonal-times-translation matrices is closed under multiplication
by the cocycle relation. Thus it is a genuine subalgebra of a native matrix
algebra, without imposing new multiplication or associativity axioms.
-/

@[expose] public noncomputable section

namespace groupCohomology.CrossedProduct

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [Fintype (L ≃ₐ[K] L)] [DecidableEq (L ≃ₐ[K] L)]

/-- The diagonal Galois embedding as a homomorphism of base-field algebras. -/
def diagonalHom : L →ₐ[K] Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) L := by
  classical
  exact (Matrix.diagonalAlgHom K).comp (AlgHom.pi fun σ => σ.toAlgHom)

@[simp]
theorem diagonalHom_apply (a : L) : diagonalHom (K := K) a = diagonal a := rfl

/-- The generating matrices with one coefficient and one group index. -/
def term (c : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ) (a : L) (g : L ≃ₐ[K] L) :
    Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) L := diagonal a * translation c g

/-- Product of two generating matrices, with its actual twisted coefficient. -/
theorem term_mul_term
    {c : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ} (hc : IsMulCocycle₂ c)
    (a b : L) (g h : L ≃ₐ[K] L) :
    term c a g * term c b h = term c (a * g b * (c (g, h) : L)) (g * h) := by
  unfold term
  calc
    diagonal a * translation c g * (diagonal b * translation c h) =
        diagonal a * (translation c g * diagonal b) * translation c h := by
          simp only [mul_assoc]
    _ = diagonal a * (diagonal (g b) * translation c g) * translation c h := by
          rw [translation_mul_diagonal]
    _ = (diagonal a * diagonal (g b)) *
        (diagonal (c (g, h) : L) * translation c (g * h)) := by
          rw [← translation_mul_translation hc]
          simp only [mul_assoc]
    _ = diagonal (a * g b * (c (g, h) : L)) * translation c (g * h) := by
          have hd (x y : L) : diagonal (K := K) (x * y) = diagonal x * diagonal y :=
            (diagonalHom (K := K)).map_mul x y
          rw [hd, hd]
          simp only [mul_assoc]

/-- The underlying base-field submodule of the crossed product. -/
def carrier (c : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ) :
    Submodule K (Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) L) :=
  Submodule.span K (Set.range fun p : L × (L ≃ₐ[K] L) => term c p.1 p.2)

theorem term_mem_carrier (c : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ)
    (a : L) (g : L ≃ₐ[K] L) : term c a g ∈ carrier c :=
  Submodule.subset_span ⟨(a, g), rfl⟩

/-- The literal span is multiplicatively closed. -/
theorem mul_mem_carrier
    {c : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ} (hc : IsMulCocycle₂ c)
    {x y : Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) L}
    (hx : x ∈ carrier c) (hy : y ∈ carrier c) : x * y ∈ carrier c := by
  apply LinearMap.BilinMap.apply_apply_mem_of_mem_span (carrier c) _ _
    (LinearMap.mul K _) ?_ x y hx hy
  rintro _ ⟨⟨a, g⟩, rfl⟩ _ ⟨⟨b, h⟩, rfl⟩
  change term c a g * term c b h ∈ carrier c
  rw [term_mul_term hc]
  exact term_mem_carrier c _ _

/-- The actual crossed-product subalgebra associated to a normalized cocycle. -/
def algebra
    {c : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ} (hc : IsMulCocycle₂ c)
    (h₁ : c (1, 1) = 1) :
    Subalgebra K (Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) L) where
  carrier := carrier c
  add_mem' := (carrier c).add_mem
  mul_mem' := mul_mem_carrier hc
  algebraMap_mem' r := by
    change algebraMap K (Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) L) r ∈ carrier c
    have h := term_mem_carrier c (algebraMap K L r) 1
    simpa only [term, translation_one hc h₁, mul_one,
      ← diagonalHom_apply, AlgHom.commutes] using h

end groupCohomology.CrossedProduct
