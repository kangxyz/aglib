/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.Brauer.CrossedProduct.Simple

/-!
# Extracting a primitive from a one-dimensional crossed-product action

On a one-dimensional extension-field vector space, the invertible translation
operators act on a basis vector by nonzero coefficients. Their actual product
law is exactly the native multiplicative coboundary equation.
-/

@[expose] public noncomputable section

namespace groupCohomology.CrossedProduct

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [Fintype (L ≃ₐ[K] L)] [DecidableEq (L ≃ₐ[K] L)]
variable {c : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ}
variable (hc : IsMulCocycle₂ c) (h₁ : c (1, 1) = 1)

/-- The primitive is constructed from coefficients of genuine operators.
The scalar compatibility hypothesis identifies the given extension-field action
with the actual diagonal subfield of the crossed product. -/
theorem isMulCoboundary₂_of_oneDimensional_action
    (V : Type*) [AddCommGroup V] [Module K V] [Module L V]
    (hV : Module.finrank L V = 1)
    (f : algebra hc h₁ →+* Module.End K V)
    (hscalar : ∀ (a : L) (v : V), f (diagonalEmbedding hc h₁ a) v = a • v) :
    IsMulCoboundary₂ c := by
  obtain ⟨v, hv, hspan⟩ := (finrank_eq_one_iff').mp hV
  let T (g : L ≃ₐ[K] L) : Module.End K V := f (translationElement hc h₁ g)
  choose b hb using fun g : L ≃ₐ[K] L => hspan (T g v)
  have hbne (g : L ≃ₐ[K] L) : b g ≠ 0 := by
    intro hzero
    have hinj := ((Module.End.isUnit_iff _).mp ((isUnit_translation hc h₁ g).map f)).injective
    apply hv
    apply hinj
    have h := hb g
    rw [hzero, zero_smul] at h
    exact h.symm.trans (map_zero _).symm
  have hsemilinear (g : L ≃ₐ[K] L) (a : L) (w : V) : T g (a • w) = g a • T g w := by
    rw [← hscalar a w, ← hscalar (g a) (T g w)]
    change (f (translationElement hc h₁ g) * f (diagonalEmbedding hc h₁ a)) w =
      (f (diagonalEmbedding hc h₁ (g a)) * f (translationElement hc h₁ g)) w
    rw [← map_mul, ← map_mul]
    congr 2
    apply Subtype.ext
    exact translation_mul_diagonal c g a
  have hprod (g h : L ≃ₐ[K] L) : g (b h) * b g = (c (g, h) : L) * b (g * h) := by
    apply smul_left_injective L hv
    calc
      (g (b h) * b g) • v = T g (T h v) := by
        rw [mul_smul, hb, ← hsemilinear, hb]
      _ = (c (g, h) : L) • T (g * h) v := by
        change (f (translationElement hc h₁ g) * f (translationElement hc h₁ h)) v = _
        rw [← map_mul]
        have he : translationElement hc h₁ g * translationElement hc h₁ h =
            diagonalEmbedding hc h₁ (c (g, h) : L) * translationElement hc h₁ (g * h) := by
          apply Subtype.ext
          exact translation_mul_translation hc g h
        rw [he, map_mul]
        exact hscalar _ _
      _ = ((c (g, h) : L) * b (g * h)) • v := by rw [mul_smul, hb]
  refine ⟨fun g => Units.mk0 (b g) (hbne g), ?_⟩
  intro g h
  apply Units.ext
  simp only [Units.val_mul, Units.val_div_eq_div_val, AlgEquiv.smul_units_def,
    Units.coe_map, Units.val_mk0]
  change g (b h) / b (g * h) * b g = (c (g, h) : L)
  rw [div_mul_eq_mul_div]
  exact (div_eq_iff (hbne (g * h))).mpr (hprod g h)

end groupCohomology.CrossedProduct
