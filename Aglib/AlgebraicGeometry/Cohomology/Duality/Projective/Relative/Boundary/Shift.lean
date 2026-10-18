/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Boundary

/-!
# The native sign in the coefficient trace boundary

The target triangle shifted by k multiplies all three arrows by (-1)^k.
Rescaling only the middle trace component makes TR3 applicable. Its third
component is the prescribed top trace, and the resulting boundary equality
retains the sign and the native shift-commutation isomorphism explicitly.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v w

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- Vanishing above the first vertex's upper bound gives a heart epimorphism. -/
theorem epi_homology_mor₂_of_first_isLE
    (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang (DerivedCategory C))
    (n : ℤ) [T.obj₁.IsLE n] : Epi ((homologyFunctor C n).map T.mor₂) := by
  have hz := isZero_of_isLE T.obj₁ n (n + 1) (by omega)
  change Epi (((homologyFunctor C 0).shift n).map T.mor₂)
  exact ((homologyFunctor C 0).homologySequence_epi_shift_map_mor₂_iff
    T hT n (n + 1) rfl).mpr (hz.eq_of_tgt _ _)

/-- The two unsigned trace squares force the correctly signed boundary square. -/
theorem triangle_shift_comm₃_of_epi_topHomology
    (T₁ T₂ : Triangle (DerivedCategory C))
    (hT₁ : T₁ ∈ distTriang (DerivedCategory C))
    (hT₂ : T₂ ∈ distTriang (DerivedCategory C))
    (n k : ℤ) [T₁.obj₁.IsLE n] [T₁.obj₂.IsLE n] [T₁.obj₃.IsLE n]
    (V : C) (e : T₂.obj₃⟦k⟧ ≅ (singleFunctor C n).obj V)
    (a : T₁.obj₁ ⟶ T₂.obj₁⟦k⟧) (b : T₁.obj₂ ⟶ T₂.obj₂⟦k⟧)
    (c : T₁.obj₃ ⟶ T₂.obj₃⟦k⟧)
    (h₁ : T₁.mor₁ ≫ b = a ≫ T₂.mor₁⟦k⟧')
    (h₂ : T₁.mor₂ ≫ c = b ≫ T₂.mor₂⟦k⟧') :
    T₁.mor₃ ≫ a⟦1⟧' =
      c ≫ (k.negOnePow • T₂.mor₃⟦k⟧' ≫
        (shiftFunctorComm (DerivedCategory C) 1 k).hom.app T₂.obj₁) := by
  let := epi_homology_mor₂_of_first_isLE T₁ hT₁ n
  apply triangle_comm₃_of_epi_topHomology T₁ ((Triangle.shiftFunctor _ k).obj T₂)
    hT₁ (Triangle.shift_distinguished T₂ hT₂ k) n V e a (k.negOnePow • b) c
  · change T₁.mor₁ ≫ (k.negOnePow • b) = a ≫ (k.negOnePow • T₂.mor₁⟦k⟧')
    simpa only [Linear.comp_units_smul] using congrArg (fun z => k.negOnePow • z) h₁
  · change T₁.mor₂ ≫ c = (k.negOnePow • b) ≫ (k.negOnePow • T₂.mor₂⟦k⟧')
    simpa only [Linear.units_smul_comp, Linear.comp_units_smul, smul_smul,
      Int.units_mul_self, one_smul] using h₂

end DerivedCategory
