/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
# Native homology sequences of the original signed mapping cone

The displayed short complexes use the original homology maps of the cone
triangle and Mathlib's actual triangle connecting map. Its genuine
distinguished-triangle exactness gives the top-degree cancellation criterion.
The native standard derived localization is used only inside proofs of these
chain-level statements; no chosen derived-category instance is a premise.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CochainComplex.mappingCone

variable {C : Type u} [Category.{v} C] [Abelian C]
  {K L : CochainComplex C ℤ} (φ : K ⟶ L)

/-- The original `Hⁱ(K) → Hⁱ(L) → Hⁱ(Cone φ)` portion of the
native signed cone triangle's homology sequence. -/
@[simps! X₁ X₂ X₃ f g]
def homologyLeftShortComplex (i : ℤ) : ShortComplex C := by
  letI := HasDerivedCategory.standard C
  exact ShortComplex.mk (homologyMap φ i) (homologyMap (inr φ) i)
    (homologyMap_comp_eq_zero_of_distTriang (triangle φ)
      (DerivedCategory.mappingCone_triangle_distinguished φ) i)

/-- Exactness concerns the original two homology maps, with no cone
comparison or cohomology-model premise. -/
theorem homologyLeftShortComplex_exact (i : ℤ) :
    (homologyLeftShortComplex φ i).Exact := by
  let := HasDerivedCategory.standard C
  exact homologyMap_exact₂_of_distTriang (triangle φ)
    (DerivedCategory.mappingCone_triangle_distinguished φ) i

/-- The original `Hⁱ(L) → Hⁱ(Cone φ) → Hⁱ⁺¹(K)` portion, with
Mathlib's native triangle connecting map and its original sign. -/
@[simps! X₁ X₂ X₃ f g]
def homologyRightShortComplex (i : ℤ) : ShortComplex C := by
  letI := HasDerivedCategory.standard C
  exact ShortComplex.mk (homologyMap (inr φ) i)
    (homologyδOfTriangle (triangle φ) i (i + 1))
    (homologyMap_homologyδOfTriangle (triangle φ)
      (DerivedCategory.mappingCone_triangle_distinguished φ) i (i + 1))

/-- The native right portion of the cone homology sequence is exact. -/
theorem homologyRightShortComplex_exact (i : ℤ) :
    (homologyRightShortComplex φ i).Exact := by
  let := HasDerivedCategory.standard C
  exact homologyMap_exact₃_of_distTriang (triangle φ)
    (DerivedCategory.mappingCone_triangle_distinguished φ) i (i + 1)

/-- Surjectivity on the actual degree-`i` homology kills the cone's
degree-`i` homology when the next original source homology vanishes. -/
theorem isZero_homology_of_epi (i : ℤ) [Epi (homologyMap φ i)]
    (hK : IsZero (K.homology (i + 1))) : IsZero ((mappingCone φ).homology i) := by
  have he : Epi (homologyLeftShortComplex φ i).f := by
    change Epi (homologyMap φ i)
    infer_instance
  have hz : homologyMap (inr φ) i = 0 :=
    (homologyLeftShortComplex_exact φ i).epi_f_iff.mp he
  exact (homologyRightShortComplex_exact φ i).isZero_X₂ hz (hK.eq_of_tgt _ _)

/-- A map between complexes cohomologically at most `n` which surjects
on their original top homology has cone cohomologically at most `n-1`.
No termwise bound, flatness or module finiteness is assumed. -/
theorem isLE_of_epi_top (n : ℤ) [K.IsLE n] [L.IsLE n] [Epi (homologyMap φ n)] :
    (mappingCone φ).IsLE (n - 1) := by
  rw [isLE_iff]
  intro i hi
  rw [exactAt_iff_isZero_homology]
  by_cases hin : i = n
  · subst i
    exact isZero_homology_of_epi φ n
      ((K.exactAt_of_isLE n (n + 1) (by omega)).isZero_homology)
  · have hL := (L.exactAt_of_isLE n i (by omega)).isZero_homology
    have hK := (K.exactAt_of_isLE n (i + 1) (by omega)).isZero_homology
    exact (homologyRightShortComplex_exact φ i).isZero_X₂
      (hL.eq_of_src _ _) (hK.eq_of_tgt _ _)

end CochainComplex.mappingCone
