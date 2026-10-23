/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov.Layers
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four

/-!
# Divisibility through native truncations and triangles

Multiplication by n is an isomorphism on a lower truncation if it is an
isomorphism on every retained original homology object. A native triangle's
long exact sequence transfers this property using the ordinary five-lemma.
This is a narrow derived argument, not a replacement spectral sequence.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v w

namespace DerivedCategory.Plus

/-- Scalar invertibility is preserved by an actual object isomorphism. -/
theorem nsmul_isIso_transport {D : Type*} [Category D] [Preadditive D]
    {A B : D} (e : A ≅ B) (n : ℕ) [IsIso (n • 𝟙 A)] : IsIso (n • 𝟙 B) := by
  have h : n • 𝟙 B = e.inv ≫ (n • 𝟙 A) ≫ e.hom := by
    simp only [Preadditive.comp_nsmul, Preadditive.nsmul_comp, Category.id_comp,
      e.inv_hom_id]
  rw [h]
  infer_instance

private theorem nsmul_isIso_of_exact {D : Type*} [Category D] [Abelian D]
    (R : ComposableArrows D 4) (hR : R.Exact) (n : ℕ)
    [IsIso (n • 𝟙 (R.obj' 0))] [IsIso (n • 𝟙 (R.obj' 1))]
    [IsIso (n • 𝟙 (R.obj' 3))] [IsIso (n • 𝟙 (R.obj' 4))] :
    IsIso (n • 𝟙 (R.obj' 2)) := by
  exact Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono hR hR (n • 𝟙 R)
    (by change Epi (n • 𝟙 (R.obj' 0)); infer_instance)
    (by change IsIso (n • 𝟙 (R.obj' 1)); infer_instance)
    (by change IsIso (n • 𝟙 (R.obj' 3)); infer_instance)
    (by change Mono (n • 𝟙 (R.obj' 4)); infer_instance)

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- Original homology detects invertibility of n on the actual lower truncation. -/
theorem isIso_nsmul_id_truncGE (K : Plus C) (a : ℤ) (n : ℕ)
    (hn : ∀ i : ℤ, a ≤ i → IsIso (n • 𝟙 ((homologyFunctor C i).obj K))) :
    IsIso (n • 𝟙 ((TStructure.t.truncGE a).obj K)) := by
  apply (isIso_iff _).mpr
  intro i
  rw [CategoryTheory.Functor.map_nsmul, CategoryTheory.Functor.map_id]
  by_cases hi : a ≤ i
  · let := hn i hi
    exact nsmul_isIso_transport (homologyTruncGEIso K a i hi) n
  · have hz := isZero_homology_of_isGE ((TStructure.t.truncGE a).obj K) a i
      (lt_of_not_ge hi)
    exact isIso_of_source_target_iso_zero _ hz.isoZero hz.isoZero

/-- In the original triangle LES, invertibility on the four outer terms implies it
on the middle homology of the first object. -/
theorem isIso_nsmul_id_homology_obj₁
    (T : Triangle (Plus C)) (hT : T ∈ distTriang _) (i j : ℤ) (hij : i + 1 = j)
    (n : ℕ)
    [IsIso (n • 𝟙 ((homologyFunctor C i).obj T.obj₂))]
    [IsIso (n • 𝟙 ((homologyFunctor C i).obj T.obj₃))]
    [IsIso (n • 𝟙 ((homologyFunctor C j).obj T.obj₂))]
    [IsIso (n • 𝟙 ((homologyFunctor C j).obj T.obj₃))] :
    IsIso (n • 𝟙 ((homologyFunctor C j).obj T.obj₁)) := by
  let R := ((homologyFunctor C 0).homologySequenceComposableArrows₅ T i j hij).δ₀
  have hR : R.Exact :=
    ((homologyFunctor C 0).homologySequenceComposableArrows₅_exact T hT i j hij).δ₀
  let : IsIso (n • 𝟙 (R.obj' 0)) := by
    change IsIso (n • 𝟙 ((homologyFunctor C i).obj T.obj₂))
    infer_instance
  let : IsIso (n • 𝟙 (R.obj' 1)) := by
    change IsIso (n • 𝟙 ((homologyFunctor C i).obj T.obj₃))
    infer_instance
  let : IsIso (n • 𝟙 (R.obj' 3)) := by
    change IsIso (n • 𝟙 ((homologyFunctor C j).obj T.obj₂))
    infer_instance
  let : IsIso (n • 𝟙 (R.obj' 4)) := by
    change IsIso (n • 𝟙 ((homologyFunctor C j).obj T.obj₃))
    infer_instance
  exact nsmul_isIso_of_exact R hR n

/-- An additive functor preserves the actual multiplication-by-n isomorphism. -/
theorem isIso_nsmul_id_functor_obj {D : Type*} [Category D] [Preadditive D]
    (F : Plus C ⥤ D) [F.Additive] (K : Plus C) (n : ℕ) [IsIso (n • 𝟙 K)] :
    IsIso (n • 𝟙 (F.obj K)) := by
  have h : F.map (n • 𝟙 K) = n • 𝟙 (F.obj K) := by
    rw [CategoryTheory.Functor.map_nsmul, CategoryTheory.Functor.map_id]
  rw [← h]
  infer_instance

end DerivedCategory.Plus
