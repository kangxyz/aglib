/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Algebra.Homology.Embedding.StupidTrunc
public import Aglib.Algebra.Homology.CochainComplex.DegreewiseSplitMono
/-! # Original brutal truncations and their actual inclusions

The complexes and functors are mathlib's existing restriction/extension-based
stupid truncations. This supplies the missing canonical inclusion, retaining
the existing degreewise identifications and original chain-map components.
No boundedness, projectivity, or term-subcategory assumption is made.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe v u w w'
namespace HomologicalComplex
variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The original degreewise identifications commute with every differential. -/
theorem stupidTruncXIso_hom_d {I : Type w} {J : Type w'}
    {c : ComplexShape I} {c' : ComplexShape J} (K : HomologicalComplex A c')
    (e : c.Embedding c') [e.IsRelIff] {a b : I} {i j : J}
    (hi : e.f a = i) (hj : e.f b = j) :
    (K.stupidTruncXIso e hi).hom ≫ K.d i j =
      (K.stupidTrunc e).d i j ≫ (K.stupidTruncXIso e hj).hom := by
  subst i j
  simp only [stupidTruncXIso, Iso.trans_hom, eqToIso_refl, Iso.refl_hom, Category.comp_id]
  rw [show (K.stupidTrunc e).d (e.f a) (e.f b) =
      ((K.restriction e).extendXIso e rfl).hom ≫ (K.restriction e).d a b ≫
        ((K.restriction e).extendXIso e rfl).inv from
    (K.restriction e).extend_d_eq e rfl rfl]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

end HomologicalComplex

namespace CochainComplex
variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The existing brutal truncation in degrees at least n. -/
abbrev stupidTruncGE (K : CochainComplex A ℤ) (n : ℤ) :=
  K.stupidTrunc (ComplexShape.embeddingUpIntGE n)

/-- The existing restriction/extension functor, unchanged. -/
abbrev stupidTruncGEFunctor (n : ℤ) : CochainComplex A ℤ ⥤ CochainComplex A ℤ :=
  (ComplexShape.embeddingUpIntGE n).stupidTruncFunctor A

/-- The original term identification in a retained degree. -/
def stupidTruncGEXIso (K : CochainComplex A ℤ) (n i : ℤ) (hi : n ≤ i) :
    (stupidTruncGE K n).X i ≅ K.X i :=
  K.stupidTruncXIso (ComplexShape.embeddingUpIntGE n)
    (show n + ((i - n).toNat : ℤ) = i by omega)

/-- The discarded terms are actual zero objects. -/
theorem stupidTruncGE_isZero_X (K : CochainComplex A ℤ) (n i : ℤ) (hi : i < n) :
    IsZero ((stupidTruncGE K n).X i) :=
  K.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE n) i
    ((ComplexShape.notMem_range_embeddingUpIntGE_iff n i).2 hi)

/-- Components of the original canonical inclusion. -/
def stupidTruncGEInclusionF (K : CochainComplex A ℤ) (n i : ℤ) :
    (stupidTruncGE K n).X i ⟶ K.X i :=
  if hi : n ≤ i then (stupidTruncGEXIso K n i hi).hom else 0

/-- The actual chain-map inclusion of the existing brutal truncation. -/
def stupidTruncGEInclusion (K : CochainComplex A ℤ) (n : ℤ) : stupidTruncGE K n ⟶ K where
  f := stupidTruncGEInclusionF K n
  comm' i j hij := by
    by_cases hi : n ≤ i
    · have hj : n ≤ j := by change i + 1 = j at hij; omega
      simp only [stupidTruncGEInclusionF, dite_eq_left hi, dite_eq_left hj]
      exact stupidTruncXIso_hom_d K (ComplexShape.embeddingUpIntGE n) _ _
    · exact (stupidTruncGE_isZero_X K n i (by omega)).eq_of_src _ _

@[simp]
theorem stupidTruncGEInclusion_f_of_le (K : CochainComplex A ℤ) (n i : ℤ) (hi : n ≤ i) :
    (stupidTruncGEInclusion K n).f i = (stupidTruncGEXIso K n i hi).hom := by
  simp only [stupidTruncGEInclusion, stupidTruncGEInclusionF, dite_eq_left hi]

/-- Naturality uses precisely the original stupid-truncation map. -/
@[reassoc]
theorem stupidTruncGEInclusion_naturality {K L : CochainComplex A ℤ}
    (f : K ⟶ L) (n : ℤ) :
    (stupidTruncGEFunctor n).map f ≫ stupidTruncGEInclusion L n =
      stupidTruncGEInclusion K n ≫ f := by
  ext i
  by_cases hi : n ≤ i
  · simpa only [comp_f, stupidTruncGEInclusion_f_of_le K n i hi,
      stupidTruncGEInclusion_f_of_le L n i hi, stupidTruncGEXIso,
      stupidTruncGEFunctor, ComplexShape.Embedding.stupidTruncFunctor_map] using
      stupidTruncMap_stupidTruncXIso_hom f (ComplexShape.embeddingUpIntGE n)
        (show n + ((i - n).toNat : ℤ) = i by omega)
  · exact (stupidTruncGE_isZero_X K n i (by omega)).eq_of_src _ _

/-- The original inclusion as a natural transformation of the existing functor. -/
def stupidTruncGEInclusionNat (n : ℤ) : stupidTruncGEFunctor (A := A) n ⟶ 𝟭 _ where
  app K := stupidTruncGEInclusion K n
  naturality _ _ f := stupidTruncGEInclusion_naturality f n

/-- The original inclusion is split in every degree, without requiring a
chain-map retraction or any projectivity assumption. -/
theorem stupidTruncGEInclusion_degreewiseSplitMono (K : CochainComplex A ℤ) (n : ℤ) :
    degreewiseSplitMono (stupidTruncGEInclusion K n) := by
  intro i
  by_cases hi : n ≤ i
  · rw [stupidTruncGEInclusion_f_of_le K n i hi]
    infer_instance
  · exact IsSplitMono.mk' ⟨0, (stupidTruncGE_isZero_X K n i (by omega)).eq_of_src _ _⟩

end CochainComplex
