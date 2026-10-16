/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.TStructure.Homology
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-!
# Original homology of native bounded-below truncations

The native truncation arrows induce isomorphisms on exactly their retained
homology degrees. The single-layer comparison is the fully faithful
bounded-below lift of the unique homology-normalized native comparison.
No term bound or injective representative is a premise.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v w

namespace DerivedCategory.Plus

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- A distinguished triangle's first arrow preserves homology below the third
object's lower bound. The assertion concerns the original arrow. -/
theorem isIso_homology_mor₁_of_isGE (T : Triangle (Plus C))
    (hT : T ∈ distTriang _) (a i : ℤ) [T.obj₃.IsGE a] (hi : i < a) :
    IsIso ((homologyFunctor C i).map T.mor₁) := by
  have h₀ := isZero_homology_of_isGE T.obj₃ a i hi
  have hprev := isZero_homology_of_isGE T.obj₃ a (i - 1) (by omega)
  change IsIso (((homologyFunctor C 0).shift i).map T.mor₁)
  let : Epi (((homologyFunctor C 0).shift i).map T.mor₁) :=
    ((homologyFunctor C 0).homologySequence_epi_shift_map_mor₁_iff T hT i).mpr
      (h₀.eq_of_tgt _ _)
  let : Mono (((homologyFunctor C 0).shift i).map T.mor₁) :=
    ((homologyFunctor C 0).homologySequence_mono_shift_map_mor₁_iff
      T hT (i - 1) i (by omega)).mpr (hprev.eq_of_src _ _)
  exact isIso_of_mono_of_epi _

/-- A distinguished triangle's second arrow preserves homology above the first
object's upper bound. The assertion concerns the original arrow. -/
theorem isIso_homology_mor₂_of_isLE (T : Triangle (Plus C))
    (hT : T ∈ distTriang _) (a i : ℤ) [T.obj₁.IsLE a] (hi : a < i) :
    IsIso ((homologyFunctor C i).map T.mor₂) := by
  have h₀ := isZero_homology_of_isLE T.obj₁ a i hi
  have hnext := isZero_homology_of_isLE T.obj₁ a (i + 1) (by omega)
  change IsIso (((homologyFunctor C 0).shift i).map T.mor₂)
  let : Mono (((homologyFunctor C 0).shift i).map T.mor₂) :=
    ((homologyFunctor C 0).homologySequence_mono_shift_map_mor₂_iff T hT i).mpr
      (h₀.eq_of_src _ _)
  let : Epi (((homologyFunctor C 0).shift i).map T.mor₂) :=
    ((homologyFunctor C 0).homologySequence_epi_shift_map_mor₂_iff
      T hT i (i + 1) rfl).mpr (hnext.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- The original upper truncation inclusion preserves every retained native homology. -/
theorem isIso_homology_truncLTι (K : Plus C) (a i : ℤ) (hi : i < a) :
    IsIso ((homologyFunctor C i).map ((TStructure.t.truncLTι a).app K)) :=
  isIso_homology_mor₁_of_isGE ((TStructure.t.triangleLTGE a).obj K)
    (TStructure.t.triangleLTGE_distinguished a K) a i hi

/-- The original lower truncation projection preserves every retained native homology. -/
theorem isIso_homology_truncGEπ (K : Plus C) (a i : ℤ) (hi : a ≤ i) :
    IsIso ((homologyFunctor C i).map ((TStructure.t.truncGEπ a).app K)) :=
  isIso_homology_mor₂_of_isLE ((TStructure.t.triangleLTGE a).obj K)
    (TStructure.t.triangleLTGE_distinguished a K) (a - 1) i (by omega)

/-- Homology of upper truncation, with the original inclusion as its forward map. -/
def homologyTruncLTIso (K : Plus C) (a i : ℤ) (hi : i < a) :
    (homologyFunctor C i).obj ((TStructure.t.truncLT a).obj K) ≅
      (homologyFunctor C i).obj K := by
  let := isIso_homology_truncLTι K a i hi
  exact asIso ((homologyFunctor C i).map ((TStructure.t.truncLTι a).app K))

/-- Homology of lower truncation, with the original projection as its forward map. -/
def homologyTruncGEIso (K : Plus C) (a i : ℤ) (hi : a ≤ i) :
    (homologyFunctor C i).obj K ≅
      (homologyFunctor C i).obj ((TStructure.t.truncGE a).obj K) := by
  let := isIso_homology_truncGEπ K a i hi
  exact asIso ((homologyFunctor C i).map ((TStructure.t.truncGEπ a).app K))

/-- The upper-truncation comparison retains the original inclusion on homology. -/
theorem homologyTruncLTIso_hom (K : Plus C) (a i : ℤ) (hi : i < a) :
    (homologyTruncLTIso K a i hi).hom =
      (homologyFunctor C i).map ((TStructure.t.truncLTι a).app K) := rfl

/-- The lower-truncation comparison retains the original projection on homology. -/
theorem homologyTruncGEIso_hom (K : Plus C) (a i : ℤ) (hi : a ≤ i) :
    (homologyTruncGEIso K a i hi).hom =
      (homologyFunctor C i).map ((TStructure.t.truncGEπ a).app K) := rfl

/-- The native single/homology comparison restricted to the bounded-below category. -/
def singleFunctorCompHomologyFunctorIso (n : ℤ) :
    singleFunctor C n ⋙ homologyFunctor C n ≅ 𝟭 C :=
  DerivedCategory.singleFunctorCompHomologyFunctorIso C n

/-- The bounded-below lift of the unique original-homology normalized comparison. -/
def isoSingleHomology (K : Plus C) (n : ℤ) [K.IsGE n] [K.IsLE n] :
    K ≅ (singleFunctor C n).obj ((homologyFunctor C n).obj K) :=
  (ι : Plus C ⥤ DerivedCategory C).preimageIso
    (DerivedCategory.isoSingleHomology (ι.obj K) n)

/-- The bounded-below comparison is exactly the normalized native derived comparison. -/
@[simp]
theorem ι_map_isoSingleHomology_hom (K : Plus C) (n : ℤ) [K.IsGE n] [K.IsLE n] :
    (ι : Plus C ⥤ DerivedCategory C).map (isoSingleHomology K n).hom =
      (DerivedCategory.isoSingleHomology (ι.obj K) n).hom :=
  (ι : Plus C ⥤ DerivedCategory C).map_preimage _

end DerivedCategory.Plus
