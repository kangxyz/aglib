/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-!
# Original truncation maps under finite upper amplitude

A uniform upper amplitude makes the original lower-truncation projection a
homology isomorphism in every retained output degree. Consequently a natural
transformation between two such triangulated functors is invertible everywhere
if it is invertible on bounded-below objects. The transformation need not be
shift-compatible. No resolution model or geometric cohomological bound is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v w u' v' w'

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  (F : DerivedCategory C ⥤ DerivedCategory D) [F.CommShift ℤ] [F.IsTriangulated]

/-- Finite upper amplitude preserves the retained homology of the original
lower-truncation projection, without a lower bound on the input object. -/
theorem isIso_homology_map_truncGEπ_of_upper_amplitude
    (N : ℤ) (hF : ∀ (X : DerivedCategory C) (n : ℤ),
      X.IsLE n → (F.obj X).IsLE (n + N))
    (K : DerivedCategory C) (m q : ℤ) (hmq : m + N ≤ q) :
    IsIso ((homologyFunctor D q).map (F.map ((TStructure.t.truncGEπ m).app K))) := by
  let T := (TStructure.t.triangleLTGE m).obj K
  let U := F.mapTriangle.obj T
  have hU := F.map_distinguished T (TStructure.t.triangleLTGE_distinguished m K)
  let : U.obj₁.IsLE (m - 1 + N) := hF T.obj₁ (m - 1) inferInstance
  have h₀ := isZero_of_isLE U.obj₁ (m - 1 + N) q (by omega)
  have hnext := isZero_of_isLE U.obj₁ (m - 1 + N) (q + 1) (by omega)
  change IsIso (((homologyFunctor D 0).shift q).map U.mor₂)
  let : Mono (((homologyFunctor D 0).shift q).map U.mor₂) :=
    ((homologyFunctor D 0).homologySequence_mono_shift_map_mor₂_iff U hU q).mpr
      (h₀.eq_of_src _ _)
  let : Epi (((homologyFunctor D 0).shift q).map U.mor₂) :=
    ((homologyFunctor D 0).homologySequence_epi_shift_map_mor₂_iff
      U hU q (q + 1) rfl).mpr (hnext.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- A natural transformation of finite-upper-amplitude triangulated functors
is invertible if its components on all bounded-below objects are invertible.
No compatibility of the transformation with shifts is required. -/
theorem isIso_natTrans_of_upper_amplitude_of_boundedBelow
    {G : DerivedCategory C ⥤ DerivedCategory D} [G.CommShift ℤ] [G.IsTriangulated]
    (η : F ⟶ G) (NF NG : ℤ)
    (hF : ∀ (X : DerivedCategory C) (n : ℤ), X.IsLE n → (F.obj X).IsLE (n + NF))
    (hG : ∀ (X : DerivedCategory C) (n : ℤ), X.IsLE n → (G.obj X).IsLE (n + NG))
    (hη : ∀ (X : DerivedCategory C) (n : ℤ), X.IsGE n → IsIso (η.app X)) :
    IsIso η := by
  have hηX (K : DerivedCategory C) : IsIso (η.app K) := by
    rw [isIso_iff]
    intro q
    let m : ℤ := q - max NF NG
    let L := (TStructure.t.truncGE m).obj K
    let π : K ⟶ L := (TStructure.t.truncGEπ m).app K
    let H := homologyFunctor D q
    let : IsIso (η.app L) := hη L m inferInstance
    let : IsIso (H.map (F.map π)) :=
      isIso_homology_map_truncGEπ_of_upper_amplitude F NF hF K m q (by dsimp [m]; omega)
    let : IsIso (H.map (G.map π)) :=
      isIso_homology_map_truncGEπ_of_upper_amplitude G NG hG K m q (by dsimp [m]; omega)
    have heq : H.map (η.app K) =
        H.map (F.map π) ≫ H.map (η.app L) ≫ inv (H.map (G.map π)) := by
      apply (cancel_mono (H.map (G.map π))).mp
      simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
      simpa only [Functor.map_comp] using (congrArg H.map (η.naturality π)).symm
    change IsIso (H.map (η.app K))
    rw [heq]
    infer_instance
  exact NatIso.isIso_of_isIso_app η

end DerivedCategory
