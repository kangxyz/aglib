/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.Filtration.Exhaustion
public import Mathlib.CategoryTheory.Limits.Shapes.Preorder.WellOrderContinuous

/-!
# Full-predecessor continuity of the exhaustive source filtration

The canonical comparison from the colimit of all predecessors is monic at
every stage. At limit stages its canonical cocone is a colimit. Both claims
refer to the complete predecessor diagram, not pairwise transition maps.
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.IsGrothendieckAbelian
  HomologicalComplex

namespace CategoryTheory.IsGrothendieckAbelian

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {M : C} {J : Type w} [LinearOrder J]

/-- For an actual increasing subobject diagram, the full predecessor colimit
maps monomorphically into each stage, including the empty predecessor case. -/
lemma mono_predecessor_comparison (F : J ⥤ MonoOver M) (j : J) :
    Mono (colimit.desc _ ((Set.principalSegIio j).cocone
      (F ⋙ MonoOver.forget M ⋙ Over.forget M))) := by
  classical
  let P := (Set.principalSegIio j).monotone.functor ⋙ F
  let D := P ⋙ MonoOver.forget M ⋙ Over.forget M
  let c := (Set.principalSegIio j).cocone (F ⋙ MonoOver.forget M ⋙ Over.forget M)
  let u : colimit D ⟶ (F.obj j).obj.left := colimit.desc D c
  change Mono u
  cases isEmpty_or_nonempty (Set.Iio j) with
  | inl h =>
    have hz : IsZero (colimit D) := by
      rw [IsZero.iff_id_eq_zero]
      apply colimit.hom_ext
      intro k
      exact isEmptyElim k
    exact hz.mono u
  | inr h =>
    let f := u ≫ (F.obj j).obj.hom
    have : Mono f := mono_of_isColimit_monoOver P (colimit.isColimit D) f (by
      intro k
      change colimit.ι D k ≫ colimit.desc D c ≫ (F.obj j).obj.hom =
        (F.obj k.val).obj.hom
      rw [colimit.ι_desc_assoc]
      exact MonoOver.w (F.map (homOfLE k.property.le)))
    exact mono_of_mono u (F.obj j).obj.hom

end CategoryTheory.IsGrothendieckAbelian

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {G : C} (hG : IsSeparator G) (M : CochainComplex C ℤ) (hM : M.Acyclic)
  {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]

/-- The coherent native complex diagram underlying the acyclic stages. -/
def acyclicComplexStages : J ⥤ CochainComplex C ℤ :=
  acyclicStagesFunctor hG M hM ⋙ MonoOver.forget M ⋙ Over.forget M

instance acyclicComplexStages_isWellOrderContinuous :
    (acyclicComplexStages hG M hM (J := J)).IsWellOrderContinuous where
  nonempty_isColimit j hj := ⟨by
    have : Nonempty (Set.Iio j) := ⟨⟨⊥, hj.bot_lt⟩⟩
    let F := acyclicStagesFunctor hG M hM (J := J)
    let c := (Set.principalSegIio j).cocone (F ⋙ MonoOver.forget M)
    have : Mono c.pt.hom := inferInstanceAs (Mono (acyclicStages hG M hM j).arrow)
    change IsColimit ((Over.forget M).mapCocone c)
    apply isColimitMapCoconeOfSubobjectMkEqISup
      ((Set.principalSegIio j).monotone.functor ⋙ F) c
    change Subobject.mk (acyclicStages hG M hM j).arrow =
      ⨆ x : Set.Iio j, Subobject.mk (acyclicStages hG M hM x.val).arrow
    simp only [Subobject.mk_arrow]
    exact transfiniteIterate_limit (acyclicGrowth hG M hM) ⊥ j hj⟩

lemma acyclicComplexStages_predecessor_mono (j : J) :
    Mono (colimit.desc _ ((Set.principalSegIio j).cocone
      (acyclicComplexStages hG M hM))) :=
  mono_predecessor_comparison (acyclicStagesFunctor hG M hM) j

end CochainComplex
