/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.PullbackComposition
public import Mathlib.CategoryTheory.Sites.Whiskering
/-! # Matching in a native presheaf from actual scheme overlaps -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u v w

/-- The actual scheme fiber product as an object of the original étale site. -/
def etaleOverlapChart {S : Scheme.{u}} (W V : S.Etale) : S.Etale :=
  Scheme.Etale.mk (pullback.fst W.hom V.hom ≫ W.hom)

/-- The original first projection of the scheme overlap. -/
def etaleOverlapFst {S : Scheme.{u}} (W V : S.Etale) : etaleOverlapChart W V ⟶ W :=
  MorphismProperty.Over.homMk (pullback.fst W.hom V.hom) rfl (by trivial)

/-- The original second projection of the scheme overlap. -/
def etaleOverlapSnd {S : Scheme.{u}} (W V : S.Etale) : etaleOverlapChart W V ⟶ V :=
  MorphismProperty.Over.homMk (pullback.snd W.hom V.hom) pullback.condition.symm (by trivial)

/-- Matching on the actual scheme fiber products implies matching on every
native site test object, for an arbitrary original presheaf. -/
theorem nativeSections_compatible_of_scheme_pullbacks {S : Scheme.{u}}
    (H : S.Etaleᵒᵖ ⥤ Ab.{w}) {J : Type v} (W : J → S.Etale)
    (z : ∀ j, H.obj (op (W j)))
    (h : ∀ j k, H.map (etaleOverlapFst (W j) (W k)).op (z j) =
      H.map (etaleOverlapSnd (W j) (W k)).op (z k)) :
    Presieve.Arrows.Compatible (H ⋙ CategoryTheory.forget Ab.{w})
      (fun j ↦ (etaleTerminalIsTerminal S).from (W j)) z := by
  intro j k T a b _
  have hab : a.left ≫ (W j).hom = b.left ≫ (W k).hom :=
    (MorphismProperty.Over.w a).trans (MorphismProperty.Over.w b).symm
  let g : T ⟶ etaleOverlapChart (W j) (W k) :=
    MorphismProperty.Over.homMk (pullback.lift a.left b.left hab)
      ((pullback.lift_fst_assoc a.left b.left hab (W j).hom).trans
        (MorphismProperty.Over.w a)) (by trivial)
  have hA : g ≫ etaleOverlapFst (W j) (W k) = a := by
    apply MorphismProperty.Over.Hom.ext
    exact pullback.lift_fst _ _ _
  have hB : g ≫ etaleOverlapSnd (W j) (W k) = b := by
    apply MorphismProperty.Over.Hom.ext
    exact pullback.lift_snd _ _ _
  have heq := congrArg (H.map g.op) (h j k)
  have hp := ConcreteCategory.congr_hom (H.map_comp
    (etaleOverlapFst (W j) (W k)).op g.op) (z j)
  have hq := ConcreteCategory.congr_hom (H.map_comp
    (etaleOverlapSnd (W j) (W k)).op g.op) (z k)
  exact (congrArg (fun q ↦ H.map q.op (z j)) hA).symm.trans
    (hp.trans (heq.trans (hq.symm.trans (congrArg (fun q ↦ H.map q.op (z k)) hB))))
end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
