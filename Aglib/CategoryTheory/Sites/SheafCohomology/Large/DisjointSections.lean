/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Sites.Preserves

/-!
# Actual section restrictions for a disjoint covering family

The empty-object sheaf condition and the actual pairwise disjoint pullback
squares make the matching-family condition vacuous. The resulting bijection
is the literal restriction map, with no chosen replacement coefficients.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf.LargeCohomology

universe c h v r

/-- A disjoint covering family decomposes sections by the original restrictions. -/
theorem disjointSections_bijective
    {C : Type c} [Category.{h} C] [HasInitial C]
    (F : Cᵒᵖ ⥤ Type v) {I : C} (hI : IsInitial I)
    (hEmpty : (Presieve.ofArrows (X := I) Empty.elim Empty.instIsEmpty.elim).IsSheafFor F)
    {ι : Type r} [Small.{v} ι] {U : ι → C} (s : Cofan U)
    [(Presieve.ofArrows U s.inj).HasPairwisePullbacks] [∀ i, Mono (s.inj i)]
    (hd : Pairwise fun i j => IsPullback (initial.to _) (initial.to _) (s.inj i) (s.inj j))
    (hCover : (Presieve.ofArrows U s.inj).IsSheafFor F) :
    Function.Bijective (fun x : F.obj (op s.pt) => fun i => F.map (s.inj i).op x) := by
  have hb : Function.Bijective (Equalizer.Presieve.Arrows.forkMap F U s.inj) := by
    rw [Function.bijective_iff_existsUnique]
    rw [Equalizer.Presieve.Arrows.sheaf_condition, Types.type_equalizer_iff_unique] at hCover
    exact fun b => hCover b
      (ConcreteCategory.congr_hom (Presieve.firstMap_eq_secondMap F hEmpty hI s hd) b)
  let e := (Types.Small.productIso (fun i => F.obj (op (U i)))).toEquiv.trans
    (equivShrink (∀ i, F.obj (op (U i)))).symm
  convert e.bijective.comp hb using 1
  funext x i
  simp [e, Iso.toEquiv, Equalizer.Presieve.Arrows.forkMap]

end CategoryTheory.Sheaf.LargeCohomology
