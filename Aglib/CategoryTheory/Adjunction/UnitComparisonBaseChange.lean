/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Base change of original unit comparisons

A commuting square of specified left comparison maps induces the corresponding
square of their original unit transposes. The right exchange is required to be
the actual mate, not an arbitrary comparison with isomorphic source and target.
This abstract lemma supplies the unit part of refinement base-change naturality;
its concrete left-comparison coherence remains a separate input to prove.
-/

@[expose] public section

universe uA vA uB vB uC vC uA' vA' uB' vB' uC' vC'

namespace CategoryTheory

variable {A : Type uA} {B : Type uB} {C : Type uC} {A' : Type uA'} {B' : Type uB'} {C' : Type uC'}
  [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]
  [Category.{vA'} A'] [Category.{vB'} B'] [Category.{vC'} C']
  {J : A ⥤ B} {I : A ⥤ C} {J' : A' ⥤ B'} {I' : A' ⥤ C'}
  {L : B ⥤ C} {R : C ⥤ B} {L' : B' ⥤ C'} {R' : C' ⥤ B'}
  {G : B ⥤ B'} {H : C ⥤ C'} {V : A ⥤ A'}

/-- The actual mate and a commuting left-comparison square transport the
original adjunction-unit comparisons through base change. -/
theorem adjunctionUnitComparison_baseChange
    (adj : L ⊣ R) (adj' : L' ⊣ R') (α : TwoSquare G L L' H)
    (β : R ⋙ G ⟶ H ⋙ R') (hβ : β = (mateEquiv adj adj' α).natTrans)
    (σ : J ⋙ L ⟶ I) (σ' : J' ⋙ L' ⟶ I')
    (eJ : J ⋙ G ⟶ V ⋙ J') (eI : I ⋙ H ⟶ V ⋙ I') (K : A)
    (hσ : α.app (J.obj K) ≫ H.map (σ.app K) ≫ eI.app K =
      L'.map (eJ.app K) ≫ σ'.app (V.obj K)) :
    G.map (adj.unit.app (J.obj K) ≫ R.map (σ.app K)) ≫
        β.app (I.obj K) ≫ R'.map (eI.app K) =
      eJ.app K ≫ (adj'.unit.app (J'.obj (V.obj K)) ≫
        R'.map (σ'.app (V.obj K))) := by
  have hn : G.map (R.map (σ.app K)) ≫ β.app (I.obj K) =
      β.app (L.obj (J.obj K)) ≫ R'.map (H.map (σ.app K)) :=
    β.naturality (σ.app K)
  have hu : G.map (adj.unit.app (J.obj K)) ≫ β.app (L.obj (J.obj K)) =
      adj'.unit.app (G.obj (J.obj K)) ≫ R'.map (α.app (J.obj K)) := by
    rw [hβ]
    exact unit_mateEquiv adj adj' α (J.obj K)
  calc
    G.map (adj.unit.app (J.obj K) ≫ R.map (σ.app K)) ≫
        β.app (I.obj K) ≫ R'.map (eI.app K) =
      G.map (adj.unit.app (J.obj K)) ≫
        (G.map (R.map (σ.app K)) ≫ β.app (I.obj K)) ≫ R'.map (eI.app K) := by
          simp only [Functor.map_comp, Category.assoc]
    _ = (G.map (adj.unit.app (J.obj K)) ≫ β.app (L.obj (J.obj K))) ≫
        R'.map (H.map (σ.app K) ≫ eI.app K) := by
          rw [hn]
          simp only [Functor.map_comp, Category.assoc]
    _ = adj'.unit.app (G.obj (J.obj K)) ≫
        R'.map (L'.map (eJ.app K) ≫ σ'.app (V.obj K)) := by
          rw [hu]
          simp only [Category.assoc, ← Functor.map_comp]
          rw [hσ]
    _ = eJ.app K ≫ (adj'.unit.app (J'.obj (V.obj K)) ≫
        R'.map (σ'.app (V.obj K))) := by
          simpa only [Functor.map_comp, Category.assoc, Functor.comp_obj, Functor.id_obj] using
            congrArg (fun t => t ≫ R'.map (σ'.app (V.obj K)))
              (adj'.unit_naturality (eJ.app K))

end CategoryTheory
