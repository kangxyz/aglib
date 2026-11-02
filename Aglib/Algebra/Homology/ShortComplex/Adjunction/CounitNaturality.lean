/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.ShortComplex.Adjunction.Counit
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Whole-complex naturality of original counit mates

A natural transformation between the original right adjoints, with an exact
change of categories on either side, induces a map of section complexes.
Its cycle square follows from the original inclusions and naturality. Its
homology square then follows from the original cycle projections. Neither
square is an additional hypothesis, and no new homology realization is used.
-/

@[expose] public section
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Adjunction

universe u₀ v₀ u₁ v₁ u₂ v₂ u₃ v₃

variable {C₀ : Type u₀} [Category.{v₀} C₀] [Abelian C₀]
  {D₀ : Type u₁} [Category.{v₁} D₀] [Abelian D₀]
  {C₁ : Type u₂} [Category.{v₂} C₁] [Abelian C₁]
  {D₁ : Type u₃} [Category.{v₃} D₁] [Abelian D₁]
  {F₀ : C₀ ⥤ D₀} {G₀ : D₀ ⥤ C₀} [F₀.Additive] [G₀.Additive]
  {F₁ : C₁ ⥤ D₁} {G₁ : D₁ ⥤ C₁} [F₁.Additive] [G₁.Additive]
  [F₀.PreservesHomology] [F₁.PreservesHomology]
  (adj₀ : F₀ ⊣ G₀) (adj₁ : F₁ ⊣ G₁)
  (A : D₀ ⥤ D₁) (T : C₁ ⥤ C₀) [A.Additive] [T.Additive]
  [A.PreservesHomology] [T.PreservesHomology]
  (η : G₀ ⟶ A ⋙ G₁ ⋙ T)
  (S : ShortComplex D₀) (L : ShortComplex D₁) (ψ : S.map A ⟶ L)

/-- The actual sections map of short complexes, before taking homology. -/
def counitSectionsMap : S.map G₀ ⟶ (L.map G₁).map T :=
  S.mapNatTrans η ≫ (G₁ ⋙ T).mapShortComplex.map ψ

/-- The whole cycle square is forced by the original cycle inclusions. -/
theorem cyclesCounitMate_naturality :
    ShortComplex.cyclesMap (counitSectionsMap A T η S L ψ) ≫
        ((L.map G₁).mapCyclesIso T).hom ≫ T.map (adj₁.cyclesCounitMate L) =
      adj₀.cyclesCounitMate S ≫ η.app S.cycles ≫
        T.map (G₁.map ((S.mapCyclesIso A).inv ≫ ShortComplex.cyclesMap ψ)) := by
  let : G₁.IsRightAdjoint := adj₁.isRightAdjoint
  let q := counitSectionsMap A T η S L ψ
  let c := (S.mapCyclesIso A).inv ≫ ShortComplex.cyclesMap ψ
  have hc : c ≫ L.iCycles = A.map S.iCycles ≫ ψ.τ₂ := by
    dsimp only [c]
    rw [Category.assoc, ShortComplex.cyclesMap_i, ← Category.assoc,
      ShortComplex.mapCyclesIso_inv_iCycles]
  have hl : (ShortComplex.cyclesMap q ≫ ((L.map G₁).mapCyclesIso T).hom ≫
        T.map (adj₁.cyclesCounitMate L)) ≫ T.map (G₁.map L.iCycles) =
      (S.map G₀).iCycles ≫ η.app S.X₂ ≫ T.map (G₁.map ψ.τ₂) := by
    simp only [Category.assoc]
    rw [← T.map_comp, adj₁.cyclesCounitMate_iCycles,
      ShortComplex.mapCyclesIso_hom_iCycles, ShortComplex.cyclesMap_i]
    rfl
  have hr : (adj₀.cyclesCounitMate S ≫ η.app S.cycles ≫ T.map (G₁.map c)) ≫
        T.map (G₁.map L.iCycles) =
      (S.map G₀).iCycles ≫ η.app S.X₂ ≫ T.map (G₁.map ψ.τ₂) := by
    simp only [Category.assoc]
    rw [← T.map_comp, ← G₁.map_comp, hc]
    simp only [Functor.map_comp]
    have hn := η.naturality S.iCycles
    change G₀.map S.iCycles ≫ η.app S.X₂ =
      η.app S.cycles ≫ T.map (G₁.map (A.map S.iCycles)) at hn
    rw [← reassoc_of% hn, adj₀.cyclesCounitMate_iCycles_assoc]
  exact (cancel_mono (T.map (G₁.map L.iCycles))).mp (hl.trans hr.symm)

/-- The original homology counit mates commute with the actual section-complex map.
The right adjoints are not assumed to preserve homology. -/
theorem homologyCounitMate_naturality :
    ShortComplex.homologyMap (counitSectionsMap A T η S L ψ) ≫
        ((L.map G₁).mapHomologyIso T).hom ≫ T.map (adj₁.homologyCounitMate L) =
      adj₀.homologyCounitMate S ≫ η.app S.homology ≫
        T.map (G₁.map ((S.mapHomologyIso A).inv ≫ ShortComplex.homologyMap ψ)) := by
  let q := counitSectionsMap A T η S L ψ
  let c := (S.mapCyclesIso A).inv ≫ ShortComplex.cyclesMap ψ
  let d := (S.mapHomologyIso A).inv ≫ ShortComplex.homologyMap ψ
  have hd : A.map S.homologyπ ≫ d = c ≫ L.homologyπ := by
    dsimp only [c, d]
    rw [← Category.assoc, ShortComplex.map_homologyπ_mapHomologyIso_inv,
      Category.assoc, ShortComplex.homologyπ_naturality]
    simp only [Category.assoc]
  apply (cancel_epi (S.map G₀).homologyπ).mp
  have hl : (S.map G₀).homologyπ ≫
        (ShortComplex.homologyMap q ≫ ((L.map G₁).mapHomologyIso T).hom ≫
          T.map (adj₁.homologyCounitMate L)) =
      (ShortComplex.cyclesMap q ≫ ((L.map G₁).mapCyclesIso T).hom ≫
        T.map (adj₁.cyclesCounitMate L)) ≫ T.map (G₁.map L.homologyπ) := by
    rw [ShortComplex.homologyπ_naturality_assoc,
      ShortComplex.homologyπ_mapHomologyIso_hom_assoc]
    simp only [Category.assoc]
    rw [← T.map_comp, adj₁.homologyCounitMate_homologyπ, T.map_comp]
  have hr : (S.map G₀).homologyπ ≫
        (adj₀.homologyCounitMate S ≫ η.app S.homology ≫ T.map (G₁.map d)) =
      (adj₀.cyclesCounitMate S ≫ η.app S.cycles ≫ T.map (G₁.map c)) ≫
        T.map (G₁.map L.homologyπ) := by
    rw [adj₀.homologyCounitMate_homologyπ_assoc]
    have hn := η.naturality S.homologyπ
    change G₀.map S.homologyπ ≫ η.app S.homology =
      η.app S.cycles ≫ T.map (G₁.map (A.map S.homologyπ)) at hn
    rw [reassoc_of% hn]
    simp only [Category.assoc]
    rw [← T.map_comp, ← G₁.map_comp, hd]
    simp only [Functor.map_comp]
  exact hl.trans ((congrArg (fun z => z ≫ T.map (G₁.map L.homologyπ))
    (cyclesCounitMate_naturality adj₀ adj₁ A T η S L ψ)).trans hr.symm)

end CategoryTheory.Adjunction
