/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.ShortComplex.Adjunction

/-!
# Cycles of the original homology adjunction unit

The original adjunction unit on cycles retains the actual cycle inclusion
and homology projection. The right adjoint preserves homology; no exactness
of the left adjoint is required. Following any actual short-complex map
computes the original canonical homology mate on those same cycle classes.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Adjunction

universe u v u' v'

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]

private theorem mapHomologyIso_homologyπ (H : C ⥤ D) [H.Additive] [H.PreservesHomology]
    (S : ShortComplex C) :
    (S.map H).homologyπ ≫ (S.mapHomologyIso H).hom =
      (S.mapCyclesIso H).hom ≫ H.map S.homologyπ := by
  let h := S.homologyData.left
  rw [h.mapHomologyIso_eq H]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  rw [← Category.assoc, ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom]
  simp only [ShortComplex.LeftHomologyData.map_π]
  rw [Category.assoc, ← H.map_comp,
    ShortComplex.LeftHomologyData.π_comp_homologyIso_inv, H.map_comp]
  have hc := congrArg (fun e => e.hom) (h.mapCyclesIso_eq H)
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom] at hc
  simpa only [Category.assoc] using congrArg (fun z => z ≫ H.map S.homologyπ) hc.symm

variable {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive] [G.PreservesHomology]
  (adj : F ⊣ G) (S : ShortComplex C)

/-- The original adjunction unit on cycles uses the native exact right-adjoint comparisons. -/
def cyclesUnit : S.cycles ⟶ G.obj (S.map F).cycles :=
  (S.mapCyclesIso (𝟭 C)).inv ≫
    ShortComplex.cyclesMap (S.mapNatTrans adj.unit) ≫
      ((S.map F).mapCyclesIso G).hom

/-- The cycle unit has the actual original component of the adjunction unit. -/
@[reassoc]
theorem cyclesUnit_iCycles :
    adj.cyclesUnit S ≫ G.map (S.map F).iCycles = S.iCycles ≫ adj.unit.app S.X₂ := by
  unfold cyclesUnit
  simp only [Category.assoc]
  rw [ShortComplex.mapCyclesIso_hom_iCycles]
  change (S.mapCyclesIso (𝟭 C)).inv ≫
      ShortComplex.cyclesMap (S.mapNatTrans adj.unit) ≫ (S.map (F ⋙ G)).iCycles = _
  rw [ShortComplex.cyclesMap_i]
  rw [← Category.assoc, ← ShortComplex.mapCyclesIso_hom_iCycles S (𝟭 C),
    Iso.inv_hom_id_assoc]
  rfl

/-- Projecting the original cycle unit gives the original homology unit. -/
@[reassoc]
theorem cyclesUnit_homologyπ :
    S.homologyπ ≫ adj.homologyUnit S =
      adj.cyclesUnit S ≫ G.map (S.map F).homologyπ := by
  have hId : S.homologyπ ≫ (S.mapHomologyIso (𝟭 C)).inv =
      (S.mapCyclesIso (𝟭 C)).inv ≫ (S.map (𝟭 C)).homologyπ := by
    apply (cancel_mono (S.mapHomologyIso (𝟭 C)).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [mapHomologyIso_homologyπ, Iso.inv_hom_id_assoc]
    rfl
  unfold homologyUnit cyclesUnit
  rw [← Category.assoc, ← Category.assoc, hId]
  simp only [Category.assoc]
  rw [← Category.assoc (S.map (𝟭 C)).homologyπ,
    ShortComplex.homologyπ_naturality]
  simp only [Category.assoc]
  change (S.mapCyclesIso (𝟭 C)).inv ≫ ShortComplex.cyclesMap (S.mapNatTrans adj.unit) ≫
      ((S.map F).map G).homologyπ ≫ ((S.map F).mapHomologyIso G).hom = _
  rw [mapHomologyIso_homologyπ]

/-- Follow the original cycle unit by the native cycle map of an actual coefficient arrow. -/
def cyclesUnitMap {T : ShortComplex D} (δ : S.map F ⟶ T) : S.cycles ⟶ G.obj T.cycles :=
  adj.cyclesUnit S ≫ G.map (ShortComplex.cyclesMap δ)

/-- The followed cycle unit retains the original coefficient component. -/
@[reassoc]
theorem cyclesUnitMap_iCycles {T : ShortComplex D} (δ : S.map F ⟶ T) :
    adj.cyclesUnitMap S δ ≫ G.map T.iCycles =
      S.iCycles ≫ adj.unit.app S.X₂ ≫ G.map δ.τ₂ := by
  unfold cyclesUnitMap
  rw [Category.assoc, ← G.map_comp, ShortComplex.cyclesMap_i, G.map_comp,
    ← Category.assoc, cyclesUnit_iCycles, Category.assoc]

/-- The actual cycle projection computes the followed original homology unit. -/
@[reassoc]
theorem cyclesUnitMap_homologyπ {T : ShortComplex D} (δ : S.map F ⟶ T) :
    S.homologyπ ≫ adj.homologyUnit S ≫ G.map (ShortComplex.homologyMap δ) =
      adj.cyclesUnitMap S δ ≫ G.map T.homologyπ := by
  rw [← Category.assoc, cyclesUnit_homologyπ, Category.assoc, ← G.map_comp,
    ShortComplex.homologyπ_naturality, G.map_comp, ← Category.assoc]
  rfl

/-- The original canonical homology mate, followed by the actual homology map, has this
literal cycle-projection formula through the original scalar or geometric adjunction unit. -/
theorem homologyComparison_map_homologyπ {T : ShortComplex D} (δ : S.map F ⟶ T) :
    S.homologyπ ≫ adj.unit.app S.homology ≫
        G.map (adj.homologyComparison S ≫ ShortComplex.homologyMap δ) =
      adj.cyclesUnitMap S δ ≫ G.map T.homologyπ := by
  rw [G.map_comp, ← Category.assoc (adj.unit.app S.homology), homologyComparison_unit]
  exact adj.cyclesUnitMap_homologyπ S δ

end CategoryTheory.Adjunction
