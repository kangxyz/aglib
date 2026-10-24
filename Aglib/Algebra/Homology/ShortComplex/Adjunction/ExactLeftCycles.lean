/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.ShortComplex.MapHomology.Components
public import Mathlib.CategoryTheory.Adjunction.Basic

/-! # Cycle normalization for an adjunction with exact left adjoint

The original adjunction unit followed by the inverse native exact-homology
comparison and an actual complex map has the same original cycle formula.
The right adjoint is not assumed to preserve homology.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [F.PreservesHomology]
  (adj : F ⊣ G) (S : ShortComplex C) {T : ShortComplex D} (δ : S.map F ⟶ T)

/-- The original exact-left-adjoint homology map is computed by the original
unit on cycles and the actual cycle map, with no exactness of the right adjoint. -/
theorem homology_unit_exact_left_cycles :
    S.homologyπ ≫ adj.unit.app S.homology ≫
        G.map ((S.mapHomologyIso F).inv ≫ ShortComplex.homologyMap δ) =
      adj.unit.app S.cycles ≫
        G.map ((S.mapCyclesIso F).inv ≫ ShortComplex.cyclesMap δ ≫ T.homologyπ) := by
  have hu : S.homologyπ ≫ adj.unit.app S.homology =
      adj.unit.app S.cycles ≫ G.map (F.map S.homologyπ) :=
    adj.unit.naturality S.homologyπ
  rw [← Category.assoc, hu, Category.assoc, ← G.map_comp]
  rw [← Category.assoc, ShortComplex.map_homologyπ_mapHomologyIso_inv,
    Category.assoc, ShortComplex.homologyπ_naturality]

/-- The same followed cycle map preserves the original cycle inclusion. -/
theorem cycles_unit_exact_left_iCycles :
    adj.unit.app S.cycles ≫
        G.map ((S.mapCyclesIso F).inv ≫ ShortComplex.cyclesMap δ) ≫ G.map T.iCycles =
      S.iCycles ≫ adj.unit.app S.X₂ ≫ G.map δ.τ₂ := by
  rw [← G.map_comp, Category.assoc, ShortComplex.cyclesMap_i,
    ← Category.assoc, ShortComplex.mapCyclesIso_inv_iCycles, G.map_comp]
  have hu : S.iCycles ≫ adj.unit.app S.X₂ =
      adj.unit.app S.cycles ≫ G.map (F.map S.iCycles) :=
    adj.unit.naturality S.iCycles
  rw [← Category.assoc, ← hu, Category.assoc]

end CategoryTheory.Adjunction
