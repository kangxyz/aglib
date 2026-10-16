/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.ShortComplex.MapHomology.Components

/-!
# Native counit mates on homology and cycles

For an additive adjunction with homology-preserving left adjoint, native
homology of the original counit has an ordinary adjunction mate. The mate
uses the actual unit at homology of the original right-adjoint image.
Its cycle inclusion, cycle projection and counit equations retain those
same native maps. The right adjoint need only be additive.
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
  {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive] [F.PreservesHomology]
  (adj : F ⊣ G) (S : ShortComplex D)

/-- Native homology of the original counit, through the original exact-left-adjoint
homology comparison. No preservation of homology by the right adjoint is assumed. -/
def homologyCounit : F.obj (S.map G).homology ⟶ S.homology :=
  ((S.map G).mapHomologyIso F).inv ≫ ShortComplex.homologyMap
    (show (S.map G).map F ⟶ S from S.mapNatTrans adj.counit)

/-- The ordinary adjunction mate of the native counit homology map. Its first arrow is
exactly the original unit at homology of the right-adjoint image. -/
def homologyCounitMate : (S.map G).homology ⟶ G.obj S.homology :=
  adj.unit.app (S.map G).homology ≫ G.map (homologyCounit adj S)

/-- The ordinary unit on cycles followed by the native exact-left-adjoint cycle comparison
and the original counit cycle map. -/
def cyclesCounitMate : (S.map G).cycles ⟶ G.obj S.cycles :=
  adj.unit.app (S.map G).cycles ≫ G.map
    (((S.map G).mapCyclesIso F).inv ≫ ShortComplex.cyclesMap
      (show (S.map G).map F ⟶ S from S.mapNatTrans adj.counit))

/-- The counit cycle mate retains the original cycle inclusion. -/
@[reassoc]
theorem cyclesCounitMate_iCycles :
    cyclesCounitMate adj S ≫ G.map S.iCycles = (S.map G).iCycles := by
  let T := S.map G
  let e := T.mapCyclesIso F
  let φ : (S.map G).map F ⟶ S := S.mapNatTrans adj.counit
  dsimp only [cyclesCounitMate]
  simp only [Category.assoc]
  change adj.unit.app T.cycles ≫ G.map (e.inv ≫ ShortComplex.cyclesMap φ) ≫
    G.map S.iCycles = T.iCycles
  rw [← G.map_comp, Category.assoc, ShortComplex.cyclesMap_i,
    ← Category.assoc, ShortComplex.mapCyclesIso_inv_iCycles F T, G.map_comp]
  have hu : T.iCycles ≫ adj.unit.app T.X₂ =
      adj.unit.app T.cycles ≫ G.map (F.map T.iCycles) := by
    simpa only [Functor.id_map, Functor.comp_map] using adj.unit.naturality T.iCycles
  rw [← Category.assoc, ← hu, Category.assoc]
  change T.iCycles ≫ adj.unit.app (G.obj S.X₂) ≫ G.map (adj.counit.app S.X₂) = T.iCycles
  rw [adj.right_triangle_components]
  erw [Category.comp_id]

/-- The counit homology mate retains the original projection of every cycle class. -/
@[reassoc]
theorem homologyCounitMate_homologyπ :
    (S.map G).homologyπ ≫ homologyCounitMate adj S =
      cyclesCounitMate adj S ≫ G.map S.homologyπ := by
  let T := S.map G
  let eH := T.mapHomologyIso F
  let eC := T.mapCyclesIso F
  let φ : (S.map G).map F ⟶ S := S.mapNatTrans adj.counit
  have h : F.map T.homologyπ ≫ eH.inv ≫ ShortComplex.homologyMap φ =
      eC.inv ≫ ShortComplex.cyclesMap φ ≫ S.homologyπ := by
    rw [← Category.assoc, ShortComplex.map_homologyπ_mapHomologyIso_inv F T,
      Category.assoc, ShortComplex.homologyπ_naturality]
  dsimp only [homologyCounitMate, homologyCounit, cyclesCounitMate]
  simp only [Category.assoc]
  change T.homologyπ ≫ adj.unit.app T.homology ≫
      G.map (eH.inv ≫ ShortComplex.homologyMap φ) =
    adj.unit.app T.cycles ≫ G.map (eC.inv ≫ ShortComplex.cyclesMap φ) ≫ G.map S.homologyπ
  have hu : T.homologyπ ≫ adj.unit.app T.homology =
      adj.unit.app T.cycles ≫ G.map (F.map T.homologyπ) := by
    simpa only [Functor.id_map, Functor.comp_map] using adj.unit.naturality T.homologyπ
  rw [← Category.assoc, hu, Category.assoc]
  change adj.unit.app T.cycles ≫ G.map (F.map T.homologyπ) ≫
    G.map (eH.inv ≫ ShortComplex.homologyMap φ) = _
  rw [← G.map_comp, h]
  simp only [Functor.map_comp, Category.assoc]

/-- The original counit identifies the left-adjoint image of its homology mate with the
literal native counit homology map. -/
@[reassoc]
theorem map_homologyCounitMate_counit :
    F.map (homologyCounitMate adj S) ≫ adj.counit.app S.homology =
      homologyCounit adj S := by
  let h := homologyCounit adj S
  have hn : F.map (G.map h) ≫ adj.counit.app S.homology =
      adj.counit.app (F.obj (S.map G).homology) ≫ h := by
    simpa only [Functor.comp_map, Functor.id_map] using adj.counit.naturality h
  dsimp only [homologyCounitMate]
  rw [F.map_comp, Category.assoc, hn, ← Category.assoc]
  erw [adj.left_triangle_components, Category.id_comp]

end CategoryTheory.Adjunction
