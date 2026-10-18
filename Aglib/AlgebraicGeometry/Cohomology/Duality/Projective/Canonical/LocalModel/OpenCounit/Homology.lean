/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.HomologicalComplex.Adjunction
public import Aglib.Algebra.Homology.ShortComplex.MapHomology.Components
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# The original adjunction on homology

The degreewise native adjunction and the native homology comparisons give
the same adjoint morphism. The proof uses the actual cycle inclusions and
projections, so the original unit and both comparison isomorphisms remain
in the resulting equation.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u v u' v' w
namespace CategoryTheory.Adjunction

variable {A : Type u} [Category.{v} A] [Abelian A]
  {B : Type u'} [Category.{v'} B] [Abelian B]
  {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (adj : F ⊣ G) {ι : Type w} (shape : ComplexShape ι)
  {C : HomologicalComplex A shape} {D : HomologicalComplex B shape}

/-- Taking homology through the original comparison maps commutes with the actual
adjunction on complexes. The homology arrow is the original ordinary adjunction mate. -/
theorem mapHomologicalComplex_homology_homEquiv_symm
    (f : C ⟶ (G.mapHomologicalComplex shape).obj D) (n : ι) :
    let d := ((adj.mapHomologicalComplex shape).homEquiv C D).symm f
    ((C.sc n).mapHomologyIso F).inv ≫ homologyMap d n =
      (adj.homEquiv _ _).symm
        (homologyMap f n ≫ ((D.sc n).mapHomologyIso G).hom) := by
  intro d
  let eC := (C.sc n).mapCyclesIso F
  let eD := (D.sc n).mapCyclesIso G
  let eHC := (C.sc n).mapHomologyIso F
  let eHD := (D.sc n).mapHomologyIso G
  have hfd := ((adj.mapHomologicalComplex shape).homEquiv C D).apply_symm_apply f
  rw [Adjunction.homEquiv_unit] at hfd
  have hd := congrArg (fun h : C ⟶ (G.mapHomologicalComplex shape).obj D => h.f n) hfd
  change adj.unit.app (C.X n) ≫ G.map (d.f n) = f.f n at hd
  have huC : C.iCycles n ≫ adj.unit.app (C.X n) =
      adj.unit.app (C.cycles n) ≫ G.map (F.map (C.iCycles n)) := by
    simpa only [Functor.id_map, Functor.comp_map] using adj.unit.naturality (C.iCycles n)
  have hc : adj.unit.app (C.cycles n) ≫ G.map (eC.inv ≫ cyclesMap d n) =
      cyclesMap f n ≫ eD.hom := by
    apply (cancel_mono (G.map (D.iCycles n))).mp
    simp only [Category.assoc]
    have hr : cyclesMap f n ≫ eD.hom ≫ G.map (D.iCycles n) = C.iCycles n ≫ f.f n := by
      erw [ShortComplex.mapCyclesIso_hom_iCycles, HomologicalComplex.cyclesMap_i]
    rw [hr]
    calc
      _ = adj.unit.app (C.cycles n) ≫ G.map (F.map (C.iCycles n)) ≫ G.map (d.f n) := by
        erw [← G.map_comp, Category.assoc, HomologicalComplex.cyclesMap_i,
          ← Category.assoc, ShortComplex.mapCyclesIso_inv_iCycles F (C.sc n), G.map_comp]
        rfl
      _ = C.iCycles n ≫ adj.unit.app (C.X n) ≫ G.map (d.f n) := by
        rw [← Category.assoc, ← huC, Category.assoc]
      _ = _ := by rw [hd]
  have hp : F.map (C.homologyπ n) ≫ eHC.inv ≫ homologyMap d n =
      eC.inv ≫ cyclesMap d n ≫ D.homologyπ n := by
    have hπ : F.map (C.homologyπ n) ≫ eHC.inv =
        eC.inv ≫ ((F.mapHomologicalComplex shape).obj C).homologyπ n :=
      ShortComplex.map_homologyπ_mapHomologyIso_inv F (C.sc n)
    rw [← Category.assoc, hπ, Category.assoc, homologyπ_naturality d n]
  have hp' : C.homologyπ n ≫ homologyMap f n ≫ eHD.hom =
      cyclesMap f n ≫ eD.hom ≫ G.map (D.homologyπ n) := by
    rw [homologyπ_naturality_assoc]
    exact congrArg (fun h => cyclesMap f n ≫ h)
      (ShortComplex.homologyπ_mapHomologyIso_hom G (D.sc n))
  have huH : C.homologyπ n ≫ adj.unit.app (C.homology n) =
      adj.unit.app (C.cycles n) ≫ G.map (F.map (C.homologyπ n)) := by
    simpa only [Functor.id_map, Functor.comp_map] using adj.unit.naturality (C.homologyπ n)
  change eHC.inv ≫ homologyMap d n =
    (adj.homEquiv (C.homology n) (D.homology n)).symm (homologyMap f n ≫ eHD.hom)
  apply (adj.homEquiv (C.homology n) (D.homology n)).injective
  erw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  apply (cancel_epi (C.homologyπ n)).mp
  change C.homologyπ n ≫ adj.unit.app (C.homology n) ≫
      G.map (eHC.inv ≫ homologyMap d n) =
    C.homologyπ n ≫ homologyMap f n ≫ eHD.hom
  calc
    _ = adj.unit.app (C.cycles n) ≫
        G.map (F.map (C.homologyπ n) ≫ eHC.inv ≫ homologyMap d n) := by
      rw [← Category.assoc, huH, Category.assoc, ← G.map_comp]
    _ = adj.unit.app (C.cycles n) ≫
        G.map ((eC.inv ≫ cyclesMap d n) ≫ D.homologyπ n) := by
      rw [hp, Category.assoc]
    _ = adj.unit.app (C.cycles n) ≫ G.map (eC.inv ≫ cyclesMap d n) ≫
        G.map (D.homologyπ n) := by
      rw [G.map_comp]
    _ = cyclesMap f n ≫ eD.hom ≫ G.map (D.homologyπ n) := by
      rw [← Category.assoc, hc, Category.assoc]
    _ = _ := hp'.symm

end CategoryTheory.Adjunction
