/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Whole sections squares and transport of original cycle classes

The first construction transports an original resolution factorization through a
natural sections map before evaluating any class. The second constructs a lift
through the original surjective cycle projection and cancels the original
injective comparison. Neither construction selects a cohomology realization.
-/

@[expose] public section
noncomputable section

open CategoryTheory

namespace CategoryTheory

universe u v u' v' w w'

/-- A resolution factorization and its original counit factor give the whole
sections square, before evaluation on any cohomology class. -/
theorem sectionsSquare_of_resolution_factorization
    {R : Type w} {S : Type w'} [CommRing R] [CommRing S]
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (A : C ⥤ D) (G₀ : C ⥤ ModuleCat R) (G : D ⥤ ModuleCat S)
    (σ : R →+* S) (η : G₀ ⟶ A ⋙ G ⋙ ModuleCat.restrictScalars σ)
    {U V : C} {W Z : D} (eI : U ≅ V) (eJ : W ≅ Z)
    (d : A.obj V ⟶ Z) (k : A.obj U ⟶ W)
    (hk : k = A.map eI.hom ≫ d ≫ eJ.inv)
    {H : ModuleCat R} (a : G₀.obj U ⟶ H) (m : H ⟶ G₀.obj V)
    (ha : a ≫ m = G₀.map eI.hom) :
    η.app U ≫ (ModuleCat.restrictScalars σ).map (G.map k) ≫
        (ModuleCat.restrictScalars σ).map (G.map eJ.hom) =
      a ≫ m ≫ η.app V ≫ (ModuleCat.restrictScalars σ).map (G.map d) := by
  let T := ModuleCat.restrictScalars σ
  have hk' : k ≫ eJ.hom = A.map eI.hom ≫ d := by
    rw [hk]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  calc
    η.app U ≫ T.map (G.map k) ≫ T.map (G.map eJ.hom) =
        η.app U ≫ T.map (G.map (k ≫ eJ.hom)) := by
      simp only [Functor.map_comp]
    _ = η.app U ≫ T.map (G.map (A.map eI.hom)) ≫ T.map (G.map d) := by
      rw [hk']
      simp only [Functor.map_comp]
    _ = G₀.map eI.hom ≫ η.app V ≫ T.map (G.map d) := by
      simpa only [Functor.comp_map, Category.assoc] using
        congrArg (fun z => z ≫ T.map (G.map d)) (η.naturality eI.hom).symm
    _ = a ≫ m ≫ η.app V ≫ T.map (G.map d) := by
      rw [← ha]
      simp only [Category.assoc]

/-- Lift the original source homology class to a cycle, transport that cycle,
and identify its original target class by the injective comparison. The inputs
are the cycle projections, counit factors and class maps, not the resulting
cohomology square. -/
theorem transport_of_surjective_cycle_projection
    {HX HY AX AY CX CY U V Z : Type*}
    (aX : HX → AX) (aY : HY ≃ AY)
    (πX : CX → AX) (πY : CY → AY) (hπX : Function.Surjective πX)
    (transfer : HX → HY) (d : CX → CY)
    (iY : HY → Z) (hiY : Function.Injective iY)
    (forward : AX → Z) (targetCycle : CY → Z)
    (hbase : ∀ x, iY (transfer x) = forward (aX x))
    (hcycle : ∀ c, forward (πX c) = targetCycle (d c))
    (mate : AY → Z) (hcounit : ∀ y, mate (aY y) = iY y)
    (hπY : ∀ c, mate (πY c) = targetCycle c)
    (eX : HX → U) (eY : HY → V) (map : U → V)
    (classX : CX → U) (classY : CY → V)
    (heX : ∀ x c, aX x = πX c → eX x = classX c)
    (heY : ∀ y c, aY y = πY c → eY y = classY c)
    (hclass : ∀ c, classY (d c) = map (classX c)) (x : HX) :
    eY (transfer x) = map (eX x) := by
  obtain ⟨c, hc⟩ := hπX (aX x)
  have hy : transfer x = aY.symm (πY (d c)) := by
    apply hiY
    rw [hbase, ← hc, hcycle, ← hcounit, aY.apply_symm_apply, hπY]
  rw [hy, heY _ _ (aY.apply_symm_apply _), hclass, heX x c hc.symm]

end CategoryTheory
