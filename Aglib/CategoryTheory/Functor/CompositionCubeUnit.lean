/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.CompositionCubeWhole

/-! Reflection of unit squares through whole comparison cubes. -/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Functor

private theorem comparisonUnit_comp
    {A B D A' B' D' : Type*}
    [Category* A] [Category* B] [Category* D] [Category* A'] [Category* B'] [Category* D']
    {L : A ⥤ B} {H : B ⥤ D} {K : A' ⥤ B'} {H' : B' ⥤ D'}
    {QA : A ⥤ A'} {QB : B ⥤ B'} {QD : D ⥤ D'}
    (sL : L ⋙ QB ≅ QA ⋙ K) (sH : H ⋙ QD ≅ QB ⋙ H')
    (U : A) {V : B} {W : D} {U' : A'} {V' : B'} {W' : D'}
    (eU : U' ≅ QA.obj U) (eV : V' ≅ QB.obj V) (eW : W' ≅ QD.obj W)
    (l : L.obj U ⟶ V) (h : H.obj V ⟶ W) (l' : K.obj U' ⟶ V') (h' : H'.obj V' ⟶ W')
    (hl : sL.inv.app U ≫ QB.map l = K.map eU.inv ≫ l' ≫ eV.hom)
    (hh : sH.inv.app V ≫ QD.map h = H'.map eV.inv ≫ h' ≫ eW.hom) :
    H'.map (sL.inv.app U) ≫ sH.inv.app (L.obj U) ≫ QD.map (H.map l ≫ h) =
      H'.map (K.map eU.inv) ≫ H'.map l' ≫ h' ≫ eW.hom := by
  have hn : H'.map (QB.map l) ≫ sH.inv.app V =
      sH.inv.app (L.obj U) ≫ QD.map (H.map l) := sH.inv.naturality l
  rw [QD.map_comp, ← Category.assoc (sH.inv.app _), ← hn]
  simp only [Category.assoc]
  rw [← H'.map_comp_assoc, hl, H'.map_comp, H'.map_comp]
  simp only [Category.assoc]
  rw [hh, ← H'.map_comp_assoc eV.hom eV.inv, eV.hom_inv_id, H'.map_id, Category.id_comp]

/-- A faithful whole comparison cube reflects its unit square from the original
four coefficient transports and the original square on the comparison objects. -/
theorem comparisonCubeEquation_unit
    {A B C D A' B' C' D' : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D]
    [Category* A'] [Category* B'] [Category* C'] [Category* D']
    {L : A ⥤ B} {L' : C ⥤ D} {G : A ⥤ C} {H : B ⥤ D}
    {K : A' ⥤ B'} {K' : C' ⥤ D'} {G' : A' ⥤ C'} {H' : B' ⥤ D'}
    {QA : A ⥤ A'} {QB : B ⥤ B'} {QC : C ⥤ C'} {QD : D ⥤ D'} [QD.Faithful]
    (sL : L ⋙ QB ≅ QA ⋙ K) (sL' : L' ⋙ QD ≅ QC ⋙ K')
    (sG : G ⋙ QC ≅ QA ⋙ G') (sH : H ⋙ QD ≅ QB ⋙ H')
    (sm : G ⋙ L' ≅ L ⋙ H) (sa : G' ⋙ K' ≅ K ⋙ H')
    (hc : ComparisonCubeEquation sL sL' sG sH sm sa)
    (U : A) {V : B} {W : C} {T : D} {U' : A'} {V' : B'} {W' : C'} {T' : D'}
    (eU : U' ≅ QA.obj U) (eV : V' ≅ QB.obj V) (eW : W' ≅ QC.obj W) (eT : T' ≅ QD.obj T)
    (l : L.obj U ⟶ V) (l' : L'.obj W ⟶ T) (g : G.obj U ⟶ W) (h : H.obj V ⟶ T)
    (k : K.obj U' ⟶ V') (k' : K'.obj W' ⟶ T') (g' : G'.obj U' ⟶ W') (h' : H'.obj V' ⟶ T')
    (hl : sL.inv.app U ≫ QB.map l = K.map eU.inv ≫ k ≫ eV.hom)
    (hl' : sL'.inv.app W ≫ QD.map l' = K'.map eW.inv ≫ k' ≫ eT.hom)
    (hg : sG.inv.app U ≫ QC.map g = G'.map eU.inv ≫ g' ≫ eW.hom)
    (hh : sH.inv.app V ≫ QD.map h = H'.map eV.inv ≫ h' ≫ eT.hom)
    (hs : sa.hom.app U' ≫ H'.map k ≫ h' = K'.map g' ≫ k') :
    sm.hom.app U ≫ H.map l ≫ h = L'.map g ≫ l' := by
  let a := K'.map (sG.inv.app U) ≫ sL'.inv.app (G.obj U)
  let b := H'.map (sL.inv.app U) ≫ sH.inv.app (L.obj U)
  let m := H.map l ≫ h
  let n := L'.map g ≫ l'
  have he : sa.hom.app (QA.obj U) ≫ b = a ≫ QD.map (sm.hom.app U) := by
    dsimp only [a, b]
    simpa only [Category.assoc] using comparisonCubeEquation_app sL sL' sG sH sm sa hc U
  have hm : b ≫ QD.map m = H'.map (K.map eU.inv) ≫ H'.map k ≫ h' ≫ eT.hom := by
    dsimp only [b, m]
    simpa only [Category.assoc] using comparisonUnit_comp sL sH U eU eV eT l h k h' hl hh
  have hn : a ≫ QD.map n = K'.map (G'.map eU.inv) ≫ K'.map g' ≫ k' ≫ eT.hom := by
    dsimp only [a, n]
    simpa only [Category.assoc] using comparisonUnit_comp sG sL' U eU eW eT g l' g' k' hg hl'
  have hnat : K'.map (G'.map eU.inv) ≫ sa.hom.app U' =
      sa.hom.app (QA.obj U) ≫ H'.map (K.map eU.inv) := sa.hom.naturality eU.inv
  let : Epi a := by dsimp only [a]; infer_instance
  apply QD.map_injective
  apply (cancel_epi a).mp
  change a ≫ QD.map (sm.hom.app U ≫ m) = a ≫ QD.map n
  rw [QD.map_comp, ← Category.assoc, ← he, Category.assoc, hm, hn, ← Category.assoc,
    ← hnat]
  simp only [Category.assoc]
  rw [reassoc_of% hs]

end CategoryTheory.Functor
