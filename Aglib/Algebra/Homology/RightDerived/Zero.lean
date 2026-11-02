/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.RightDerived.Postcomp
public import Aglib.Algebra.Homology.ShortComplex.MapHomology.Components

/-!
# Original degree-zero units of natural-degree right-derived functors

Deriving a natural transformation preserves the original map into degree zero;
exact postcomposition preserves the same unit. These are the original
category-level implementations extracted from the site module-coefficient
`DerivedGammaZero` owner. No site, module coefficient or derived-category model
is a hypothesis; all category and Hom universes remain independent.
-/

@[expose] public noncomputable section

universe u v u₁ v₁ u₂ v₂

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
  {D : Type u₁} [Category.{v₁} D] [Abelian D]
  {E : Type u₂} [Category.{v₂} E] [Abelian E]

-- Retain the original cochain cycles, native unit and homology comparison dictionaries.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Deriving a natural transformation preserves the original degree-zero unit. -/
@[reassoc]
lemma toRightDerivedZero_naturality {F G : C ⥤ D} [F.Additive] [G.Additive]
    (α : F ⟶ G) (X : C) :
    F.toRightDerivedZero.app X ≫ (NatTrans.rightDerived α 0).app X =
      α.app X ≫ G.toRightDerivedZero.app X := by
  let I := injectiveResolution X
  let φ := (NatTrans.mapHomologicalComplex α (.up ℕ)).app I.cocomplex
  have h : I.toRightDerivedZero' F ≫ HomologicalComplex.cyclesMap φ 0 =
      α.app X ≫ I.toRightDerivedZero' G := by
    rw [← cancel_mono (((G.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).iCycles 0)]
    simp only [Category.assoc, HomologicalComplex.cyclesMap_i,
      InjectiveResolution.toRightDerivedZero'_comp_iCycles,
      InjectiveResolution.toRightDerivedZero'_comp_iCycles_assoc]
    exact α.naturality (I.ι.f 0)
  have hπ : I.toRightDerivedZero' F ≫
      ((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).homologyπ 0 ≫
      HomologicalComplex.homologyMap φ 0 ≫ (I.isoRightDerivedObj G 0).inv =
      α.app X ≫ I.toRightDerivedZero' G ≫
      ((G.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).homologyπ 0 ≫
      (I.isoRightDerivedObj G 0).inv := by
    erw [HomologicalComplex.homologyπ_naturality_assoc, reassoc_of% h]
  rw [I.toRightDerivedZero_eq F, I.toRightDerivedZero_eq G,
    I.rightDerived_app_eq α 0]
  simpa only [CochainComplex.isoHomologyπ₀, HomologicalComplex.isoHomologyπ_hom,
    HomologicalComplex.homologyFunctor_map, Category.assoc, Iso.inv_hom_id_assoc] using hπ

-- Retain the original cochain cycles, native unit and homology comparison dictionaries.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Exact postcomposition retains the original degree-zero derived-functor unit. -/
@[reassoc]
lemma toRightDerivedZero_postcomp (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] [G.PreservesHomology] (X : C) :
    (F ⋙ G).toRightDerivedZero.app X ≫ (rightDerivedPostcompIso F G 0).hom.app X =
      G.map (F.toRightDerivedZero.app X) := by
  let I := injectiveResolution X
  let K := (F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  have h : I.toRightDerivedZero' (F ⋙ G) ≫ ((K.sc 0).mapCyclesIso G).hom =
      G.map (I.toRightDerivedZero' F) := by
    have : Mono (G.map (K.iCycles 0)) := by
      change Mono (G.map (K.sc 0).iCycles)
      rw [← ShortComplex.mapCyclesIso_inv_iCycles G (K.sc 0)]
      infer_instance
    apply (cancel_mono (G.map (K.iCycles 0))).mp
    erw [Category.assoc, ShortComplex.mapCyclesIso_hom_iCycles]
    change I.toRightDerivedZero' (F ⋙ G) ≫
        ((G.mapHomologicalComplex (.up ℕ)).obj K).iCycles 0 = _
    erw [InjectiveResolution.toRightDerivedZero'_comp_iCycles, ← G.map_comp,
      InjectiveResolution.toRightDerivedZero'_comp_iCycles]
    rfl
  have hπ : I.toRightDerivedZero' (F ⋙ G) ≫
      (((F ⋙ G).mapHomologicalComplex (.up ℕ)).obj I.cocomplex).homologyπ 0 ≫
      ((K.sc 0).mapHomologyIso G).hom ≫ G.map (I.isoRightDerivedObj F 0).inv =
      G.map (I.toRightDerivedZero' F ≫ K.homologyπ 0 ≫
        (I.isoRightDerivedObj F 0).inv) := by
    change I.toRightDerivedZero' (F ⋙ G) ≫ ((K.sc 0).map G).homologyπ ≫
      ((K.sc 0).mapHomologyIso G).hom ≫ G.map (I.isoRightDerivedObj F 0).inv = _
    rw [ShortComplex.homologyπ_mapHomologyIso_hom_assoc, reassoc_of% h]
    simp only [Functor.map_comp, HomologicalComplex.homologyπ]
  rw [I.toRightDerivedZero_eq (F ⋙ G), I.toRightDerivedZero_eq F]
  change (I.toRightDerivedZero' (F ⋙ G) ≫
      (((F ⋙ G).mapHomologicalComplex (.up ℕ)).obj I.cocomplex).homologyπ 0 ≫
      (I.isoRightDerivedObj (F ⋙ G) 0).inv) ≫
      (I.isoRightDerivedObj (F ⋙ G) 0).hom ≫ ((K.sc 0).mapHomologyIso G).hom ≫
      G.map (I.isoRightDerivedObj F 0).inv =
    G.map (I.toRightDerivedZero' F ≫ K.homologyπ 0 ≫ (I.isoRightDerivedObj F 0).inv)
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hπ

end CategoryTheory.Functor
