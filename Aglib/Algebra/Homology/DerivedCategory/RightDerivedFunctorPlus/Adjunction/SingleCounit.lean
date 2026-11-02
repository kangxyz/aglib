/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.SingleSquare
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.ZeroComparison
public import Aglib.CategoryTheory.Sites.SheafCohomology.OriginalSections.DerivedPullback

/-! # The original single counit and the derived section edge

The original right-derived single unit is the adjunct of the original
coefficient counit under the installed derived adjunction. Consequently its
section edge is exactly pullback followed by that counit, not a reselected
map with the same source and target.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CategoryTheory.Adjunction

universe u v d u' v' d' u'' v'' d''
variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{d} A]
  [EnoughInjectives A] {B : Type u'} [Category.{v'} B] [Abelian B]
  [HasDerivedCategory.{d'} B] [EnoughInjectives B]
  {L : A ⥤ B} {R : B ⥤ A} [L.Additive] [R.Additive] [L.PreservesHomology]
  (adj : L ⊣ R)

omit [HasDerivedCategory A] [EnoughInjectives A] [HasDerivedCategory B]
  [EnoughInjectives B] [L.PreservesHomology] in
/-- The actual complex counit commutes with the original single-complex maps. -/
theorem singleCounit_complex (M : B) :
    L.mapCochainComplexPlus.map (R.mapCochainComplexPlusSingleIso M).inv ≫
        adj.mapCochainComplexPlus.counit.app
          ((CochainComplex.singleFunctorPlus B 0).obj M) =
      (L.mapCochainComplexPlusSingleIso (R.obj M)).hom ≫
        (CochainComplex.singleFunctorPlus B 0).map (adj.counit.app M) := by
  apply ObjectProperty.hom_ext
  ext i
  by_cases hi : i = 0
  · subst i
    simp [Functor.mapCochainComplexPlusSingleIso, mapCochainComplexPlus,
      mapHomologicalComplex, singleMapHomologicalComplex,
      CochainComplex.singleFunctorPlus,
      CochainComplex.singleFunctor, ObjectProperty.lift, HomologicalComplex.single]
  · exact (L.map_isZero (isZero_single_obj_X (.up ℤ) 0 (R.obj M) i hi)).eq_of_src _ _

/-- The installed derived counit sends the literal right-derived single unit
to the original coefficient counit under the exact-single comparison. -/
@[reassoc]
theorem rightDerivedSingleUnit_counit (M : B) :
    L.rightDerivedFunctorPlus.map (R.rightDerivedSingleUnit M) ≫
        adj.rightDerivedFunctorPlus.counit.app
          ((DerivedCategory.Plus.singleFunctor B 0).obj M) =
      (L.rightDerivedFunctorPlusSingleIso 0).hom.app (R.obj M) ≫
        (DerivedCategory.Plus.singleFunctor B 0).map (adj.counit.app M) := by
  let K := (CochainComplex.singleFunctorPlus B 0).obj M
  let s := (R.mapCochainComplexPlusSingleIso M).inv
  have hn := L.rightDerivedFunctorPlusExactComparison.hom.naturality s
  change L.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map s) ≫
      L.rightDerivedFunctorPlusExactComparison.hom.app _ =
    L.rightDerivedFunctorPlusExactComparison.hom.app _ ≫
      DerivedCategory.Plus.Q.map (L.mapCochainComplexPlus.map s) at hn
  change L.rightDerivedFunctorPlus.map
      (DerivedCategory.Plus.Q.map s ≫ R.rightDerivedFunctorPlusUnit.app K) ≫ _ = _
  erw [Functor.map_comp, Category.assoc, adj.rightDerivedFunctorPlus_counit_fac K,
    ← Category.assoc, hn, Category.assoc, ← Functor.map_comp,
    singleCounit_complex, Functor.map_comp, ← Category.assoc,
    ← L.rightDerivedFunctorPlusSingleIso_exactComparison]
  rfl

variable {V : Type u''} [Category.{v''} V] [Abelian V] [HasDerivedCategory.{d''} V]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  (Γ : A ⥤ V) {Δ : B ⥤ V} [Γ.Additive] [Δ.Additive] (e : R ⋙ Γ ≅ Δ)

/-- The original section edge equals original derived pullback followed by the
original coefficient counit. All functors and adjunctions are the installed ones. -/
theorem derivedUnitSectionsPullbackSingle_counit (M : B) :
    derivedUnitSectionsPullbackSingle adj Γ e (R.obj M) ≫
        Δ.rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor B 0).map (adj.counit.app M)) =
      Γ.rightDerivedFunctorPlus.map (R.rightDerivedSingleUnit M) ≫
        (derivedRightSectionsIso adj Γ e).hom.app
          ((DerivedCategory.Plus.singleFunctor B 0).obj M) := by
  let SA := (DerivedCategory.Plus.singleFunctor A 0).obj (R.obj M)
  let SB := (DerivedCategory.Plus.singleFunctor B 0).obj M
  let u := R.rightDerivedSingleUnit M
  let ε := adj.rightDerivedFunctorPlus.counit.app SB
  let E := (derivedRightSectionsIso adj Γ e).hom
  have hn := E.naturality (L.rightDerivedFunctorPlus.map u ≫ ε)
  dsimp only [Functor.comp_map, Functor.id_obj] at hn
  have hu : adj.rightDerivedFunctorPlus.unit.app SA ≫
      R.rightDerivedFunctorPlus.map (L.rightDerivedFunctorPlus.map u ≫ ε) = u := by
    have hn := adj.rightDerivedFunctorPlus.unit.naturality u
    dsimp only [Functor.comp_map, Functor.id_map] at hn
    rw [Functor.map_comp, ← Category.assoc,
      ← hn, Category.assoc,
      adj.rightDerivedFunctorPlus.right_triangle_components]
    exact Category.comp_id u
  dsimp only [derivedUnitSectionsPullbackSingle, derivedUnitSectionsPullback]
  rw [Category.assoc, ← Functor.map_comp, ← adj.rightDerivedSingleUnit_counit M]
  change (Γ.rightDerivedFunctorPlus.map (adj.rightDerivedFunctorPlus.unit.app SA) ≫
    E.app (L.rightDerivedFunctorPlus.obj SA)) ≫
      Δ.rightDerivedFunctorPlus.map (L.rightDerivedFunctorPlus.map u ≫ ε) = _
  rw [Category.assoc]
  rw [← hn, ← Γ.rightDerivedFunctorPlus.map_comp_assoc, hu]

/-- Normalization of the same edge on the original natural-degree derived
functors, retaining both native single/homology comparisons. -/
theorem rightDerivedUnitSectionsPullback_counit (M : B) (q : ℕ) :
    rightDerivedUnitSectionsPullback adj Γ e (R.obj M) q ≫
        (Δ.rightDerived q).map (adj.counit.app M) =
      (Γ.rightDerivedSingleHomologyIso q).hom.app (R.obj M) ≫
        (DerivedCategory.Plus.homologyFunctor V (q : ℤ)).map
          (Γ.rightDerivedFunctorPlus.map (R.rightDerivedSingleUnit M) ≫
            (derivedRightSectionsIso adj Γ e).hom.app
              ((DerivedCategory.Plus.singleFunctor B 0).obj M)) ≫
        (Δ.rightDerivedSingleHomologyIso q).inv.app M := by
  let H := DerivedCategory.Plus.homologyFunctor V (q : ℤ)
  have hn := (Δ.rightDerivedSingleHomologyIso q).inv.naturality (adj.counit.app M)
  dsimp only [Functor.comp_map] at hn
  dsimp only [rightDerivedUnitSectionsPullback]
  simp only [Category.assoc]
  erw [← hn]
  rw [← H.map_comp_assoc, derivedUnitSectionsPullbackSingle_counit]
  rfl

end CategoryTheory.Adjunction
