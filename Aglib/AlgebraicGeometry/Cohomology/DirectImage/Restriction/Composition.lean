/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Restriction
public import Aglib.AlgebraicGeometry.Modules.BaseChange.OpenImmersion.CartesianSections
public import Aglib.Algebra.Homology.CochainComplexPlus.NatTrans
public import Aglib.Algebra.Homology.ShortComplex.MapHomology

/-!
# Pasting the original higher-image open comparisons

The actual native higher-image open isomorphisms compose through the
original restriction-composition comparisons. The proof first pastes the
ordinary cartesian maps, then uses their original derived units and the
native single and homology comparisons. All coefficients and natural
degrees are allowed; no finiteness or quasicoherence premise is used.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The standard derived-category structure on the indicated module-sheaf category. -/
-- Preserve the original local native derived-category instance and its generated name.
@[nolint defsWithUnderscore]
local instance (Z : Scheme.{u}) : HasDerivedCategory.{u + 1} Z.Modules :=
  HasDerivedCategory.standard _

section RestrictionComposition

variable {U V X : Scheme.{u}} (a : U ⟶ V) (j : V ⟶ X)
  [IsOpenImmersion a] [IsOpenImmersion j]

private def derivedRestrictionCompIso :
    (restrictFunctor (a ≫ j)).rightDerivedFunctorPlus ≅
      (restrictFunctor j).rightDerivedFunctorPlus ⋙
        (restrictFunctor a).rightDerivedFunctorPlus :=
  (restrictFunctor (a ≫ j)).rightDerivedFunctorPlusIso (restrictFunctorComp a j) ≪≫
    (restrictFunctor j).rightDerivedFunctorPlusCompIsoOfPreservesHomology (restrictFunctor a)

private theorem derivedRestrictionCompIso_unit (K : CochainComplex.Plus X.Modules) :
    (restrictFunctor (a ≫ j)).rightDerivedFunctorPlusUnit.app K ≫
        (derivedRestrictionCompIso a j).hom.app (DerivedCategory.Plus.Q.obj K) =
      DerivedCategory.Plus.Q.map
          ((NatIso.mapCochainComplexPlus (restrictFunctorComp a j)).hom.app K) ≫
        (Functor.rightDerivedFunctorPlusCompUnit (restrictFunctor j)
          (restrictFunctor a)).app K := by
  let L := restrictFunctor (a ≫ j)
  let F := restrictFunctor j
  let G := restrictFunctor a
  let e := F.rightDerivedFunctorPlusCompIsoOfPreservesHomology G
  have h := L.rightDerivedFunctorPlusIso_hom_app (restrictFunctorComp a j) K
  have he : (F ⋙ G).rightDerivedFunctorPlusUnit.app K ≫
      e.hom.app (DerivedCategory.Plus.Q.obj K) =
    (Functor.rightDerivedFunctorPlusCompUnit F G).app K := by
    simpa only [Functor.rightDerivedFunctorPlusCompUnit_app] using
      F.rightDerivedFunctorPlusCompIsoOfPreservesHomology_hom_app G K
  change L.rightDerivedFunctorPlusUnit.app K ≫
      (L.rightDerivedFunctorPlusIso (restrictFunctorComp a j)).hom.app _ ≫ e.hom.app _ = _
  rw [← Category.assoc, h, Category.assoc, he]


end RestrictionComposition

section TripleUnit

variable {W X Y Z : Scheme.{u}} (f : W ⟶ X) (j : Y ⟶ X) (v : Z ⟶ Y)
  [IsOpenImmersion j] [IsOpenImmersion v]

private def tripleUnit :
    (pushforward f ⋙ restrictFunctor j ⋙ restrictFunctor v).mapCochainComplexPlus ⋙
        DerivedCategory.Plus.Q ⟶
      DerivedCategory.Plus.Q ⋙ (pushforward f).rightDerivedFunctorPlus ⋙
        (restrictFunctor j).rightDerivedFunctorPlus ⋙ (restrictFunctor v).rightDerivedFunctorPlus :=
  Functor.rightDerivedFunctorPlusCompUnit (pushforward f)
      (restrictFunctor j ⋙ restrictFunctor v) ≫
    Functor.whiskerLeft DerivedCategory.Plus.Q
      (Functor.isoWhiskerLeft (pushforward f).rightDerivedFunctorPlus
        ((restrictFunctor j).rightDerivedFunctorPlusCompIsoOfPreservesHomology
          (restrictFunctor v))).hom

private theorem tripleUnit_derived :
    Functor.IsRightDerivedFunctor
      ((pushforward f).rightDerivedFunctorPlus ⋙
        (restrictFunctor j).rightDerivedFunctorPlus ⋙ (restrictFunctor v).rightDerivedFunctorPlus)
      (tripleUnit f j v) (CochainComplex.Plus.quasiIso W.Modules) := by
  let F := pushforward f
  let J := restrictFunctor j
  let V := restrictFunctor v
  let e := Functor.isoWhiskerLeft F.rightDerivedFunctorPlus
    (J.rightDerivedFunctorPlusCompIsoOfPreservesHomology V)
  let U := Functor.rightDerivedFunctorPlusCompUnit F (J ⋙ V)
  have h : Functor.IsRightDerivedFunctor
      (F.rightDerivedFunctorPlus ⋙ (J ⋙ V).rightDerivedFunctorPlus)
      U (CochainComplex.Plus.quasiIso W.Modules) :=
    F.isRightDerivedFunctor_comp_of_preservesHomology (J ⋙ V)
  exact (Functor.isRightDerivedFunctor_iff_of_iso (α := U)
    (tripleUnit f j v) (CochainComplex.Plus.quasiIso W.Modules) e rfl).mp h

private theorem tripleUnit_app (K : CochainComplex.Plus W.Modules) :
    (tripleUnit f j v).app K =
      (restrictFunctor v).rightDerivedFunctorPlusUnit.app
          ((pushforward f ⋙ restrictFunctor j).mapCochainComplexPlus.obj K) ≫
        (restrictFunctor v).rightDerivedFunctorPlus.map
          ((restrictFunctor j).rightDerivedFunctorPlusUnit.app
            ((pushforward f).mapCochainComplexPlus.obj K)) ≫
        (restrictFunctor v).rightDerivedFunctorPlus.map
          ((restrictFunctor j).rightDerivedFunctorPlus.map
            ((pushforward f).rightDerivedFunctorPlusUnit.app K)) := by
  let F := pushforward f
  let J := restrictFunctor j
  let V := restrictFunctor v
  let e := J.rightDerivedFunctorPlusCompIsoOfPreservesHomology V
  let η := F.rightDerivedFunctorPlusUnit.app K
  have hn := e.hom.naturality η
  change (J ⋙ V).rightDerivedFunctorPlus.map η ≫
      e.hom.app (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)) =
    e.hom.app (DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj K)) ≫
      (J.rightDerivedFunctorPlus ⋙ V.rightDerivedFunctorPlus).map η at hn
  change (Functor.rightDerivedFunctorPlusCompUnit F (J ⋙ V)).app K ≫
      e.hom.app (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)) = _
  rw [Functor.rightDerivedFunctorPlusCompUnit_app, Category.assoc, hn, ← Category.assoc,
    Functor.rightDerivedFunctorPlusCompIsoOfPreservesHomology_hom_app]
  simp only [Functor.comp_map, Category.assoc]
  rfl

private theorem tripleUnit_comp_normalization (K : CochainComplex.Plus W.Modules) :
    DerivedCategory.Plus.Q.map
          ((NatIso.mapCochainComplexPlus (restrictFunctorComp v j)).hom.app
            ((pushforward f).mapCochainComplexPlus.obj K)) ≫
        (tripleUnit f j v).app K =
      (Functor.rightDerivedFunctorPlusCompUnit (pushforward f)
        (restrictFunctor (v ≫ j))).app K ≫
        (derivedRestrictionCompIso v j).hom.app
          ((pushforward f).rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)) := by
  let F := pushforward f
  let J := restrictFunctor j
  let V := restrictFunctor v
  let JV := restrictFunctor (v ≫ j)
  let e := derivedRestrictionCompIso v j
  let η := F.rightDerivedFunctorPlusUnit.app K
  have hn := e.hom.naturality η
  change JV.rightDerivedFunctorPlus.map η ≫
      e.hom.app (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)) =
    e.hom.app (DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj K)) ≫
      (J.rightDerivedFunctorPlus ⋙ V.rightDerivedFunctorPlus).map η at hn
  have hu := derivedRestrictionCompIso_unit v j (F.mapCochainComplexPlus.obj K)
  change JV.rightDerivedFunctorPlusUnit.app (F.mapCochainComplexPlus.obj K) ≫
      e.hom.app (DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj K)) =
    DerivedCategory.Plus.Q.map
        ((NatIso.mapCochainComplexPlus (restrictFunctorComp v j)).hom.app
          (F.mapCochainComplexPlus.obj K)) ≫
      (Functor.rightDerivedFunctorPlusCompUnit J V).app (F.mapCochainComplexPlus.obj K) at hu
  symm
  rw [Functor.rightDerivedFunctorPlusCompUnit_app, Category.assoc, hn, ← Category.assoc, hu]
  simp only [tripleUnit_app, Functor.rightDerivedFunctorPlusCompUnit_app,
    Functor.comp_map, Category.assoc]
  rfl

private theorem tripleUnit_inv_derivedRestrictionCompIso (K : CochainComplex.Plus W.Modules) :
    (tripleUnit f j v).app K ≫
        (derivedRestrictionCompIso v j).inv.app
          ((pushforward f).rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)) =
      DerivedCategory.Plus.Q.map
          ((NatIso.mapCochainComplexPlus (restrictFunctorComp v j)).inv.app
            ((pushforward f).mapCochainComplexPlus.obj K)) ≫
        (Functor.rightDerivedFunctorPlusCompUnit (pushforward f)
          (restrictFunctor (v ≫ j))).app K := by
  let F := pushforward f
  let e := derivedRestrictionCompIso v j
  let ξ := (NatIso.mapCochainComplexPlus (restrictFunctorComp v j)).app
    (F.mapCochainComplexPlus.obj K)
  let U := (Functor.rightDerivedFunctorPlusCompUnit F (restrictFunctor (v ≫ j))).app K
  have hu := tripleUnit_comp_normalization f j v K
  change DerivedCategory.Plus.Q.map ξ.hom ≫ (tripleUnit f j v).app K =
    U ≫ e.hom.app (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)) at hu
  apply (cancel_epi (DerivedCategory.Plus.Q.map ξ.hom)).mp
  change DerivedCategory.Plus.Q.map ξ.hom ≫
      ((tripleUnit f j v).app K ≫ e.inv.app _) =
    DerivedCategory.Plus.Q.map ξ.hom ≫ (DerivedCategory.Plus.Q.map ξ.inv ≫ U)
  rw [← Category.assoc, hu, Category.assoc, Iso.hom_inv_id_app]
  erw [Category.comp_id]
  rw [← Functor.map_comp_assoc, ξ.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]


end TripleUnit

section Pasting

variable {X₀ X₁ X₂ Y₀ Y₁ Y₂ : Scheme.{u}}
  (a : X₁ ⟶ X₀) (b : X₁ ⟶ Y₁) (f : X₀ ⟶ Y₀) (j : Y₁ ⟶ Y₀)
  (c : X₂ ⟶ X₁) (d : X₂ ⟶ Y₂) (v : Y₂ ⟶ Y₁)
  [IsOpenImmersion a] [IsOpenImmersion c] [IsOpenImmersion j] [IsOpenImmersion v]
  (h : IsPullback a b f j) (h' : IsPullback c d b v)
  (H : IsPullback (c ≫ a) d f (v ≫ j))

private theorem rightUnit_normalization (K : CochainComplex.Plus X₀.Modules) :
    let A := restrictFunctor a
    let C := restrictFunctor c
    let D := pushforward d
    let V := restrictFunctor v
    let χ₁ := (NatIso.mapCochainComplexPlus (cartesianOpenBaseChange a b f j h)).hom.app K
    let χ₂ := (NatIso.mapCochainComplexPlus (cartesianOpenBaseChange c d b v h')).hom.app
      (A.mapCochainComplexPlus.obj K)
    (tripleUnit f j v).app K ≫
        V.rightDerivedFunctorPlus.map
          ((derivedOpenBaseChangeIso a b f j h).hom.app (DerivedCategory.Plus.Q.obj K)) ≫
        (derivedOpenBaseChangeIso c d b v h').hom.app
          (A.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)) =
      DerivedCategory.Plus.Q.map (V.mapCochainComplexPlus.map χ₁ ≫ χ₂) ≫
        D.rightDerivedFunctorPlusUnit.app
          (C.mapCochainComplexPlus.obj (A.mapCochainComplexPlus.obj K)) ≫
        D.rightDerivedFunctorPlus.map
          (C.rightDerivedFunctorPlusUnit.app (A.mapCochainComplexPlus.obj K)) ≫
        D.rightDerivedFunctorPlus.map
          (C.rightDerivedFunctorPlus.map (A.rightDerivedFunctorPlusUnit.app K)) := by
  let F := pushforward f
  let J := restrictFunctor j
  let A := restrictFunctor a
  let B := pushforward b
  let C := restrictFunctor c
  let D := pushforward d
  let V := restrictFunctor v
  let AK := A.mapCochainComplexPlus.obj K
  let χ₁ := (NatIso.mapCochainComplexPlus (cartesianOpenBaseChange a b f j h)).hom.app K
  let χ₂ := (NatIso.mapCochainComplexPlus (cartesianOpenBaseChange c d b v h')).hom.app AK
  let δ₁ := (derivedOpenBaseChangeIso a b f j h).hom
  let δ₂ := (derivedOpenBaseChangeIso c d b v h').hom
  let η := A.rightDerivedFunctorPlusUnit.app K
  have h₁ := derivedOpenBaseChangeIso_unit a b f j h K
  change (Functor.rightDerivedFunctorPlusCompUnit F J).app K ≫
      δ₁.app (DerivedCategory.Plus.Q.obj K) =
    DerivedCategory.Plus.Q.map χ₁ ≫ (Functor.rightDerivedFunctorPlusCompUnit A B).app K at h₁
  have h₂ := derivedOpenBaseChangeIso_unit c d b v h' AK
  change (Functor.rightDerivedFunctorPlusCompUnit B V).app AK ≫
      δ₂.app (DerivedCategory.Plus.Q.obj AK) =
    DerivedCategory.Plus.Q.map χ₂ ≫ (Functor.rightDerivedFunctorPlusCompUnit C D).app AK at h₂
  have hδ := δ₂.naturality η
  change V.rightDerivedFunctorPlus.map (B.rightDerivedFunctorPlus.map η) ≫
      δ₂.app (A.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)) =
    δ₂.app (DerivedCategory.Plus.Q.obj AK) ≫
      D.rightDerivedFunctorPlus.map (C.rightDerivedFunctorPlus.map η) at hδ
  have hV := V.rightDerivedFunctorPlusUnit.naturality χ₁
  change DerivedCategory.Plus.Q.map (V.mapCochainComplexPlus.map χ₁) ≫
      V.rightDerivedFunctorPlusUnit.app (B.mapCochainComplexPlus.obj AK) =
    V.rightDerivedFunctorPlusUnit.app ((F ⋙ J).mapCochainComplexPlus.obj K) ≫
      V.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map χ₁) at hV
  change (tripleUnit f j v).app K ≫
      V.rightDerivedFunctorPlus.map (δ₁.app (DerivedCategory.Plus.Q.obj K)) ≫
      δ₂.app (A.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)) = _
  calc
    _ = V.rightDerivedFunctorPlusUnit.app ((F ⋙ J).mapCochainComplexPlus.obj K) ≫
        V.rightDerivedFunctorPlus.map
          ((Functor.rightDerivedFunctorPlusCompUnit F J).app K ≫
            δ₁.app (DerivedCategory.Plus.Q.obj K)) ≫
        δ₂.app (A.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)) := by
      rw [tripleUnit_app, Functor.rightDerivedFunctorPlusCompUnit_app,
        Functor.map_comp, Functor.map_comp]
      simp only [Category.assoc]
      rfl
    _ = V.rightDerivedFunctorPlusUnit.app ((F ⋙ J).mapCochainComplexPlus.obj K) ≫
        V.rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map χ₁ ≫
            (Functor.rightDerivedFunctorPlusCompUnit A B).app K) ≫
        δ₂.app (A.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)) := by rw [h₁]
    _ = DerivedCategory.Plus.Q.map (V.mapCochainComplexPlus.map χ₁) ≫
        V.rightDerivedFunctorPlusUnit.app (B.mapCochainComplexPlus.obj AK) ≫
        V.rightDerivedFunctorPlus.map (B.rightDerivedFunctorPlusUnit.app AK) ≫
        V.rightDerivedFunctorPlus.map (B.rightDerivedFunctorPlus.map η) ≫
        δ₂.app (A.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)) := by
      simp only [Functor.map_comp, Functor.rightDerivedFunctorPlusCompUnit_app]
      simpa only [Category.assoc] using congrArg
        (fun z => z ≫ V.rightDerivedFunctorPlus.map (B.rightDerivedFunctorPlusUnit.app AK) ≫
          V.rightDerivedFunctorPlus.map (B.rightDerivedFunctorPlus.map η) ≫
          δ₂.app (A.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K))) hV.symm
    _ = DerivedCategory.Plus.Q.map (V.mapCochainComplexPlus.map χ₁) ≫
        (Functor.rightDerivedFunctorPlusCompUnit B V).app AK ≫
        δ₂.app (DerivedCategory.Plus.Q.obj AK) ≫
        D.rightDerivedFunctorPlus.map (C.rightDerivedFunctorPlus.map η) := by
      rw [Functor.rightDerivedFunctorPlusCompUnit_app]
      simp only [Category.assoc]
      rw [hδ]
    _ = DerivedCategory.Plus.Q.map (V.mapCochainComplexPlus.map χ₁) ≫
        DerivedCategory.Plus.Q.map χ₂ ≫
        (Functor.rightDerivedFunctorPlusCompUnit C D).app AK ≫
        D.rightDerivedFunctorPlus.map (C.rightDerivedFunctorPlus.map η) := by
      simpa only [Category.assoc] using congrArg
        (fun z => DerivedCategory.Plus.Q.map (V.mapCochainComplexPlus.map χ₁) ≫ z ≫
          D.rightDerivedFunctorPlus.map (C.rightDerivedFunctorPlus.map η)) h₂
    _ = _ := by
      rw [Functor.map_comp, Functor.rightDerivedFunctorPlusCompUnit_app]
      simp only [Category.assoc]
      rfl


private theorem ordinaryOpen_pasting (M : X₀.Modules) :
    (restrictFunctorComp v j).inv.app ((pushforward f).obj M) ≫
        (cartesianOpenBaseChange (c ≫ a) d f (v ≫ j) H).hom.app M ≫
        (pushforward d).map ((restrictFunctorComp c a).hom.app M) =
      (restrictFunctor v).map ((cartesianOpenBaseChange a b f j h).hom.app M) ≫
        (cartesianOpenBaseChange c d b v h').hom.app ((restrictFunctor a).obj M) := by
  apply Scheme.Modules.hom_ext
  intro U
  simp only [Scheme.Modules.Hom.comp_app, restrictFunctorComp_inv_app_app,
    cartesianOpenBaseChange_hom_app, Scheme.Modules.pushforward_map_app,
    restrictFunctorComp_hom_app_app, restrictFunctor_map_app]
  change M.presheaf.map _ ≫ M.presheaf.map _ ≫ M.presheaf.map _ =
    M.presheaf.map _ ≫ M.presheaf.map _
  simp only [← Functor.map_comp]
  congr 1

private def ordinaryLeft :
    pushforward f ⋙ restrictFunctor j ⋙ restrictFunctor v ⟶
      restrictFunctor a ⋙ restrictFunctor c ⋙ pushforward d :=
  Functor.whiskerLeft (pushforward f) (restrictFunctorComp v j).inv ≫
    (cartesianOpenBaseChange (c ≫ a) d f (v ≫ j) H).hom ≫
    Functor.whiskerRight (restrictFunctorComp c a).hom (pushforward d)

private def derivedLeft :
    (pushforward f).rightDerivedFunctorPlus ⋙
        (restrictFunctor j).rightDerivedFunctorPlus ⋙ (restrictFunctor v).rightDerivedFunctorPlus ⟶
      (restrictFunctor a).rightDerivedFunctorPlus ⋙
        (restrictFunctor c).rightDerivedFunctorPlus ⋙ (pushforward d).rightDerivedFunctorPlus :=
  Functor.whiskerLeft (pushforward f).rightDerivedFunctorPlus (derivedRestrictionCompIso v j).inv ≫
    (derivedOpenBaseChangeIso (c ≫ a) d f (v ≫ j) H).hom ≫
    Functor.whiskerRight (derivedRestrictionCompIso c a).hom (pushforward d).rightDerivedFunctorPlus

private def targetTripleUnit :
    (restrictFunctor a ⋙ restrictFunctor c ⋙ pushforward d).mapCochainComplexPlus ⋙
        DerivedCategory.Plus.Q ⟶
      DerivedCategory.Plus.Q ⋙ (restrictFunctor a).rightDerivedFunctorPlus ⋙
        (restrictFunctor c).rightDerivedFunctorPlus ⋙ (pushforward d).rightDerivedFunctorPlus :=
  Functor.whiskerRight (Functor.mapCochainComplexPlusCompIso
      (restrictFunctor a ⋙ restrictFunctor c) (pushforward d)).hom DerivedCategory.Plus.Q ≫
    Functor.whiskerLeft (restrictFunctor a ⋙ restrictFunctor c).mapCochainComplexPlus
      (pushforward d).rightDerivedFunctorPlusUnit ≫
    Functor.whiskerRight (Functor.rightDerivedFunctorPlusCompUnit
      (restrictFunctor a) (restrictFunctor c)) (pushforward d).rightDerivedFunctorPlus

private theorem targetTripleUnit_app (K : CochainComplex.Plus X₀.Modules) :
    (targetTripleUnit a c d).app K =
      (pushforward d).rightDerivedFunctorPlusUnit.app
          ((restrictFunctor c).mapCochainComplexPlus.obj
            ((restrictFunctor a).mapCochainComplexPlus.obj K)) ≫
        (pushforward d).rightDerivedFunctorPlus.map
          ((restrictFunctor c).rightDerivedFunctorPlusUnit.app
            ((restrictFunctor a).mapCochainComplexPlus.obj K)) ≫
        (pushforward d).rightDerivedFunctorPlus.map
          ((restrictFunctor c).rightDerivedFunctorPlus.map
            ((restrictFunctor a).rightDerivedFunctorPlusUnit.app K)) := by
  simp only [targetTripleUnit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.mapCochainComplexPlusCompIso,
    NatIso.ofComponents_hom_app, Iso.refl_hom, CategoryTheory.Functor.map_id,
    Functor.rightDerivedFunctorPlusCompUnit_app, Functor.map_comp]
  erw [Category.id_comp]
  rfl

private theorem targetStage_normalization (K : CochainComplex.Plus X₀.Modules) :
    (Functor.rightDerivedFunctorPlusCompUnit (restrictFunctor (c ≫ a))
        (pushforward d)).app K ≫
        (pushforward d).rightDerivedFunctorPlus.map
          ((derivedRestrictionCompIso c a).hom.app (DerivedCategory.Plus.Q.obj K)) =
      DerivedCategory.Plus.Q.map
          ((pushforward d).mapCochainComplexPlus.map
            ((NatIso.mapCochainComplexPlus (restrictFunctorComp c a)).hom.app K)) ≫
        (targetTripleUnit a c d).app K := by
  let A := restrictFunctor a
  let C := restrictFunctor c
  let AC := restrictFunctor (c ≫ a)
  let D := pushforward d
  let AK := A.mapCochainComplexPlus.obj K
  let χ := (NatIso.mapCochainComplexPlus (restrictFunctorComp c a)).hom.app K
  let e := derivedRestrictionCompIso c a
  have hu := derivedRestrictionCompIso_unit c a K
  change AC.rightDerivedFunctorPlusUnit.app K ≫ e.hom.app (DerivedCategory.Plus.Q.obj K) =
    DerivedCategory.Plus.Q.map χ ≫ (Functor.rightDerivedFunctorPlusCompUnit A C).app K at hu
  have hD := D.rightDerivedFunctorPlusUnit.naturality χ
  change DerivedCategory.Plus.Q.map (D.mapCochainComplexPlus.map χ) ≫
      D.rightDerivedFunctorPlusUnit.app (C.mapCochainComplexPlus.obj AK) =
    D.rightDerivedFunctorPlusUnit.app (AC.mapCochainComplexPlus.obj K) ≫
      D.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map χ) at hD
  rw [Functor.rightDerivedFunctorPlusCompUnit_app]
  simp only [Category.assoc]
  change D.rightDerivedFunctorPlusUnit.app (AC.mapCochainComplexPlus.obj K) ≫
      D.rightDerivedFunctorPlus.map (AC.rightDerivedFunctorPlusUnit.app K) ≫
      D.rightDerivedFunctorPlus.map (e.hom.app (DerivedCategory.Plus.Q.obj K)) = _
  rw [← Functor.map_comp, hu, Functor.map_comp]
  have hh := congrArg
    (fun z => z ≫ D.rightDerivedFunctorPlus.map
      (Functor.rightDerivedFunctorPlusCompUnit A C |>.app K)) hD.symm
  rw [targetTripleUnit_app]
  rw [Functor.rightDerivedFunctorPlusCompUnit_app, Functor.map_comp] at hh
  rw [Functor.rightDerivedFunctorPlusCompUnit_app, Functor.map_comp]
  simpa only [Category.assoc] using hh


private def ordinarySource :
    pushforward f ⋙ restrictFunctor j ⋙ restrictFunctor v ⟶
      pushforward f ⋙ restrictFunctor (v ≫ j) :=
  Functor.whiskerLeft (pushforward f) (restrictFunctorComp v j).inv

private def derivedSource :
    (pushforward f).rightDerivedFunctorPlus ⋙
        (restrictFunctor j).rightDerivedFunctorPlus ⋙ (restrictFunctor v).rightDerivedFunctorPlus ⟶
      (pushforward f).rightDerivedFunctorPlus ⋙ (restrictFunctor (v ≫ j)).rightDerivedFunctorPlus :=
  Functor.whiskerLeft (pushforward f).rightDerivedFunctorPlus (derivedRestrictionCompIso v j).inv

private def ordinaryTarget :
    restrictFunctor (c ≫ a) ⋙ pushforward d ⟶
      restrictFunctor a ⋙ restrictFunctor c ⋙ pushforward d :=
  Functor.whiskerRight (restrictFunctorComp c a).hom (pushforward d)

private def derivedTarget :
    (restrictFunctor (c ≫ a)).rightDerivedFunctorPlus ⋙ (pushforward d).rightDerivedFunctorPlus ⟶
      (restrictFunctor a).rightDerivedFunctorPlus ⋙
        (restrictFunctor c).rightDerivedFunctorPlus ⋙ (pushforward d).rightDerivedFunctorPlus :=
  Functor.whiskerRight (derivedRestrictionCompIso c a).hom (pushforward d).rightDerivedFunctorPlus

private theorem sourceStage :
    tripleUnit f j v ≫
        Functor.whiskerLeft (DerivedCategory.Plus.Q (C := X₀.Modules)) (derivedSource f j v) =
      Functor.whiskerRight (NatTrans.mapCochainComplexPlus (ordinarySource f j v))
          (DerivedCategory.Plus.Q (C := Y₂.Modules)) ≫
        Functor.rightDerivedFunctorPlusCompUnit (pushforward f) (restrictFunctor (v ≫ j)) := by
  apply NatTrans.ext
  funext K
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  have hχ : (NatTrans.mapCochainComplexPlus (ordinarySource f j v)).app K =
      (NatIso.mapCochainComplexPlus (restrictFunctorComp v j)).inv.app
        ((pushforward f).mapCochainComplexPlus.obj K) := by
    apply ObjectProperty.hom_ext
    ext i : 1
    rfl
  rw [hχ]
  exact tripleUnit_inv_derivedRestrictionCompIso f j v K

private theorem targetStage :
    Functor.rightDerivedFunctorPlusCompUnit (restrictFunctor (c ≫ a)) (pushforward d) ≫
        Functor.whiskerLeft (DerivedCategory.Plus.Q (C := X₀.Modules)) (derivedTarget a c d) =
      Functor.whiskerRight (NatTrans.mapCochainComplexPlus (ordinaryTarget a c d))
          (DerivedCategory.Plus.Q (C := Y₂.Modules)) ≫
        targetTripleUnit a c d := by
  apply NatTrans.ext
  funext K
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  have hχ : (NatTrans.mapCochainComplexPlus (ordinaryTarget a c d)).app K =
      (pushforward d).mapCochainComplexPlus.map
        ((NatIso.mapCochainComplexPlus (restrictFunctorComp c a)).hom.app K) := by
    apply ObjectProperty.hom_ext
    ext i : 1
    rfl
  rw [hχ]
  exact targetStage_normalization a c d K

private theorem middleStage :
    Functor.rightDerivedFunctorPlusCompUnit (pushforward f) (restrictFunctor (v ≫ j)) ≫
        Functor.whiskerLeft (DerivedCategory.Plus.Q (C := X₀.Modules))
          (derivedOpenBaseChangeIso (c ≫ a) d f (v ≫ j) H).hom =
      Functor.whiskerRight
          (NatTrans.mapCochainComplexPlus
            (cartesianOpenBaseChange (c ≫ a) d f (v ≫ j) H).hom)
          (DerivedCategory.Plus.Q (C := Y₂.Modules)) ≫
        Functor.rightDerivedFunctorPlusCompUnit (restrictFunctor (c ≫ a)) (pushforward d) := by
  apply NatTrans.ext
  funext K
  exact derivedOpenBaseChangeIso_unit (c ≫ a) d f (v ≫ j) H K

private theorem leftUnit_normalization :
    tripleUnit f j v ≫
        Functor.whiskerLeft (DerivedCategory.Plus.Q (C := X₀.Modules))
          (derivedLeft a f j c d v H) =
      Functor.whiskerRight
          (NatTrans.mapCochainComplexPlus (ordinaryLeft a f j c d v H))
          (DerivedCategory.Plus.Q (C := Y₂.Modules)) ≫
        targetTripleUnit a c d := by
  let Q₀ := DerivedCategory.Plus.Q (C := X₀.Modules)
  let Q₂ := DerivedCategory.Plus.Q (C := Y₂.Modules)
  let A := tripleUnit f j v
  let S := Functor.whiskerLeft Q₀ (derivedSource f j v)
  let O := Functor.whiskerLeft Q₀ (derivedOpenBaseChangeIso (c ≫ a) d f (v ≫ j) H).hom
  let T := Functor.whiskerLeft Q₀ (derivedTarget a c d)
  let s := Functor.whiskerRight (NatTrans.mapCochainComplexPlus (ordinarySource f j v)) Q₂
  let o := Functor.whiskerRight
    (NatTrans.mapCochainComplexPlus (cartesianOpenBaseChange (c ≫ a) d f (v ≫ j) H).hom) Q₂
  let t := Functor.whiskerRight (NatTrans.mapCochainComplexPlus (ordinaryTarget a c d)) Q₂
  let U := Functor.rightDerivedFunctorPlusCompUnit (pushforward f) (restrictFunctor (v ≫ j))
  let V := Functor.rightDerivedFunctorPlusCompUnit (restrictFunctor (c ≫ a)) (pushforward d)
  have hS : A ≫ S = s ≫ U := sourceStage f j v
  have hO : U ≫ O = o ≫ V := middleStage a f j c d v H
  have hT : V ≫ T = t ≫ targetTripleUnit a c d := targetStage a c d
  have hL : Functor.whiskerLeft Q₀ (derivedLeft a f j c d v H) = S ≫ O ≫ T := by
    rfl
  have hR : Functor.whiskerRight
      (NatTrans.mapCochainComplexPlus (ordinaryLeft a f j c d v H)) Q₂ = s ≫ o ≫ t := by
    rw [ordinaryLeft, NatTrans.mapCochainComplexPlus_comp, NatTrans.mapCochainComplexPlus_comp,
      Functor.whiskerRight_comp, Functor.whiskerRight_comp]
    rfl
  change A ≫ Functor.whiskerLeft Q₀ (derivedLeft a f j c d v H) = _
  rw [hL, hR]
  calc
    _ = (A ≫ S) ≫ O ≫ T := by simp only [Category.assoc]
    _ = (s ≫ U) ≫ O ≫ T := by rw [hS]
    _ = s ≫ (U ≫ O) ≫ T := by simp only [Category.assoc]
    _ = s ≫ (o ≫ V) ≫ T := by rw [hO]
    _ = s ≫ o ≫ (V ≫ T) := by simp only [Category.assoc]
    _ = s ≫ o ≫ (t ≫ targetTripleUnit a c d) := by rw [hT]
    _ = _ := by simp only [Category.assoc]


private def ordinaryRight :
    pushforward f ⋙ restrictFunctor j ⋙ restrictFunctor v ⟶
      restrictFunctor a ⋙ restrictFunctor c ⋙ pushforward d :=
  Functor.whiskerRight (cartesianOpenBaseChange a b f j h).hom (restrictFunctor v) ≫
    Functor.whiskerLeft (restrictFunctor a) (cartesianOpenBaseChange c d b v h').hom

private def derivedRight :
    (pushforward f).rightDerivedFunctorPlus ⋙
        (restrictFunctor j).rightDerivedFunctorPlus ⋙ (restrictFunctor v).rightDerivedFunctorPlus ⟶
      (restrictFunctor a).rightDerivedFunctorPlus ⋙
        (restrictFunctor c).rightDerivedFunctorPlus ⋙ (pushforward d).rightDerivedFunctorPlus :=
  Functor.whiskerRight (derivedOpenBaseChangeIso a b f j h).hom
      (restrictFunctor v).rightDerivedFunctorPlus ≫
    Functor.whiskerLeft (restrictFunctor a).rightDerivedFunctorPlus
      (derivedOpenBaseChangeIso c d b v h').hom

private theorem ordinaryOpen_pasting_natTrans :
    ordinaryLeft a f j c d v H = ordinaryRight a b f j c d v h h' := by
  apply NatTrans.ext
  funext M
  change (restrictFunctorComp v j).inv.app ((pushforward f).obj M) ≫
      (cartesianOpenBaseChange (c ≫ a) d f (v ≫ j) H).hom.app M ≫
      (pushforward d).map ((restrictFunctorComp c a).hom.app M) = _
  exact ordinaryOpen_pasting a b f j c d v h h' H M

private theorem rightUnit_normalization_typed :
    tripleUnit f j v ≫
        Functor.whiskerLeft (DerivedCategory.Plus.Q (C := X₀.Modules))
          (derivedRight a b f j c d v h h') =
      Functor.whiskerRight
          (NatTrans.mapCochainComplexPlus (ordinaryRight a b f j c d v h h'))
          (DerivedCategory.Plus.Q (C := Y₂.Modules)) ≫
        targetTripleUnit a c d := by
  apply NatTrans.ext
  funext K
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  let A := restrictFunctor a
  let V := restrictFunctor v
  let χ₁ := (NatIso.mapCochainComplexPlus (cartesianOpenBaseChange a b f j h)).hom.app K
  let χ₂ := (NatIso.mapCochainComplexPlus (cartesianOpenBaseChange c d b v h')).hom.app
    (A.mapCochainComplexPlus.obj K)
  have hχ :
      (NatTrans.mapCochainComplexPlus (ordinaryRight a b f j c d v h h')).app K =
        V.mapCochainComplexPlus.map χ₁ ≫ χ₂ := by
    apply ObjectProperty.hom_ext
    ext i : 1
    rfl
  rw [hχ, targetTripleUnit_app]
  exact rightUnit_normalization a b f j c d v h h' K

private theorem derivedOpen_pasting_natTrans :
    derivedLeft a f j c d v H = derivedRight a b f j c d v h h' := by
  let F := (pushforward f).rightDerivedFunctorPlus ⋙
    (restrictFunctor j).rightDerivedFunctorPlus ⋙ (restrictFunctor v).rightDerivedFunctorPlus
  let T := (restrictFunctor a).rightDerivedFunctorPlus ⋙
    (restrictFunctor c).rightDerivedFunctorPlus ⋙ (pushforward d).rightDerivedFunctorPlus
  let : F.IsRightDerivedFunctor (tripleUnit f j v) (CochainComplex.Plus.quasiIso X₀.Modules) :=
    tripleUnit_derived f j v
  apply F.rightDerived_ext (tripleUnit f j v) (CochainComplex.Plus.quasiIso X₀.Modules) T
  rw [leftUnit_normalization, rightUnit_normalization_typed]
  rw [ordinaryOpen_pasting_natTrans a b f j c d v h h' H]


end Pasting

section SingleComplex

variable {X Y Z : Scheme.{u}} (F : X.Modules ⥤ Y.Modules) [F.Additive]

private def singleComplexIso (M : X.Modules) :
    F.mapCochainComplexPlus.obj ((CochainComplex.singleFunctorPlus X.Modules 0).obj M) ≅
      (CochainComplex.singleFunctorPlus Y.Modules 0).obj (F.obj M) :=
  (CochainComplex.plus Y.Modules).isoMk
    ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app M)

private theorem singleComplexIso_unit [F.PreservesHomology] (M : X.Modules) :
    F.rightDerivedFunctorPlusUnit.app ((CochainComplex.singleFunctorPlus X.Modules 0).obj M) ≫
        (F.rightDerivedFunctorPlusSingleIso 0).hom.app M =
      DerivedCategory.Plus.Q.map (singleComplexIso F M).hom :=
  F.rightDerivedFunctorPlusSingleIso_unit 0 M

private theorem singleComplexIso_comp (G : Y.Modules ⥤ Z.Modules) [G.Additive]
    (M : X.Modules) :
    (singleComplexIso (F ⋙ G) M).hom =
      G.mapCochainComplexPlus.map (singleComplexIso F M).hom ≫
        (singleComplexIso G (F.obj M)).hom := by
  apply ObjectProperty.hom_ext
  change (HomologicalComplex.singleMapHomologicalComplex (F ⋙ G) (.up ℤ) 0).hom.app M =
    (G.mapHomologicalComplex (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app M) ≫
      (HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).hom.app (F.obj M)
  simpa only [Functor.mapHomologicalComplexCompIso, NatIso.mapHomologicalComplex,
    Iso.refl_inv, NatTrans.mapHomologicalComplex_id, NatTrans.id_app, Category.id_comp] using
    HomologicalComplex.singleMapHomologicalComplex_comp_hom_app F G (.up ℤ) (0 : ℤ) M

private theorem singleComplexIso_naturality {G : X.Modules ⥤ Y.Modules} [G.Additive]
    (τ : F ⟶ G) (M : X.Modules) :
    (NatTrans.mapCochainComplexPlus τ).app ((CochainComplex.singleFunctorPlus X.Modules 0).obj M) ≫
        (singleComplexIso G M).hom =
      (singleComplexIso F M).hom ≫
        (CochainComplex.singleFunctorPlus Y.Modules 0).map (τ.app M) := by
  apply ObjectProperty.hom_ext
  change (τ.mapHomologicalComplex (.up ℤ)).app
        ((HomologicalComplex.single X.Modules (.up ℤ) 0).obj M) ≫
      (HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).hom.app M =
    (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app M ≫
      (HomologicalComplex.single Y.Modules (.up ℤ) 0).map (τ.app M)
  rw [HomologicalComplex.natTransMapHomologicalComplex_app_single_obj]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]


end SingleComplex

section CompositeSingle

variable {X Y Z : Scheme.{u}} (F : X.Modules ⥤ Y.Modules) (G : Y.Modules ⥤ Z.Modules)
  [F.Additive] [G.Additive] [F.PreservesHomology] [G.PreservesHomology]

private theorem compositeSingleUnit (M : X.Modules) :
    (Functor.rightDerivedFunctorPlusCompUnit F G).app
          ((CochainComplex.singleFunctorPlus X.Modules 0).obj M) ≫
        G.rightDerivedFunctorPlus.map ((F.rightDerivedFunctorPlusSingleIso 0).hom.app M) ≫
        (G.rightDerivedFunctorPlusSingleIso 0).hom.app (F.obj M) =
      DerivedCategory.Plus.Q.map (singleComplexIso (F ⋙ G) M).hom := by
  let K := (CochainComplex.singleFunctorPlus X.Modules 0).obj M
  let eF := F.rightDerivedFunctorPlusSingleIso 0
  let eG := G.rightDerivedFunctorPlusSingleIso 0
  let sF := singleComplexIso F M
  let sG := singleComplexIso G (F.obj M)
  have hF := singleComplexIso_unit F M
  have hG := singleComplexIso_unit G (F.obj M)
  have hn := G.rightDerivedFunctorPlusUnit.naturality sF.hom
  change DerivedCategory.Plus.Q.map (G.mapCochainComplexPlus.map sF.hom) ≫
      G.rightDerivedFunctorPlusUnit.app
        ((CochainComplex.singleFunctorPlus Y.Modules 0).obj (F.obj M)) =
    G.rightDerivedFunctorPlusUnit.app (F.mapCochainComplexPlus.obj K) ≫
      G.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map sF.hom) at hn
  rw [Functor.rightDerivedFunctorPlusCompUnit_app]
  simp only [Category.assoc]
  rw [← Category.assoc (G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnit.app K))
    (G.rightDerivedFunctorPlus.map (eF.hom.app M)), ← Functor.map_comp, hF]
  rw [← Category.assoc (G.rightDerivedFunctorPlusUnit.app (F.mapCochainComplexPlus.obj K))
    (G.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map sF.hom)), ← hn]
  simp only [Category.assoc]
  rw [hG, ← Functor.map_comp, ← singleComplexIso_comp F G M]


end CompositeSingle

section DerivedSingle

variable {U V X : Scheme.{u}} (a : U ⟶ V) (j : V ⟶ X)
  [IsOpenImmersion a] [IsOpenImmersion j] (M : X.Modules)

private theorem derivedRestrictionCompIso_single :
    (derivedRestrictionCompIso a j).hom.app
          ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M) ≫
        (restrictFunctor a).rightDerivedFunctorPlus.map
          (((restrictFunctor j).rightDerivedFunctorPlusSingleIso 0).hom.app M) ≫
        ((restrictFunctor a).rightDerivedFunctorPlusSingleIso 0).hom.app
          ((restrictFunctor j).obj M) =
      ((restrictFunctor (a ≫ j)).rightDerivedFunctorPlusSingleIso 0).hom.app M ≫
        (DerivedCategory.Plus.singleFunctor U.Modules 0).map
          ((restrictFunctorComp a j).hom.app M) := by
  let J := restrictFunctor j
  let A := restrictFunctor a
  let JA := restrictFunctor (a ≫ j)
  let K := (CochainComplex.singleFunctorPlus X.Modules 0).obj M
  let e := derivedRestrictionCompIso a j
  let eJ := J.rightDerivedFunctorPlusSingleIso 0
  let eA := A.rightDerivedFunctorPlusSingleIso 0
  let eJA := JA.rightDerivedFunctorPlusSingleIso 0
  let : IsIso JA.rightDerivedFunctorPlusUnit :=
    JA.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  have he := derivedRestrictionCompIso_unit a j K
  have huJA := singleComplexIso_unit JA M
  apply (cancel_epi (JA.rightDerivedFunctorPlusUnit.app K)).mp
  change JA.rightDerivedFunctorPlusUnit.app K ≫
      e.hom.app (DerivedCategory.Plus.Q.obj K) ≫
      A.rightDerivedFunctorPlus.map (eJ.hom.app M) ≫ eA.hom.app (J.obj M) =
    JA.rightDerivedFunctorPlusUnit.app K ≫ eJA.hom.app M ≫
      (DerivedCategory.Plus.singleFunctor U.Modules 0).map ((restrictFunctorComp a j).hom.app M)
  rw [← Category.assoc (JA.rightDerivedFunctorPlusUnit.app K)
    (e.hom.app (DerivedCategory.Plus.Q.obj K)), he]
  simp only [Category.assoc]
  rw [compositeSingleUnit J A M]
  rw [← Category.assoc (JA.rightDerivedFunctorPlusUnit.app K) (eJA.hom.app M), huJA]
  have hn := singleComplexIso_naturality JA (restrictFunctorComp a j).hom M
  have hQ := congrArg (DerivedCategory.Plus.Q (C := U.Modules)).map hn
  simp only [Functor.map_comp] at hQ
  exact hQ


end DerivedSingle

section Homology

variable {U V X : Scheme.{u}} (a : U ⟶ V) (j : V ⟶ X)
  [IsOpenImmersion a] [IsOpenImmersion j] (n : ℤ)

private def homologyCompLeft :
    (restrictFunctor (a ≫ j)).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor U.Modules n ⟶
      DerivedCategory.Plus.homologyFunctor X.Modules n ⋙ restrictFunctor j ⋙ restrictFunctor a :=
  Functor.whiskerRight (derivedRestrictionCompIso a j).hom
      (DerivedCategory.Plus.homologyFunctor U.Modules n) ≫
    Functor.whiskerLeft (restrictFunctor j).rightDerivedFunctorPlus
      ((restrictFunctor a).rightDerivedFunctorPlusHomologyIso n).hom ≫
    Functor.whiskerRight ((restrictFunctor j).rightDerivedFunctorPlusHomologyIso n).hom
      (restrictFunctor a)

private def homologyCompRight :
    (restrictFunctor (a ≫ j)).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor U.Modules n ⟶
      DerivedCategory.Plus.homologyFunctor X.Modules n ⋙ restrictFunctor j ⋙ restrictFunctor a :=
  ((restrictFunctor (a ≫ j)).rightDerivedFunctorPlusHomologyIso n).hom ≫
    Functor.whiskerLeft (DerivedCategory.Plus.homologyFunctor X.Modules n)
      (restrictFunctorComp a j).hom

private theorem derivedRestrictionCompIso_homology :
    homologyCompLeft a j n = homologyCompRight a j n := by
  apply Localization.natTrans_ext (DerivedCategory.Plus.Q (C := X.Modules))
    (CochainComplex.Plus.quasiIso X.Modules)
  intro K
  dsimp only [homologyCompLeft, homologyCompRight, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  let J := restrictFunctor j
  let A := restrictFunctor a
  let JA := restrictFunctor (a ≫ j)
  let H₀ := DerivedCategory.Plus.homologyFunctor X.Modules n
  let H₁ := DerivedCategory.Plus.homologyFunctor V.Modules n
  let H₂ := DerivedCategory.Plus.homologyFunctor U.Modules n
  let KJ := J.mapCochainComplexPlus.obj K
  let KJA := A.mapCochainComplexPlus.obj KJ
  let K₀ := JA.mapCochainComplexPlus.obj K
  let P := (DerivedCategory.Plus.homologyFunctorFactors (A := X.Modules) n).app K
  let PJ := (DerivedCategory.Plus.homologyFunctorFactors (A := V.Modules) n).app KJ
  let PJA := (DerivedCategory.Plus.homologyFunctorFactors (A := U.Modules) n).app KJA
  let P₀ := (DerivedCategory.Plus.homologyFunctorFactors (A := U.Modules) n).app K₀
  let e := derivedRestrictionCompIso a j
  let eJ := J.rightDerivedFunctorPlusHomologyIso n
  let eA := A.rightDerivedFunctorPlusHomologyIso n
  let eJA := JA.rightDerivedFunctorPlusHomologyIso n
  let ξ := (NatIso.mapCochainComplexPlus (restrictFunctorComp a j)).hom.app K
  let : IsIso JA.rightDerivedFunctorPlusUnit :=
    JA.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  have he := congrArg H₂.map (derivedRestrictionCompIso_unit a j K)
  simp only [Functor.map_comp] at he
  have hA := eA.hom.naturality (J.rightDerivedFunctorPlusUnit.app K)
  change H₂.map (A.rightDerivedFunctorPlus.map (J.rightDerivedFunctorPlusUnit.app K)) ≫
      eA.hom.app (J.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)) =
    eA.hom.app (DerivedCategory.Plus.Q.obj KJ) ≫
      A.map (H₁.map (J.rightDerivedFunctorPlusUnit.app K)) at hA
  have hJunit := J.rightDerivedFunctorPlusHomologyIso_unit n K
  change H₁.map (J.rightDerivedFunctorPlusUnit.app K) ≫
      eJ.hom.app (DerivedCategory.Plus.Q.obj K) ≫ J.map P.hom =
    PJ.hom ≫ ((K.obj.sc n).mapHomologyIso J).hom at hJunit
  have hAunit := A.rightDerivedFunctorPlusHomologyIso_unit n KJ
  change H₂.map (A.rightDerivedFunctorPlusUnit.app KJ) ≫
      eA.hom.app (DerivedCategory.Plus.Q.obj KJ) ≫ A.map PJ.hom =
    PJA.hom ≫ ((KJ.obj.sc n).mapHomologyIso A).hom at hAunit
  have hJAunit := JA.rightDerivedFunctorPlusHomologyIso_unit n K
  change H₂.map (JA.rightDerivedFunctorPlusUnit.app K) ≫
      eJA.hom.app (DerivedCategory.Plus.Q.obj K) ≫ JA.map P.hom =
    P₀.hom ≫ ((K.obj.sc n).mapHomologyIso JA).hom at hJAunit
  have hξ := (restrictFunctorComp a j).hom.naturality P.hom
  change JA.map P.hom ≫ (restrictFunctorComp a j).hom.app (K.obj.homology n) =
    (restrictFunctorComp a j).hom.app (H₀.obj (DerivedCategory.Plus.Q.obj K)) ≫
      A.map (J.map P.hom) at hξ
  have hSC := NatTrans.app_homology (restrictFunctorComp a j).hom (K.obj.sc n)
  change (restrictFunctorComp a j).hom.app (K.obj.homology n) =
    ((K.obj.sc n).mapHomologyIso JA).inv ≫ homologyMap ξ.hom n ≫
      ((K.obj.sc n).mapHomologyIso (J ⋙ A)).hom at hSC
  have hP := (DerivedCategory.Plus.homologyFunctorFactors (A := U.Modules) n).hom.naturality ξ
  change H₂.map (DerivedCategory.Plus.Q.map ξ) ≫ PJA.hom =
    P₀.hom ≫ homologyMap ξ.hom n at hP
  apply (cancel_epi (H₂.map (JA.rightDerivedFunctorPlusUnit.app K))).mp
  apply (cancel_mono (A.map (J.map P.hom))).mp
  simp only [Category.assoc]
  conv_lhs =>
    rw [← Category.assoc (H₂.map (JA.rightDerivedFunctorPlusUnit.app K))
      (H₂.map (e.hom.app (DerivedCategory.Plus.Q.obj K))), he]
    simp only [Category.assoc]
    rw [Functor.rightDerivedFunctorPlusCompUnit_app, Functor.map_comp]
    simp only [Category.assoc]
    rw [← Category.assoc
      (H₂.map (A.rightDerivedFunctorPlus.map (J.rightDerivedFunctorPlusUnit.app K)))
      (eA.hom.app (J.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K))), hA]
    simp only [Category.assoc]
    rw [← A.map_comp (eJ.hom.app (DerivedCategory.Plus.Q.obj K)) (J.map P.hom)]
    rw [← A.map_comp (H₁.map (J.rightDerivedFunctorPlusUnit.app K))
      (eJ.hom.app (DerivedCategory.Plus.Q.obj K) ≫ J.map P.hom)]
    rw [hJunit, A.map_comp]
    rw [← Category.assoc (eA.hom.app (DerivedCategory.Plus.Q.obj KJ)) (A.map PJ.hom)]
    rw [← Category.assoc (H₂.map (A.rightDerivedFunctorPlusUnit.app KJ))
      (eA.hom.app (DerivedCategory.Plus.Q.obj KJ) ≫ A.map PJ.hom), hAunit]
    simp only [Category.assoc]
  conv_rhs =>
    rw [← hξ]
    rw [← Category.assoc (eJA.hom.app (DerivedCategory.Plus.Q.obj K)) (JA.map P.hom)]
    rw [← Category.assoc (H₂.map (JA.rightDerivedFunctorPlusUnit.app K))
      (eJA.hom.app (DerivedCategory.Plus.Q.obj K) ≫ JA.map P.hom), hJAunit]
    simp only [Category.assoc]
    rw [hSC]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc P₀.hom (homologyMap ξ.hom n), ← hP]
    rw [ShortComplex.mapHomologyIso_comp_hom J A (K.obj.sc n)]
    simp only [Category.assoc]
  rfl


end Homology

section HomologyInverse

variable {U V X : Scheme.{u}} (a : U ⟶ V) (j : V ⟶ X)
  [IsOpenImmersion a] [IsOpenImmersion j] (n : ℤ)

private theorem derivedRestrictionCompIso_homology_inv (K : DerivedCategory.Plus X.Modules) :
    (restrictFunctorComp a j).inv.app ((DerivedCategory.Plus.homologyFunctor X.Modules n).obj K) ≫
        ((restrictFunctor (a ≫ j)).rightDerivedFunctorPlusHomologyIso n).inv.app K =
      (restrictFunctor a).map
        (((restrictFunctor j).rightDerivedFunctorPlusHomologyIso n).inv.app K) ≫
        ((restrictFunctor a).rightDerivedFunctorPlusHomologyIso n).inv.app
          ((restrictFunctor j).rightDerivedFunctorPlus.obj K) ≫
        (DerivedCategory.Plus.homologyFunctor U.Modules n).map
          ((derivedRestrictionCompIso a j).inv.app K) := by
  let J := restrictFunctor j
  let A := restrictFunctor a
  let JA := restrictFunctor (a ≫ j)
  let H₀ := DerivedCategory.Plus.homologyFunctor X.Modules n
  let H₂ := DerivedCategory.Plus.homologyFunctor U.Modules n
  let e := derivedRestrictionCompIso a j
  let eJ := J.rightDerivedFunctorPlusHomologyIso n
  let eA := A.rightDerivedFunctorPlusHomologyIso n
  let eJA := JA.rightDerivedFunctorPlusHomologyIso n
  let L := H₂.mapIso (e.app K) ≪≫ eA.app (J.rightDerivedFunctorPlus.obj K) ≪≫ A.mapIso (eJ.app K)
  let R := eJA.app K ≪≫ (restrictFunctorComp a j).app (H₀.obj K)
  have h := congrArg (fun η => η.app K) (derivedRestrictionCompIso_homology a j n)
  change L.hom = R.hom at h
  have hi := congrArg Iso.inv (Iso.ext h : L = R)
  simpa only [L, R, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Category.assoc] using hi.symm

end HomologyInverse

section HigherModel

variable {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  [IsOpenImmersion a] [IsOpenImmersion j] (h : IsPullback a b f j)
  (M : U.Modules) (n : ℕ)

private theorem higherOpen_app_model :
    (higherDirectImageOpenRestrictionIso a b f j h n).hom.app M =
      (restrictFunctor j).map (((pushforward f).rightDerivedSingleHomologyIso n).hom.app M) ≫
        ((restrictFunctor j).rightDerivedFunctorPlusHomologyIso (n : ℤ)).inv.app
          ((pushforward f).rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.singleFunctor U.Modules 0).obj M)) ≫
        (DerivedCategory.Plus.homologyFunctor V.Modules (n : ℤ)).map
          ((derivedOpenBaseChangeIso a b f j h).hom.app
            ((DerivedCategory.Plus.singleFunctor U.Modules 0).obj M)) ≫
        (DerivedCategory.Plus.homologyFunctor V.Modules (n : ℤ)).map
          ((pushforward b).rightDerivedFunctorPlus.map
            (((restrictFunctor a).rightDerivedFunctorPlusSingleIso 0).hom.app M)) ≫
        ((pushforward b).rightDerivedSingleHomologyIso n).inv.app ((restrictFunctor a).obj M) := by
  simp only [higherDirectImageOpenRestrictionIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.comp_obj, Category.id_comp]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

end HigherModel

section HigherPasting

variable {X₀ X₁ X₂ Y₀ Y₁ Y₂ : Scheme.{u}}
  (a : X₁ ⟶ X₀) (b : X₁ ⟶ Y₁) (f : X₀ ⟶ Y₀) (j : Y₁ ⟶ Y₀)
  (c : X₂ ⟶ X₁) (d : X₂ ⟶ Y₂) (v : Y₂ ⟶ Y₁)
  [IsOpenImmersion a] [IsOpenImmersion c] [IsOpenImmersion j] [IsOpenImmersion v]
  (h : IsPullback a b f j) (h' : IsPullback c d b v)
  (H : IsPullback (c ≫ a) d f (v ≫ j)) (M : X₀.Modules) (n : ℕ)

private def higherPastingPrefix :
    (restrictFunctor v).obj ((restrictFunctor j).obj (((pushforward f).rightDerived n).obj M)) ⟶
      (DerivedCategory.Plus.homologyFunctor Y₂.Modules (n : ℤ)).obj
        ((restrictFunctor v).rightDerivedFunctorPlus.obj
          ((restrictFunctor j).rightDerivedFunctorPlus.obj
            ((pushforward f).rightDerivedFunctorPlus.obj
              ((DerivedCategory.Plus.singleFunctor X₀.Modules 0).obj M)))) :=
  (restrictFunctor v).map
      ((restrictFunctor j).map (((pushforward f).rightDerivedSingleHomologyIso n).hom.app M)) ≫
    (restrictFunctor v).map
      (((restrictFunctor j).rightDerivedFunctorPlusHomologyIso (n : ℤ)).inv.app
        ((pushforward f).rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor X₀.Modules 0).obj M))) ≫
    ((restrictFunctor v).rightDerivedFunctorPlusHomologyIso (n : ℤ)).inv.app
      ((restrictFunctor j).rightDerivedFunctorPlus.obj
        ((pushforward f).rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor X₀.Modules 0).obj M)))

private def higherPastingSuffix :
    (DerivedCategory.Plus.homologyFunctor Y₂.Modules (n : ℤ)).obj
        ((pushforward d).rightDerivedFunctorPlus.obj
          ((restrictFunctor c).rightDerivedFunctorPlus.obj
            ((restrictFunctor a).rightDerivedFunctorPlus.obj
              ((DerivedCategory.Plus.singleFunctor X₀.Modules 0).obj M)))) ⟶
      ((pushforward d).rightDerived n).obj ((restrictFunctor c).obj ((restrictFunctor a).obj M)) :=
  (DerivedCategory.Plus.homologyFunctor Y₂.Modules (n : ℤ)).map
      ((pushforward d).rightDerivedFunctorPlus.map
        ((restrictFunctor c).rightDerivedFunctorPlus.map
          (((restrictFunctor a).rightDerivedFunctorPlusSingleIso 0).hom.app M))) ≫
    (DerivedCategory.Plus.homologyFunctor Y₂.Modules (n : ℤ)).map
      ((pushforward d).rightDerivedFunctorPlus.map
        (((restrictFunctor c).rightDerivedFunctorPlusSingleIso 0).hom.app
          ((restrictFunctor a).obj M))) ≫
    ((pushforward d).rightDerivedSingleHomologyIso n).inv.app
      ((restrictFunctor c).obj ((restrictFunctor a).obj M))

private theorem rightHigher_normalization :
    (restrictFunctor v).map ((higherDirectImageOpenRestrictionIso a b f j h n).hom.app M) ≫
        (higherDirectImageOpenRestrictionIso c d b v h' n).hom.app ((restrictFunctor a).obj M) =
      higherPastingPrefix f j v M n ≫
        (DerivedCategory.Plus.homologyFunctor Y₂.Modules (n : ℤ)).map
          ((derivedRight a b f j c d v h h').app
            ((DerivedCategory.Plus.singleFunctor X₀.Modules 0).obj M)) ≫
        higherPastingSuffix a c d M n := by
  let F := pushforward f
  let J := restrictFunctor j
  let V := restrictFunctor v
  let A := restrictFunctor a
  let B := pushforward b
  let C := restrictFunctor c
  let D := pushforward d
  let H₁ := DerivedCategory.Plus.homologyFunctor Y₁.Modules (n : ℤ)
  let H₂ := DerivedCategory.Plus.homologyFunctor Y₂.Modules (n : ℤ)
  let K := (DerivedCategory.Plus.singleFunctor X₀.Modules 0).obj M
  let eB := B.rightDerivedSingleHomologyIso n
  let eV := V.rightDerivedFunctorPlusHomologyIso (n : ℤ)
  let sA := (A.rightDerivedFunctorPlusSingleIso 0).hom.app M
  let sC := (C.rightDerivedFunctorPlusSingleIso 0).hom.app (A.obj M)
  let δ₁ := (derivedOpenBaseChangeIso a b f j h).hom.app K
  let δ₂ := (derivedOpenBaseChangeIso c d b v h').hom
  have hSA := eV.inv.naturality (B.rightDerivedFunctorPlus.map sA)
  change V.map (H₁.map (B.rightDerivedFunctorPlus.map sA)) ≫
      eV.inv.app (B.rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor X₁.Modules 0).obj (A.obj M))) =
    eV.inv.app (B.rightDerivedFunctorPlus.obj (A.rightDerivedFunctorPlus.obj K)) ≫
      H₂.map (V.rightDerivedFunctorPlus.map (B.rightDerivedFunctorPlus.map sA)) at hSA
  have hδ₁ := eV.inv.naturality δ₁
  change V.map (H₁.map δ₁) ≫
      eV.inv.app (B.rightDerivedFunctorPlus.obj (A.rightDerivedFunctorPlus.obj K)) =
    eV.inv.app (J.rightDerivedFunctorPlus.obj (F.rightDerivedFunctorPlus.obj K)) ≫
      H₂.map (V.rightDerivedFunctorPlus.map δ₁) at hδ₁
  have hδ₂ := δ₂.naturality sA
  change V.rightDerivedFunctorPlus.map (B.rightDerivedFunctorPlus.map sA) ≫
      δ₂.app ((DerivedCategory.Plus.singleFunctor X₁.Modules 0).obj (A.obj M)) =
    δ₂.app (A.rightDerivedFunctorPlus.obj K) ≫
      D.rightDerivedFunctorPlus.map (C.rightDerivedFunctorPlus.map sA) at hδ₂
  rw [higherOpen_app_model a b f j h M n,
    higherOpen_app_model c d b v h' (A.obj M) n]
  simp only [Functor.map_comp, Category.assoc]
  rw [← V.map_comp_assoc (eB.inv.app (A.obj M)) (eB.hom.app (A.obj M)),
    Iso.inv_hom_id_app]
  erw [V.map_id, Category.id_comp]
  rw [← Category.assoc (V.map (H₁.map (B.rightDerivedFunctorPlus.map sA)))
      (eV.inv.app (B.rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor X₁.Modules 0).obj (A.obj M)))), hSA]
  simp only [Category.assoc]
  rw [← Category.assoc (V.map (H₁.map δ₁))
      (eV.inv.app (B.rightDerivedFunctorPlus.obj (A.rightDerivedFunctorPlus.obj K))), hδ₁]
  simp only [Category.assoc]
  rw [← H₂.map_comp_assoc
      (V.rightDerivedFunctorPlus.map (B.rightDerivedFunctorPlus.map sA))
      (δ₂.app ((DerivedCategory.Plus.singleFunctor X₁.Modules 0).obj (A.obj M))),
    hδ₂, H₂.map_comp]
  dsimp only [higherPastingPrefix, higherPastingSuffix, derivedRight,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  simp only [Functor.map_comp, Category.assoc]
  rfl


private theorem leftHigher_normalization :
    (restrictFunctorComp v j).inv.app (((pushforward f).rightDerived n).obj M) ≫
        (higherDirectImageOpenRestrictionIso (c ≫ a) d f (v ≫ j) H n).hom.app M ≫
        ((pushforward d).rightDerived n).map ((restrictFunctorComp c a).hom.app M) =
      higherPastingPrefix f j v M n ≫
        (DerivedCategory.Plus.homologyFunctor Y₂.Modules (n : ℤ)).map
          ((derivedLeft a f j c d v H).app
            ((DerivedCategory.Plus.singleFunctor X₀.Modules 0).obj M)) ≫
        higherPastingSuffix a c d M n := by
  let F := pushforward f
  let J := restrictFunctor j
  let V := restrictFunctor v
  let JV := restrictFunctor (v ≫ j)
  let A := restrictFunctor a
  let C := restrictFunctor c
  let AC := restrictFunctor (c ≫ a)
  let D := pushforward d
  let H₀ := DerivedCategory.Plus.homologyFunctor Y₀.Modules (n : ℤ)
  let H₂ := DerivedCategory.Plus.homologyFunctor Y₂.Modules (n : ℤ)
  let K := (DerivedCategory.Plus.singleFunctor X₀.Modules 0).obj M
  let eF := F.rightDerivedSingleHomologyIso n
  let eD := D.rightDerivedSingleHomologyIso n
  let eJV := JV.rightDerivedFunctorPlusHomologyIso (n : ℤ)
  let sAC := (AC.rightDerivedFunctorPlusSingleIso 0).hom.app M
  let ξ := (restrictFunctorComp c a).hom.app M
  have hF := (restrictFunctorComp v j).inv.naturality (eF.hom.app M)
  change V.map (J.map (eF.hom.app M)) ≫
      (restrictFunctorComp v j).inv.app (H₀.obj (F.rightDerivedFunctorPlus.obj K)) =
    (restrictFunctorComp v j).inv.app ((F.rightDerived n).obj M) ≫
      JV.map (eF.hom.app M) at hF
  have hD := eD.inv.naturality ξ
  change H₂.map (D.rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.singleFunctor X₂.Modules 0).map ξ)) ≫
      eD.inv.app (C.obj (A.obj M)) =
    eD.inv.app (AC.obj M) ≫ (D.rightDerived n).map ξ at hD
  have hs := derivedRestrictionCompIso_single c a M
  rw [higherOpen_app_model (c ≫ a) d f (v ≫ j) H M n]
  simp only [Category.assoc]
  rw [← Category.assoc ((restrictFunctorComp v j).inv.app ((F.rightDerived n).obj M))
      (JV.map (eF.hom.app M)), ← hF]
  simp only [Category.assoc]
  rw [← Category.assoc
      ((restrictFunctorComp v j).inv.app (H₀.obj (F.rightDerivedFunctorPlus.obj K)))
      (eJV.inv.app (F.rightDerivedFunctorPlus.obj K)),
    derivedRestrictionCompIso_homology_inv v j (n : ℤ) (F.rightDerivedFunctorPlus.obj K)]
  simp only [Category.assoc]
  rw [← hD]
  rw [← H₂.map_comp_assoc (D.rightDerivedFunctorPlus.map sAC)
    (D.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor X₂.Modules 0).map ξ))]
  rw [← D.rightDerivedFunctorPlus.map_comp sAC
    ((DerivedCategory.Plus.singleFunctor X₂.Modules 0).map ξ), ← hs]
  dsimp only [higherPastingPrefix, higherPastingSuffix, derivedLeft,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  simp only [Functor.map_comp, Category.assoc]
  rfl

/-- The native higher-image open comparisons paste through the original restriction-composition
isomorphisms, for every module coefficient and natural degree. -/
@[reassoc]
theorem higherDirectImageOpenRestrictionIso_comp :
    (restrictFunctorComp v j).inv.app (((pushforward f).rightDerived n).obj M) ≫
        (higherDirectImageOpenRestrictionIso (c ≫ a) d f (v ≫ j) H n).hom.app M ≫
        ((pushforward d).rightDerived n).map ((restrictFunctorComp c a).hom.app M) =
      (restrictFunctor v).map ((higherDirectImageOpenRestrictionIso a b f j h n).hom.app M) ≫
        (higherDirectImageOpenRestrictionIso c d b v h' n).hom.app ((restrictFunctor a).obj M) := by
  rw [leftHigher_normalization, rightHigher_normalization,
    derivedOpen_pasting_natTrans a b f j c d v h h' H]


end HigherPasting



end AlgebraicGeometry.Scheme.Modules
