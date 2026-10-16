/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Flat
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Restriction
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Composition
public import Aglib.AlgebraicGeometry.Modules.BaseChange.OpenImmersion.Pullback

/-!
# The original derived flat comparison under open restriction

The native flat pullback composition comparison retains its original units.
For an open change of base, the existing derived base-change map is an
isomorphism on all bounded-below module complexes: the original ordinary
mate is invertible and both composite functors compute their native right
derived functors. No quasicoherence of resolution terms is used. Successive flat changes of
base satisfy the original pasting equation, proved by their installed
units and the original ordinary mate composition identity.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

local instance baseChangeRestrictionStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

/-- Composition of the installed exact flat pullbacks, through the original
geometric pullback-composition isomorphism. -/
def derivedFlatPullbackPlusCompIso {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Flat f] [Flat g] :
    derivedFlatPullbackPlus g ⋙ derivedFlatPullbackPlus f ≅
      derivedFlatPullbackPlus (f ≫ g) :=
  ((pullback g).rightDerivedFunctorPlusCompIsoOfPreservesHomology (pullback f)).symm ≪≫
    (pullback g ⋙ pullback f).rightDerivedFunctorPlusIso (pullbackComp f g)

/-- Flat pullback composition preserves both installed units and the original
geometric composition map. -/
@[reassoc]
theorem derivedFlatPullbackPlusCompIso_unit {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Flat f] [Flat g]
    (K : CochainComplex.Plus Z.Modules) :
    (Functor.rightDerivedFunctorPlusCompUnit (pullback g) (pullback f)).app K ≫
        (derivedFlatPullbackPlusCompIso f g).hom.app (DerivedCategory.Plus.Q.obj K) =
      DerivedCategory.Plus.Q.map
          ((NatIso.mapCochainComplexPlus (pullbackComp f g)).hom.app K) ≫
        (pullback (f ≫ g)).rightDerivedFunctorPlusUnit.app K := by
  let e := (pullback g).rightDerivedFunctorPlusCompIsoOfPreservesHomology (pullback f)
  have he : (pullback g ⋙ pullback f).rightDerivedFunctorPlusUnit.app K ≫
      e.hom.app (DerivedCategory.Plus.Q.obj K) =
      (Functor.rightDerivedFunctorPlusCompUnit (pullback g) (pullback f)).app K := by
    rw [Functor.rightDerivedFunctorPlusCompUnit_app]
    exact (pullback g).rightDerivedFunctorPlusCompIsoOfPreservesHomology_hom_app
      (pullback f) K
  change (Functor.rightDerivedFunctorPlusCompUnit (pullback g) (pullback f)).app K ≫
    e.inv.app (DerivedCategory.Plus.Q.obj K) ≫ _ = _
  rw [← he]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  exact (pullback g ⋙ pullback f).rightDerivedFunctorPlusIso_hom_app (pullbackComp f g) K

/-- Open base change makes the original derived flat comparison invertible on
every bounded-below complex of arbitrary module sheaves. -/
theorem isIso_derivedFlatBaseChangeMap_of_isOpenImmersion
    {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
    [IsOpenImmersion a] [IsOpenImmersion j] (h : IsPullback a b f j) :
    IsIso (derivedFlatBaseChangeMap a b f j h) := by
  let := flat_cartesian_baseChange a b f j h
  let F := pushforward f
  let J := pullback j
  let A := pullback a
  let B := pushforward b
  let : A.PreservesInjectiveObjects := {
    injective_obj := fun {M} hM => by
      let := hM
      exact Injective.of_iso ((restrictFunctorIsoPullback a).app M) inferInstance }
  let := F.isRightDerivedFunctor_comp_of_preservesHomology J
  let := A.isRightDerivedFunctor_comp_of_preservesInjectiveObjects B
  let : IsIso (cartesianBaseChangeMap a b f j h) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact isIso_cartesianBaseChangeMap_of_isOpenImmersion a b f j h
  let e := Functor.isoWhiskerRight
    (NatIso.mapCochainComplexPlus (asIso (cartesianBaseChangeMap a b f j h)))
      DerivedCategory.Plus.Q
  change IsIso (Functor.rightDerivedNatIso
    (F.rightDerivedFunctorPlus ⋙ J.rightDerivedFunctorPlus)
    (A.rightDerivedFunctorPlus ⋙ B.rightDerivedFunctorPlus)
    (Functor.rightDerivedFunctorPlusCompUnit F J)
    (Functor.rightDerivedFunctorPlusCompUnit A B)
    (CochainComplex.Plus.quasiIso U.Modules) e).hom
  infer_instance

variable {W U V X W' V' : Scheme.{u}}
  (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  (h : IsPullback a b f j) (c : W' ⟶ W) (d : W' ⟶ V') (v : V' ⟶ V)
  (h' : IsPullback c d b v) (H : IsPullback (c ≫ a) d f (v ≫ j))
  [Flat j] [Flat v]

private theorem derivedFlatBaseChangeMap_comp_left_unit (K : CochainComplex.Plus U.Modules) :
    (pullback v).rightDerivedFunctorPlusUnit.app
        ((pushforward f ⋙ pullback j).mapCochainComplexPlus.obj K) ≫
      (derivedFlatPullbackPlus v).map
        ((Functor.rightDerivedFunctorPlusCompUnit (pushforward f) (pullback j)).app K) ≫
      (derivedFlatPullbackPlusCompIso v j).hom.app
        ((derivedPushforwardPlus f).obj (DerivedCategory.Plus.Q.obj K)) ≫
      (derivedFlatBaseChangeMap (c ≫ a) d f (v ≫ j) H).app (DerivedCategory.Plus.Q.obj K) =
    DerivedCategory.Plus.Q.map
        ((NatIso.mapCochainComplexPlus (pullbackComp v j)).hom.app
          ((pushforward f).mapCochainComplexPlus.obj K)) ≫
      DerivedCategory.Plus.Q.map
        ((NatTrans.mapCochainComplexPlus
          (cartesianBaseChangeMap (c ≫ a) d f (v ≫ j) H)).app K) ≫
      (Functor.rightDerivedFunctorPlusCompUnit (pullback (c ≫ a)) (pushforward d)).app K := by
  let F := pushforward f
  let J := pullback j
  let V := pullback v
  let e := derivedFlatPullbackPlusCompIso v j
  have hn := e.hom.naturality (F.rightDerivedFunctorPlusUnit.app K)
  have he := derivedFlatPullbackPlusCompIso_unit v j (F.mapCochainComplexPlus.obj K)
  rw [Functor.rightDerivedFunctorPlusCompUnit_app] at he
  simp only [Functor.comp_obj, Functor.comp_map, Category.assoc] at hn he
  have hH := derivedFlatBaseChangeMap_unit (c ≫ a) d f (v ≫ j) H K
  rw [Functor.rightDerivedFunctorPlusCompUnit_app] at hH
  simp only [Category.assoc] at hH
  change V.rightDerivedFunctorPlusUnit.app ((F ⋙ J).mapCochainComplexPlus.obj K) ≫
      V.rightDerivedFunctorPlus.map
        ((Functor.rightDerivedFunctorPlusCompUnit F J).app K) ≫
      e.hom.app (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)) ≫ _ = _
  rw [Functor.rightDerivedFunctorPlusCompUnit_app, Functor.map_comp]
  simp only [Category.assoc]
  erw [reassoc_of% hn]
  erw [reassoc_of% he]
  erw [hH]

private theorem derivedFlatBaseChangeMap_comp_right_unit [Flat a] [Flat c]
    (K : CochainComplex.Plus U.Modules) :
    (pullback v).rightDerivedFunctorPlusUnit.app
        ((pushforward f ⋙ pullback j).mapCochainComplexPlus.obj K) ≫
      (derivedFlatPullbackPlus v).map
        ((Functor.rightDerivedFunctorPlusCompUnit (pushforward f) (pullback j)).app K) ≫
      (derivedFlatPullbackPlus v).map
        ((derivedFlatBaseChangeMap a b f j h).app (DerivedCategory.Plus.Q.obj K)) ≫
      (derivedFlatBaseChangeMap c d b v h').app
        ((derivedFlatPullbackPlus a).obj (DerivedCategory.Plus.Q.obj K)) ≫
      (derivedPushforwardPlus d).map
        ((derivedFlatPullbackPlusCompIso c a).hom.app (DerivedCategory.Plus.Q.obj K)) =
    DerivedCategory.Plus.Q.map
        ((pullback v).mapCochainComplexPlus.map
          ((NatTrans.mapCochainComplexPlus (cartesianBaseChangeMap a b f j h)).app K)) ≫
      DerivedCategory.Plus.Q.map
        ((NatTrans.mapCochainComplexPlus (cartesianBaseChangeMap c d b v h')).app
          ((pullback a).mapCochainComplexPlus.obj K)) ≫
      DerivedCategory.Plus.Q.map
        ((pushforward d).mapCochainComplexPlus.map
          ((NatIso.mapCochainComplexPlus (pullbackComp c a)).hom.app K)) ≫
      (Functor.rightDerivedFunctorPlusCompUnit (pullback (c ≫ a)) (pushforward d)).app K := by
  let F := pushforward f
  let J := pullback j
  let A := pullback a
  let B := pushforward b
  let V := pullback v
  let C := pullback c
  let D := pushforward d
  let α := (NatTrans.mapCochainComplexPlus (cartesianBaseChangeMap a b f j h)).app K
  let ε := (NatIso.mapCochainComplexPlus (pullbackComp c a)).hom.app K
  have h1 := derivedFlatBaseChangeMap_unit a b f j h K
  have h2 := derivedFlatBaseChangeMap_unit c d b v h' (A.mapCochainComplexPlus.obj K)
  have hnα := V.rightDerivedFunctorPlusUnit.naturality α
  have hnA := (derivedFlatBaseChangeMap c d b v h').naturality
    (A.rightDerivedFunctorPlusUnit.app K)
  have he := derivedFlatPullbackPlusCompIso_unit c a K
  rw [Functor.rightDerivedFunctorPlusCompUnit_app] at he h2
  have hnε := D.rightDerivedFunctorPlusUnit.naturality ε
  simp only [Functor.comp_obj, Functor.comp_map, Category.assoc] at hnα hnA he h2 hnε
  change V.rightDerivedFunctorPlusUnit.app ((F ⋙ J).mapCochainComplexPlus.obj K) ≫
      V.rightDerivedFunctorPlus.map
        ((Functor.rightDerivedFunctorPlusCompUnit F J).app K) ≫
      V.rightDerivedFunctorPlus.map
        ((derivedFlatBaseChangeMap a b f j h).app (DerivedCategory.Plus.Q.obj K)) ≫
      (derivedFlatBaseChangeMap c d b v h').app
        (A.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)) ≫
      D.rightDerivedFunctorPlus.map
        ((derivedFlatPullbackPlusCompIso c a).hom.app (DerivedCategory.Plus.Q.obj K)) = _
  rw [← Functor.map_comp_assoc]
  erw [h1]
  rw [Functor.map_comp]
  simp only [Category.assoc]
  erw [← reassoc_of% hnα]
  rw [Functor.rightDerivedFunctorPlusCompUnit_app, Functor.map_comp]
  simp only [Category.assoc]
  erw [reassoc_of% hnA]
  erw [reassoc_of% h2]
  erw [Functor.rightDerivedFunctorPlusCompUnit_app]
  simp only [Category.assoc]
  erw [← D.rightDerivedFunctorPlus.map_comp_assoc, ← D.rightDerivedFunctorPlus.map_comp]
  simp only [Category.assoc]
  erw [he]
  rw [Functor.map_comp]
  erw [← reassoc_of% hnε]
  rw [Functor.rightDerivedFunctorPlusCompUnit_app]

private theorem derivedFlatBaseChangeMap_comp_unit [Flat a] [Flat c]
    (K : CochainComplex.Plus U.Modules) :
    (pullback v).rightDerivedFunctorPlusUnit.app
        ((pushforward f ⋙ pullback j).mapCochainComplexPlus.obj K) ≫
      (derivedFlatPullbackPlus v).map
        ((Functor.rightDerivedFunctorPlusCompUnit (pushforward f) (pullback j)).app K) ≫
      (derivedFlatPullbackPlusCompIso v j).hom.app
        ((derivedPushforwardPlus f).obj (DerivedCategory.Plus.Q.obj K)) ≫
      (derivedFlatBaseChangeMap (c ≫ a) d f (v ≫ j) H).app (DerivedCategory.Plus.Q.obj K) =
    (pullback v).rightDerivedFunctorPlusUnit.app
        ((pushforward f ⋙ pullback j).mapCochainComplexPlus.obj K) ≫
      (derivedFlatPullbackPlus v).map
        ((Functor.rightDerivedFunctorPlusCompUnit (pushforward f) (pullback j)).app K) ≫
      (derivedFlatPullbackPlus v).map
        ((derivedFlatBaseChangeMap a b f j h).app (DerivedCategory.Plus.Q.obj K)) ≫
      (derivedFlatBaseChangeMap c d b v h').app
        ((derivedFlatPullbackPlus a).obj (DerivedCategory.Plus.Q.obj K)) ≫
      (derivedPushforwardPlus d).map
        ((derivedFlatPullbackPlusCompIso c a).hom.app (DerivedCategory.Plus.Q.obj K)) := by
  rw [derivedFlatBaseChangeMap_comp_left_unit
      (a := a) (f := f) (j := j) (c := c) (d := d) (v := v) H K,
    derivedFlatBaseChangeMap_comp_right_unit a b f j h c d v h' K]
  have hc :
      (NatIso.mapCochainComplexPlus (pullbackComp v j)).hom.app
          ((pushforward f).mapCochainComplexPlus.obj K) ≫
        (NatTrans.mapCochainComplexPlus
          (cartesianBaseChangeMap (c ≫ a) d f (v ≫ j) H)).app K =
      (pullback v).mapCochainComplexPlus.map
          ((NatTrans.mapCochainComplexPlus (cartesianBaseChangeMap a b f j h)).app K) ≫
        (NatTrans.mapCochainComplexPlus (cartesianBaseChangeMap c d b v h')).app
          ((pullback a).mapCochainComplexPlus.obj K) ≫
        (pushforward d).mapCochainComplexPlus.map
          ((NatIso.mapCochainComplexPlus (pullbackComp c a)).hom.app K) := by
    apply ObjectProperty.hom_ext
    apply HomologicalComplex.hom_ext
    intro i
    exact cartesianBaseChangeMap_comp a b f j h c d v h' H (K.obj.X i)
  simpa only [Functor.map_comp, Category.assoc] using congrArg
    (fun q => DerivedCategory.Plus.Q.map q ≫
      (Functor.rightDerivedFunctorPlusCompUnit (pullback (c ≫ a))
        (pushforward d)).app K) hc

/-- Successive flat changes of base give the original derived comparison for their composite,
through the native exact pullback-composition comparisons on both sides. -/
theorem derivedFlatBaseChangeMap_comp :
    letI := flat_cartesian_baseChange a b f j h
    letI := flat_cartesian_baseChange c d b v h'
    ∀ K : DerivedCategory.Plus U.Modules,
      (derivedFlatPullbackPlusCompIso v j).hom.app ((derivedPushforwardPlus f).obj K) ≫
          (derivedFlatBaseChangeMap (c ≫ a) d f (v ≫ j) H).app K =
        (derivedFlatPullbackPlus v).map ((derivedFlatBaseChangeMap a b f j h).app K) ≫
          (derivedFlatBaseChangeMap c d b v h').app ((derivedFlatPullbackPlus a).obj K) ≫
          (derivedPushforwardPlus d).map ((derivedFlatPullbackPlusCompIso c a).hom.app K) := by
  let := flat_cartesian_baseChange a b f j h
  let := flat_cartesian_baseChange c d b v h'
  let F := pushforward f
  let J := pullback j
  let A := pullback a
  let B := pushforward b
  let V := pullback v
  let C := pullback c
  let D := pushforward d
  let JV := pullback (v ≫ j)
  let AC := pullback (c ≫ a)
  let eJ : J.rightDerivedFunctorPlus ⋙ V.rightDerivedFunctorPlus ≅
      JV.rightDerivedFunctorPlus := derivedFlatPullbackPlusCompIso v j
  let eA : A.rightDerivedFunctorPlus ⋙ C.rightDerivedFunctorPlus ≅
      AC.rightDerivedFunctorPlus := derivedFlatPullbackPlusCompIso c a
  let δ : F.rightDerivedFunctorPlus ⋙ J.rightDerivedFunctorPlus ⟶
      A.rightDerivedFunctorPlus ⋙ B.rightDerivedFunctorPlus :=
    derivedFlatBaseChangeMap a b f j h
  let δ' : B.rightDerivedFunctorPlus ⋙ V.rightDerivedFunctorPlus ⟶
      C.rightDerivedFunctorPlus ⋙ D.rightDerivedFunctorPlus :=
    derivedFlatBaseChangeMap c d b v h'
  let δH : F.rightDerivedFunctorPlus ⋙ JV.rightDerivedFunctorPlus ⟶
      AC.rightDerivedFunctorPlus ⋙ D.rightDerivedFunctorPlus :=
    derivedFlatBaseChangeMap (c ≫ a) d f (v ≫ j) H
  let τL := Functor.whiskerLeft F.rightDerivedFunctorPlus eJ.hom ≫ δH
  let τR := (Functor.associator F.rightDerivedFunctorPlus J.rightDerivedFunctorPlus
      V.rightDerivedFunctorPlus).inv ≫
    Functor.whiskerRight δ V.rightDerivedFunctorPlus ≫
    (Functor.associator A.rightDerivedFunctorPlus B.rightDerivedFunctorPlus
      V.rightDerivedFunctorPlus).hom ≫
    Functor.whiskerLeft A.rightDerivedFunctorPlus δ' ≫
    (Functor.associator A.rightDerivedFunctorPlus C.rightDerivedFunctorPlus
      D.rightDerivedFunctorPlus).inv ≫
    Functor.whiskerRight eA.hom D.rightDerivedFunctorPlus
  have ht : τL = τR := by
    let eFJ := F.rightDerivedFunctorPlusCompIsoOfPreservesHomology J
    let e := Functor.isoWhiskerRight eFJ V.rightDerivedFunctorPlus ≪≫
      Functor.associator F.rightDerivedFunctorPlus J.rightDerivedFunctorPlus
        V.rightDerivedFunctorPlus
    apply (cancel_epi e.hom).mp
    let := (F ⋙ J).isRightDerivedFunctor_comp_of_preservesHomology V
    apply Functor.rightDerived_ext _
      (Functor.rightDerivedFunctorPlusCompUnit (F ⋙ J) V)
      (CochainComplex.Plus.quasiIso U.Modules)
    ext K : 2
    have hFJ : (F ⋙ J).rightDerivedFunctorPlusUnit.app K ≫
        eFJ.hom.app (DerivedCategory.Plus.Q.obj K) =
        (Functor.rightDerivedFunctorPlusCompUnit F J).app K := by
      rw [Functor.rightDerivedFunctorPlusCompUnit_app]
      exact F.rightDerivedFunctorPlusCompIsoOfPreservesHomology_hom_app J K
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.rightDerivedFunctorPlusCompUnit_app, e, Iso.trans_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
      Functor.associator_hom_app, Category.assoc]
    erw [← V.rightDerivedFunctorPlus.map_comp_assoc, hFJ,
      ← V.rightDerivedFunctorPlus.map_comp_assoc, hFJ]
    dsimp only [τL, τR, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Functor.comp_obj]
    simp only [Category.id_comp]
    exact derivedFlatBaseChangeMap_comp_unit a b f j h c d v h' H K
  intro K
  simpa only [derivedFlatPullbackPlus, derivedPushforwardPlus, flatExactPullback,
    τL, τR, eJ, eA, δ, δ', δH, F, J, A, B, V, C, D, JV, AC, NatTrans.comp_app,
    Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.comp_obj, Category.id_comp, Category.comp_id, Category.assoc] using congr_app ht K

end AlgebraicGeometry.Scheme.Modules
