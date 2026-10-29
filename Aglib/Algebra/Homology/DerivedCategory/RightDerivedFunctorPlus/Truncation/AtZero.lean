/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov.Layers
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.TStructure
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.SingleHomology

/-! # The original degree-zero truncation of a right-derived single

For a left-exact additive functor, truncation below one of its native derived
single is the single of its original value. The homology equation retains the
original truncation inclusion and right-derived-zero comparison. Source and
target derived realizations are supplied independently.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open DerivedCategory.Plus

namespace CategoryTheory.Functor

universe uA vA dA uB vB dB

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{dA} A]
  [EnoughInjectives A] {B : Type uB} [Category.{vB} B] [Abelian B]
  [HasDerivedCategory.{dB} B] (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]

/-- The complete original truncation comparison, with no positive-homology
vanishing hypothesis and no reselected derived realization. -/
def rightDerivedFunctorPlusTruncLTOneIso (L : A) :
    (TStructure.t.truncLT 1).obj
        (F.rightDerivedFunctorPlus.obj ((singleFunctor A 0).obj L)) ≅
      (singleFunctor B 0).obj (F.obj L) := by
  let K := F.rightDerivedFunctorPlus.obj ((singleFunctor A 0).obj L)
  let : K.IsGE 0 := F.rightDerivedFunctorPlus_isGE _ 0
  let : ((TStructure.t.truncLT 1).obj K).IsLE 0 :=
    TStructure.t.isLE_truncLT_obj K 1 0 (by omega)
  exact isoSingleHomology ((TStructure.t.truncLT 1).obj K) 0 ≪≫
    (singleFunctor B 0).mapIso
      (homologyTruncLTIso K 1 0 (by omega) ≪≫
        (F.rightDerivedSingleHomologyZeroIso).app L)

/-- On original zero homology the comparison is the original truncation
inclusion, inverse native R0/homology comparison and right-derived-zero map. -/
@[reassoc]
theorem rightDerivedFunctorPlusTruncLTOneIso_homology_zero (L : A) :
    (homologyFunctor B 0).map (F.rightDerivedFunctorPlusTruncLTOneIso L).hom ≫
        (singleFunctorCompHomologyFunctorIso (C := B) 0).hom.app (F.obj L) =
      (homologyFunctor B 0).map ((TStructure.t.truncLTι 1).app
        (F.rightDerivedFunctorPlus.obj ((singleFunctor A 0).obj L))) ≫
          (F.rightDerivedSingleHomologyIso 0).inv.app L ≫ F.rightDerivedZeroIsoSelf.hom.app L := by
  let K := F.rightDerivedFunctorPlus.obj ((singleFunctor A 0).obj L)
  let : K.IsGE 0 := F.rightDerivedFunctorPlus_isGE _ 0
  let : ((TStructure.t.truncLT 1).obj K).IsLE 0 :=
    TStructure.t.isLE_truncLT_obj K 1 0 (by omega)
  let M := (TStructure.t.truncLT 1).obj K
  let e := isoSingleHomology M 0
  let q := homologyTruncLTIso K 1 0 (by omega) ≪≫
    (F.rightDerivedSingleHomologyZeroIso).app L
  let H := homologyFunctor B 0
  let S := singleFunctor B 0
  let E := singleFunctorCompHomologyFunctorIso (C := B) 0
  have he : H.map e.hom ≫ E.hom.app (H.obj M) = 𝟙 _ := by
    change (DerivedCategory.homologyFunctor B 0).map
        ((DerivedCategory.Plus.ι : DerivedCategory.Plus B ⥤ DerivedCategory B).map
          (isoSingleHomology M 0).hom) ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso B 0).hom.app
          ((DerivedCategory.homologyFunctor B 0).obj
            (DerivedCategory.Plus.ι.obj M)) = 𝟙 _
    rw [ι_map_isoSingleHomology_hom]
    exact DerivedCategory.isoSingleHomology_homology (DerivedCategory.Plus.ι.obj M) 0
  have hn := E.hom.naturality q.hom
  change H.map (S.map q.hom) ≫ E.hom.app (F.obj L) =
    E.hom.app (H.obj M) ≫ q.hom at hn
  have h : H.map (F.rightDerivedFunctorPlusTruncLTOneIso L).hom ≫
      E.hom.app (F.obj L) = q.hom := by
    change H.map (e.hom ≫ S.map q.hom) ≫ E.hom.app (F.obj L) = q.hom
    rw [Functor.map_comp, Category.assoc, hn, ← Category.assoc, he, Category.id_comp]
  simpa only [H, E, q, K, homologyTruncLTIso_hom,
    Functor.rightDerivedSingleHomologyZeroIso, Iso.app_hom, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc] using h

end CategoryTheory.Functor
