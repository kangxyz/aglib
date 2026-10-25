/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.Global.RelativeAffine

/-! # Original maps from actual relative affine algebra diagrams

An original map of structural ring diagrams gives the contravariant map of
native relative gluings. Its original chart equation and full structural
triangle are retained. The affine source comparison then gives the actual
map out of the original source scheme.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators.Global

universe u

open AffineZariskiSite

variable {X : Scheme.{u}}

section Diagrams

variable {F G : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u}}
  {a : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F}
  {b : (toOpensFunctor X).op ⋙ X.presheaf ⟶ G}
  (ha : a.Coequifibered) (hb : b.Coequifibered) (φ : G ⟶ F)

/-- The actual contravariant map of the native relative gluings. Only the
two displayed locally directed colimits are used. -/
def relativeAlgebraMap : (relativeGluingData ha).glued ⟶ (relativeGluingData hb).glued := by
  haveI : ((relativeGluingData ha).functor ⋙ Scheme.forget).IsLocallyDirected :=
    Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..
  haveI : ((relativeGluingData hb).functor ⋙ Scheme.forget).IsLocallyDirected :=
    Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..
  exact colimMap (Functor.whiskerRight φ.rightOp Scheme.Spec)

/-- Each original chart map is the Spec map of the supplied original ring map. -/
@[reassoc]
theorem relativeAlgebraMap_chart (U : X.AffineZariskiSite) :
    (relativeGluingData ha).cover.f U ≫ relativeAlgebraMap ha hb φ =
      Spec.map (φ.app (op U)) ≫ (relativeGluingData hb).cover.f U := by
  have : ((relativeGluingData ha).functor ⋙ Scheme.forget).IsLocallyDirected :=
    Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..
  have : ((relativeGluingData hb).functor ⋙ Scheme.forget).IsLocallyDirected :=
    Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..
  have : HasColimit (F.rightOp ⋙ Scheme.Spec) :=
    inferInstanceAs (HasColimit (relativeGluingData ha).functor)
  have : HasColimit (G.rightOp ⋙ Scheme.Spec) :=
    inferInstanceAs (HasColimit (relativeGluingData hb).functor)
  exact ι_colimMap (Functor.whiskerRight φ.rightOp Scheme.Spec) U

/-- The supplied original structural equation gives the exact chart triangle. -/
theorem relativeAlgebraMap_component_over (hφ : b ≫ φ = a) (U : X.AffineZariskiSite) :
    Spec.map (φ.app (op U)) ≫ (relativeGluingData hb).natTrans.app U =
      (relativeGluingData ha).natTrans.app U := by
  change Spec.map (φ.app (op U)) ≫ (Spec.map (b.app (op U)) ≫ U.2.isoSpec.inv) =
    Spec.map (a.app (op U)) ≫ U.2.isoSpec.inv
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun k => k ≫ U.2.isoSpec.inv)
      ((Spec.map_comp (b.app (op U)) (φ.app (op U))).symm.trans
        (congrArg Spec.map (congr_app hφ (op U)))))

/-- The actual relative map is over the original base by the original full
structural natural-transformation equation. -/
@[reassoc]
theorem relativeAlgebraMap_over (hφ : b ≫ φ = a) :
    relativeAlgebraMap ha hb φ ≫ (relativeGluingData hb).toBase =
      (relativeGluingData ha).toBase := by
  apply (relativeGluingData ha).cover.hom_ext
  intro U
  let c := (relativeGluingData ha).cover.f U
  let d := (relativeGluingData hb).cover.f U
  let m := relativeAlgebraMap ha hb φ
  let t := (relativeGluingData hb).toBase
  let q := Spec.map (φ.app (op U))
  let v := (directedCover X).f U
  have hmap : c ≫ m = q ≫ d := relativeAlgebraMap_chart ha hb φ U
  have ht : d ≫ t = (relativeGluingData hb).natTrans.app U ≫ v :=
    Cover.RelativeGluingData.ι_toBase (relativeGluingData hb) U
  have hbase := relativeAlgebraMap_component_over ha hb φ hφ U
  have hs : c ≫ (relativeGluingData ha).toBase =
      (relativeGluingData ha).natTrans.app U ≫ v :=
    Cover.RelativeGluingData.ι_toBase (relativeGluingData ha) U
  exact (Category.assoc c m t).symm.trans
    ((congrArg (fun k => k ≫ t) hmap).trans
      ((Category.assoc q d t).trans
        ((congrArg (fun k => q ≫ k) ht).trans
          ((Category.assoc q ((relativeGluingData hb).natTrans.app U) v).symm.trans
            ((congrArg (fun k => k ≫ v) hbase).trans hs.symm)))))

end Diagrams

section AffineSource

variable {Y : Scheme.{u}} (f : Y ⟶ X) [IsAffineHom f]
  {G : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u}}
  {b : (toOpensFunctor X).op ⋙ X.presheaf ⟶ G}
  (hb : b.Coequifibered)
  (φ : G ⟶ (toOpensFunctor X).op ⋙ relativeSectionDiagram f)

/-- The actual ring-diagram map gives a map out of the original affine source. -/
def relativeMapFromAffine : Y ⟶ (relativeGluingData hb).glued :=
  (relativeSourceIso f).inv ≫
    relativeAlgebraMap (relativeSectionMap_coequifibered f) hb φ

/-- The map from the original source retains its original structural morphism. -/
@[reassoc]
theorem relativeMapFromAffine_over
    (hφ : b ≫ φ = (toOpensFunctor X).op.whiskerLeft (relativeSectionMap f)) :
    relativeMapFromAffine f hb φ ≫ (relativeGluingData hb).toBase = f := by
  let e := relativeSourceIso f
  let m := relativeAlgebraMap (relativeSectionMap_coequifibered f) hb φ
  have hm : m ≫ (relativeGluingData hb).toBase = (relativeAffineData f).toBase :=
    relativeAlgebraMap_over (relativeSectionMap_coequifibered f) hb φ hφ
  exact (Category.assoc e.inv m (relativeGluingData hb).toBase).trans
    ((congrArg (fun k => e.inv ≫ k) hm).trans
      ((congrArg (fun k => e.inv ≫ k) (relativeSourceIso_hom_over f).symm).trans
        (by simp)))

end AffineSource
end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators.Global
