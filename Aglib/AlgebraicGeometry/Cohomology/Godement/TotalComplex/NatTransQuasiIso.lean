/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Godement.TotalComplex.Naturality

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/WeakFunctorTransport.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general;
source ranges [[1, 66]]. Actual objects, maps and hypotheses are preserved.
-/

/-! # Typed weak-map transport before concrete functor specialization -/
@[expose] public section
noncomputable section
universe u v w x y
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules.Godement

/-- The exact associator and actual total/image whiskering, with typed endpoints. -/
@[irreducible] def plusReassociatedTotalImageMap
    {D : Type v} [Category.{w} D] {X Y : Scheme.{u}} (p : X ⟶ Y)
    {M : Type x} [Category.{y} M] (A : D ⥤ M)
    (B : M ⥤ CochainComplex.Plus X.Modules)
    (C : D ⥤ CochainComplex.Plus X.Modules)
    (E : CochainComplex.Plus X.Modules ⥤ CochainComplex.Plus X.Modules)
    (a : A ⋙ B ⟶ C ⋙ E) :
    A ⋙ B ⋙ godementTotalPlus X ⋙
        (Scheme.Modules.pushforward p).mapCochainComplexPlus ⟶
      C ⋙ E ⋙ godementTotalPlus X ⋙
        (Scheme.Modules.pushforward p).mapCochainComplexPlus :=
  (Functor.associator A B
    (godementTotalPlus X ⋙ (Scheme.Modules.pushforward p).mapCochainComplexPlus)).inv ≫
    Functor.whiskerRight a
      (godementTotalPlus X ⋙ (Scheme.Modules.pushforward p).mapCochainComplexPlus) ≫
    (Functor.associator C E
      (godementTotalPlus X ⋙ (Scheme.Modules.pushforward p).mapCochainComplexPlus)).hom

lemma plusReassociatedTotalImageMap_quasiIso
    {D : Type v} [Category.{w} D] {X Y : Scheme.{u}} (p : X ⟶ Y)
    {M : Type x} [Category.{y} M] (A : D ⥤ M)
    (B : M ⥤ CochainComplex.Plus X.Modules)
    (C : D ⥤ CochainComplex.Plus X.Modules)
    (E : CochainComplex.Plus X.Modules ⥤ CochainComplex.Plus X.Modules)
    (a : A ⋙ B ⟶ C ⋙ E) (ha : ∀ K, QuasiIso (a.app K).hom) (K : D) :
    QuasiIso ((plusReassociatedTotalImageMap p A B C E a).app K).hom := by
  let F := godementTotalPlus X ⋙ (Scheme.Modules.pushforward p).mapCochainComplexPlus
  let e₁ := Functor.associator A B F
  let e₂ := Functor.associator C E F
  let aF := Functor.whiskerRight a F
  unfold plusReassociatedTotalImageMap
  exact Plus.plus_nattrans_comp_quasiIso e₁.inv (aF ≫ e₂.hom)
    (Plus.plus_natIso_hom_quasiIso e₁.symm)
    (Plus.plus_nattrans_comp_quasiIso aF e₂.hom
      (plus_whiskerTotalImage_quasiIso p a ha) (Plus.plus_natIso_hom_quasiIso e₂)) K

lemma complex_map_quasiIso_of_natIso
    {D : Type v} [Category.{w} D] {X : Scheme.{u}}
    {F G : D ⥤ CochainComplex X.Modules ℤ} (e : F ≅ G)
    {K L : D} (a : K ⟶ L) (ha : QuasiIso (G.map a)) : QuasiIso (F.map a) := by
  let := ha
  let : QuasiIso (e.hom.app K) := inferInstance
  let : QuasiIso (e.hom.app L) := inferInstance
  have : QuasiIso (F.map a ≫ e.hom.app L) := by
    rw [e.hom.naturality a]
    infer_instance
  exact quasiIso_of_comp_right (F.map a) (e.hom.app L)

end AlgebraicGeometry.Scheme.Modules.Godement

namespace AlgebraicGeometry.Scheme.Modules.Godement

lemma plus_tensor_totalImage_functor_map_quasiIso
    {D : Type v} [Category.{w} D] {X Y : Scheme.{u}} (p : X ⟶ Y)
    (F : D ⥤ CochainComplex.Plus X.Modules) (T : X.Modules ⥤ X.Modules)
    [T.Additive] [T.PreservesHomology] {K L : D} (a : K ⟶ L) (ha : QuasiIso (F.map a).hom) :
    QuasiIso ((((F ⋙ CochainComplex.Plus.ι X.Modules) ⋙
      T.mapHomologicalComplex (.up ℤ) ⋙ godementTotal X ⋙
      (Scheme.Modules.pushforward p).mapHomologicalComplex (.up ℤ)).map a)) := by
  let := ha
  let t := T.mapCochainComplexPlus.map (F.map a)
  let : QuasiIso t.hom := by
    change QuasiIso ((T.mapHomologicalComplex (.up ℤ)).map (F.map a).hom)
    infer_instance
  exact totalPushforwardPlus_quasiIso p t

/-- The ordinary complex direct image after additive termwise mapping and Godement totalization
of a bounded-below family. -/
@[irreducible] def plusTensorTotalImageFunctor
    {D : Type v} [Category.{w} D] {X Y : Scheme.{u}} (p : X ⟶ Y)
    (F : D ⥤ CochainComplex.Plus X.Modules) (T : X.Modules ⥤ X.Modules) [T.Additive] :
    D ⥤ CochainComplex Y.Modules ℤ :=
  (F ⋙ CochainComplex.Plus.ι X.Modules) ⋙ T.mapHomologicalComplex (.up ℤ) ⋙
    godementTotal X ⋙ (Scheme.Modules.pushforward p).mapHomologicalComplex (.up ℤ)

/-- Definitional equality at functor level avoids concrete component evaluation. -/
lemma plusTensorTotalImageFunctor_eq
    {D : Type v} [Category.{w} D] {X Y : Scheme.{u}} (p : X ⟶ Y)
    (F : D ⥤ CochainComplex.Plus X.Modules) (T : X.Modules ⥤ X.Modules) [T.Additive] :
    plusTensorTotalImageFunctor p F T =
      (F ⋙ CochainComplex.Plus.ι X.Modules) ⋙ T.mapHomologicalComplex (.up ℤ) ⋙
        godementTotal X ⋙ (Scheme.Modules.pushforward p).mapHomologicalComplex (.up ℤ) := by
  unfold plusTensorTotalImageFunctor
  rfl

lemma plusTensorTotalImageFunctor_map_quasiIso
    {D : Type v} [Category.{w} D] {X Y : Scheme.{u}} (p : X ⟶ Y)
    (F : D ⥤ CochainComplex.Plus X.Modules) (T : X.Modules ⥤ X.Modules)
    [T.Additive] [T.PreservesHomology] {K L : D} (a : K ⟶ L)
    (ha : QuasiIso (F.map a).hom) :
    QuasiIso ((plusTensorTotalImageFunctor p F T).map a) := by
  rw [plusTensorTotalImageFunctor_eq]
  exact plus_tensor_totalImage_functor_map_quasiIso (D := D) (X := X) (Y := Y)
    p F T (K := K) (L := L) a ha

end AlgebraicGeometry.Scheme.Modules.Godement
