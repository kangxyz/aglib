/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.FiniteEtaleTransfer
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.SplitProjection
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-! # Gluing actual finite-etale generator sums

Restriction of a chosen splitting uses the canonical pullback-pasting
isomorphism. All sums are sections of the original free representable.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.Sheaf.Hypercohomology

namespace AlgebraicGeometry.Scheme.FiniteEtale

universe u

attribute [local instance] Fintype.ofFinite

variable {X : Scheme.{u}} (Y : Scheme.FiniteEtale X)

/-- The native pullback-pasting isomorphism on finite covers, with the actual
site-arrow structure equality at its target. -/
def chartPullbackIso {W V : X.Etale} (f : W ⟶ V) :
    (baseChange f.left).obj ((baseChange V.hom).obj Y) ≅ (baseChange W.hom).obj Y :=
  ObjectProperty.isoMk _ (Over.isoMk
    (pullbackLeftPullbackSndIso Y.obj.hom V.hom f.left ≪≫
      pullback.congrHom rfl (MorphismProperty.Over.w f)) (by
        change ((pullbackLeftPullbackSndIso Y.obj.hom V.hom f.left).hom ≫
          (pullback.congrHom rfl (MorphismProperty.Over.w f)).hom) ≫
          pullback.snd Y.obj.hom W.hom = pullback.snd _ _
        simp only [Category.assoc, pullback.congrHom_hom,
          pullback.map, pullback.lift_snd, Category.comp_id, pullbackLeftPullbackSndIso_hom_snd]))

@[reassoc] theorem chartPullbackIso_fst {W V : X.Etale} (f : W ⟶ V) :
    (chartPullbackIso Y f).hom.hom.left ≫ pullback.fst Y.obj.hom W.hom =
      pullback.fst (pullback.snd Y.obj.hom V.hom) f.left ≫
        pullback.fst Y.obj.hom V.hom := by
  change ((pullbackLeftPullbackSndIso Y.obj.hom V.hom f.left).hom ≫
    (pullback.congrHom rfl (MorphismProperty.Over.w f)).hom) ≫
      pullback.fst Y.obj.hom W.hom = _
  simp only [Category.assoc, pullback.congrHom_hom, pullback.map, pullback.lift_fst,
    Category.comp_id, pullbackLeftPullbackSndIso_hom_fst]

/-- Pull back an actual splitting along a site morphism. -/
def restrictChartSplitting {W V : X.Etale} (f : W ⟶ V) {A : FintypeCat.{u}}
    (e : (trivialCoverFunctor V.left).obj A ≅ (baseChange V.hom).obj Y) :
    (trivialCoverFunctor W.left).obj A ≅ (baseChange W.hom).obj Y :=
  trivialCoverBaseChangeIso f.left A ≪≫ (baseChange f.left).mapIso e ≪≫
    chartPullbackIso Y f

/-- The original site section of the finite cover on a split chart. -/
def chartSiteSection {V : X.Etale} {A : FintypeCat.{u}}
    (e : (trivialCoverFunctor V.left).obj A ≅ (baseChange V.hom).obj Y) (a : A) :
    V ⟶ (toEtale X).obj Y :=
  trivializationSiteSection ((baseChange V.hom).obj Y)
    (pullback.fst Y.obj.hom V.hom) pullback.condition e a

@[reassoc] theorem chartSiteSection_restrict {W V : X.Etale} (f : W ⟶ V)
    {A : FintypeCat.{u}}
    (e : (trivialCoverFunctor V.left).obj A ≅ (baseChange V.hom).obj Y) (a : A) :
    chartSiteSection Y (restrictChartSplitting Y f e) a = f ≫ chartSiteSection Y e a := by
  apply MorphismProperty.Over.Hom.ext
  change (trivialCoverι W.left A a).hom.left ≫
      (restrictChartSplitting Y f e).hom.hom.left ≫ pullback.fst Y.obj.hom W.hom =
    f.left ≫ (trivialCoverι V.left A a).hom.left ≫ e.hom.hom.left ≫
      pullback.fst Y.obj.hom V.hom
  simp only [restrictChartSplitting, Iso.trans_hom, ObjectProperty.FullSubcategory.comp_hom,
    Over.comp_left, Category.assoc, chartPullbackIso_fst]
  change (trivialCoverι W.left A a).hom.left ≫
      (trivialCoverBaseChangeMap f.left A).hom.left ≫
      pullback.lift (pullback.fst _ _ ≫ e.hom.hom.left) (pullback.snd _ _) _ ≫
      pullback.fst _ _ ≫ pullback.fst _ _ = _
  rw [pullback.lift_fst_assoc]
  rw [← Category.assoc (trivialCoverι W.left A a).hom.left]
  have h := congrArg (fun k => k.hom.left) (trivialCoverι_baseChangeMap f.left A a)
  change (trivialCoverι W.left A a).hom.left ≫
    (trivialCoverBaseChangeMap f.left A).hom.left =
      (trivialCoverBaseChangeSection f.left A a).hom.left at h
  rw [h]
  change pullback.lift (f.left ≫ (trivialCoverι V.left A a).hom.left) (𝟙 _) _ ≫
    pullback.fst _ _ ≫ e.hom.hom.left ≫ pullback.fst _ _ = _
  simp only [pullback.lift_fst_assoc, Category.assoc]
  rfl

variable [HasSheafify (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}]

/-- The local original sum for a splitting of the pullback of the fixed cover. -/
def chartSum {V : X.Etale} {A : FintypeCat.{u}}
    (e : (trivialCoverFunctor V.left).obj A ≅ (baseChange V.hom).obj Y) :
    (freeAbelianSheaf.{u + 1} (Scheme.smallEtaleTopology X) ((toEtale X).obj Y)).obj.obj (op V) :=
  representedSum (Scheme.smallEtaleTopology X) (chartSiteSection Y e)

@[simp] theorem chartSum_restrict {W V : X.Etale} (f : W ⟶ V)
    {A : FintypeCat.{u}}
    (e : (trivialCoverFunctor V.left).obj A ≅ (baseChange V.hom).obj Y) :
    (freeAbelianSheaf.{u + 1} (Scheme.smallEtaleTopology X) ((toEtale X).obj Y)).obj.map f.op
      (chartSum Y e) = chartSum Y (restrictChartSplitting Y f e) := by
  simp only [chartSum, representedSum_restrict]
  apply congrArg (representedSum (Scheme.smallEtaleTopology X))
  funext a
  exact (chartSiteSection_restrict Y f e a).symm

theorem chartSum_independent {V : X.Etale} {A B : FintypeCat.{u}}
    (e : (trivialCoverFunctor V.left).obj A ≅ (baseChange V.hom).obj Y)
    (f : (trivialCoverFunctor V.left).obj B ≅ (baseChange V.hom).obj Y) :
    chartSum Y e = chartSum Y f :=
  trivializationSum_independent (X := X) (V := V) (U := (toEtale X).obj Y)
    ((baseChange V.hom).obj Y)
    (pullback.fst Y.obj.hom V.hom) pullback.condition e f

omit [HasSheafify (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}] in
/-- The scheme structure map of the actual trivial cover is its split projection. -/
theorem trivialCover_structure_projection (S : Scheme.{u}) (A : FintypeCat.{u}) :
    (trivialCover S A).obj.hom =
      (trivialCoverSigmaIso S A).hom ≫ Scheme.SplitProjection.projection A S := by
  apply (isColimitOfHasCoproductOfPreservesColimit (forgetToScheme S)
    (fun _ : A => terminalCover S)).hom_ext
  intro a
  change (trivialCoverι S A a.as).hom.left ≫ (trivialCover S A).obj.hom =
    (trivialCoverι S A a.as).hom.left ≫
      (trivialCoverSigmaIso S A).hom ≫ Scheme.SplitProjection.projection A S
  rw [trivialCoverι_struct, ← Category.assoc, trivialCoverSigmaIso_ι]
  exact (Sigma.ι_comp_desc (fun _ : A => 𝟙 S) a.as).symm

omit [HasSheafify (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}] in
/-- A splitting has the actual finite-flat rank of the original cover. -/
theorem chartSplitting_card {V : X.Etale} {A : FintypeCat.{u}}
    (e : (trivialCoverFunctor V.left).obj A ≅ (baseChange V.hom).obj Y) (v : V.left) :
    Fintype.card A = Y.obj.hom.finrank (V.hom v) := by
  have he : IsIso e.hom.hom.left := inferInstance
  have h := congrArg (fun g : (trivialCover V.left A).obj.left ⟶ V.left => g.finrank v)
    (Over.w e.hom.hom)
  rw [Scheme.Hom.finrank_comp_left_of_isIso] at h
  change (pullback.snd Y.obj.hom V.hom).finrank v =
    (trivialCover V.left A).obj.hom.finrank v at h
  rw [Scheme.Hom.finrank_pullback_snd, trivialCover_structure_projection,
    Scheme.Hom.finrank_comp_left_of_isIso, Scheme.SplitProjection.rank] at h
  exact (Nat.card_eq_fintype_card (α := A)).symm.trans h.symm

omit [HasSheafify (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}] in
/-- Every base point admits an actual labelled splitting chart. -/
theorem exists_labelled_chart (x : X) :
    ∃ (V : X.Etale) (A : FintypeCat.{u})
      (_e : (trivialCoverFunctor V.left).obj A ≅ (baseChange V.hom).obj Y)
      (v : V.left), V.hom v = x := by
  obtain ⟨V, v, hv, he, _⟩ := exists_etale_trivialization_at_point Y x
  exact ⟨V, FintypeCat.of (Fiber (algebraicClosureResiduePoint X x) Y), he.some, v, hv⟩

/-- The original local sums form a matching family on any chosen splitting cover. -/
theorem chartSum_matching {I : Type u} (V : I → X.Etale) (A : I → FintypeCat.{u})
    (e : ∀ i, (trivialCoverFunctor (V i).left).obj (A i) ≅ (baseChange (V i).hom).obj Y)
    (i j : I) (W : X.Etale) (f : W ⟶ V i) (g : W ⟶ V j) :
    (freeAbelianSheaf.{u + 1} (Scheme.smallEtaleTopology X) ((toEtale X).obj Y)).obj.map f.op
        (chartSum Y (e i)) =
      (freeAbelianSheaf.{u + 1} (Scheme.smallEtaleTopology X) ((toEtale X).obj Y)).obj.map g.op
        (chartSum Y (e j)) := by
  rw [chartSum_restrict, chartSum_restrict]
  exact chartSum_independent Y _ _

end AlgebraicGeometry.Scheme.FiniteEtale
