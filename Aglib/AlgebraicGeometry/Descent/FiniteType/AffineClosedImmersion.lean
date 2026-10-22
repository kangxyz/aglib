/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.Ring.Descent.FiniteType.Surjectivity
public import Aglib.Algebra.Category.Ring.Descent.FiniteType.Propagation
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Eventual closed immersion in affine generated systems

This lower lemma translates actual affine scheme systems to their rings
of global sections and applies finite-type eventual surjectivity. Its
affineness assumptions belong only to this affine lemma. A global proof
must obtain such affine systems by localization and eventual affineness,
not assume that the original base stages are affine.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme

/-- A closed limit arrow of affine systems descends when the chosen stage
arrow is locally of finite type and the old source-ring image together
with the new target-ring image generate every later source ring. No
cartesian transition condition or finite-presentation assumption is imposed. -/
lemma exists_isClosedImmersion_app_of_isLimit_of_isAffine_of_closure_eq_top
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D E : I ⥤ Scheme.{u}) [∀ j, IsAffine (D.obj j)] [∀ j, IsAffine (E.obj j)]
    (α : D ⟶ E) (cD : Cone D) (hD : IsLimit cD) (cE : Cone E) (hE : IsLimit cE)
    (f : cD.pt ⟶ cE.pt)
    (hf : ∀ j, f ≫ cE.π.app j = cD.π.app j ≫ α.app j)
    (i : I) [LocallyOfFiniteType (α.app i)]
    (hgenerate : ∀ (j : I) (q : j ⟶ i),
      Subring.closure (Set.range (D.map q).appTop ∪ Set.range (α.app j).appTop) = ⊤)
    [IsClosedImmersion f] :
    ∃ (j : I) (_q : j ⟶ i), IsClosedImmersion (α.app j) := by
  have (j : I) : CompactSpace (D.obj j) := inferInstance
  have (j : I) : CompactSpace (E.obj j) := inferInstance
  have (j : I) : QuasiSeparatedSpace (D.obj j) := inferInstance
  have (j : I) : QuasiSeparatedSpace (E.obj j) := inferInstance
  have {j k : I} (q : j ⟶ k) : IsAffineHom (D.map q) := inferInstance
  have {j k : I} (q : j ⟶ k) : IsAffineHom (E.map q) := inferInstance
  have : IsAffine cD.pt := Scheme.isAffine_of_isLimit cD hD
  have : IsAffine cE.pt := Scheme.isAffine_of_isLimit cE hE
  let F := E.op ⋙ Scheme.Γ
  let G := D.op ⋙ Scheme.Γ
  let β : F ⟶ G := Functor.whiskerRight (NatTrans.op α) Scheme.Γ
  let cF : Cocone F := Scheme.Γ.mapCocone cE.op
  let cG : Cocone G := Scheme.Γ.mapCocone cD.op
  have hF : IsColimit cF := (nonempty_isColimit_Γ_mapCocone E cE hE).some
  have hG : IsColimit cG := (nonempty_isColimit_Γ_mapCocone D cD hD).some
  have hcompat (j : Iᵒᵖ) : β.app j ≫ cG.ι.app j = cF.ι.app j ≫ f.appTop := by
    change (α.app j.unop).appTop ≫ (cD.π.app j.unop).appTop =
      (cE.π.app j.unop).appTop ≫ f.appTop
    simpa only [Scheme.Hom.comp_appTop] using
      (congrArg Scheme.Hom.appTop (hf j.unop)).symm
  have hfinite : (β.app (op i)).hom.FiniteType :=
    HasRingHomProperty.appTop @LocallyOfFiniteType (α.app i) inferInstance
  obtain ⟨j, q, hj⟩ := CommRingCat.exists_surjective_app_of_isColimit_of_closure_eq_top
    F G β cF hF cG hG f.appTop hcompat (op i) hfinite
    (fun j q ↦ hgenerate j.unop q.unop)
    (IsClosedImmersion.isAffine_surjective_of_isAffine f).2
  exact ⟨j.unop, q.unop, IsClosedImmersion.of_surjective_of_isAffine (α.app j.unop) hj⟩

/-- A closed limit arrow of affine systems descends when the chosen stage
arrow is locally of finite type and its later transition squares are
actual pullbacks. No finite-presentation assumption is imposed. -/
lemma exists_isClosedImmersion_app_of_isLimit_of_isAffine
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D E : I ⥤ Scheme.{u}) [∀ j, IsAffine (D.obj j)] [∀ j, IsAffine (E.obj j)]
    (α : D ⟶ E) (cD : Cone D) (hD : IsLimit cD) (cE : Cone E) (hE : IsLimit cE)
    (f : cD.pt ⟶ cE.pt)
    (hf : ∀ j, f ≫ cE.π.app j = cD.π.app j ≫ α.app j)
    (i : I) [LocallyOfFiniteType (α.app i)]
    (hcart : ∀ (j : I) (q : j ⟶ i),
      IsPullback (α.app j) (D.map q) (E.map q) (α.app i))
    [IsClosedImmersion f] :
    ∃ (j : I) (_q : j ⟶ i), IsClosedImmersion (α.app j) := by
  apply exists_isClosedImmersion_app_of_isLimit_of_isAffine_of_closure_eq_top
    D E α cD hD cE hE f hf i
  intro j q
  exact CommRingCat.closure_range_union_range_eq_top_of_isPushout
    (isPushout_appTop_of_isPullback (hcart j q).flip)

/-- Closedness persists under a generating naturality square between affine
schemes, even when the square is not cartesian. -/
lemma isClosedImmersion_app_of_closure_eq_top
    {I : Type u} [Category.{u} I]
    (D E : I ⥤ Scheme.{u}) [∀ j, IsAffine (D.obj j)] [∀ j, IsAffine (E.obj j)]
    (α : D ⟶ E) {i j : I} (q : j ⟶ i)
    (hgenerate : Subring.closure
      (Set.range (D.map q).appTop ∪ Set.range (α.app j).appTop) = ⊤)
    [IsClosedImmersion (α.app i)] : IsClosedImmersion (α.app j) := by
  have hcomm : (α.app i).appTop ≫ (D.map q).appTop =
      (E.map q).appTop ≫ (α.app j).appTop := by
    simpa only [Scheme.Hom.comp_appTop] using
      congrArg Scheme.Hom.appTop (α.naturality q)
  exact IsClosedImmersion.of_surjective_of_isAffine (α.app j)
    (CommRingCat.surjective_of_closure_range_union_range_eq_top
      (α.app i).appTop (E.map q).appTop (D.map q).appTop (α.app j).appTop
      hcomm hgenerate (IsClosedImmersion.isAffine_surjective_of_isAffine (α.app i)).2)

end AlgebraicGeometry.Scheme
