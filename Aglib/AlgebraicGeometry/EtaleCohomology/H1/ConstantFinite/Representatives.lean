/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.ConstantFinite.Basic

/-! # Actual finite scheme torsors representing finite constant H1 classes -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.EtaleCohomology.ConstantFinite

universe u w

attribute [local instance] hasSheafifyLarge Over.cartesianMonoidalCategory

variable (A : Type u) [AddCommGroup A] [Finite A] (X : Scheme.{u})
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- Every original finite constant H1 class is represented by an actual
surjective finite etale scheme with its genuine coefficient-group action.
The equality retains the native torsor Ext class and original coefficient map. -/
theorem exists_schemeTorsorRepresentative (c : H1Etale X (coefficient A X)) :
    ∃ (Y : Scheme.FiniteEtale X)
      (τ : TorsorAction (representation A X).group (toUnit Y.obj))
      (hY : Surjective Y.obj.hom),
      letI := hY
      coefficientMap (representation A X).iso.hom
        (torsorExtClass (torsorOfSchemeAction (representation A X).group Y τ)) = c := by
  let D := representation A X
  have hG : IsFiniteLocallyConstant (representedSheaf D.group) :=
    (isFiniteLocallyConstant_iff_of_iso D.iso).mpr (isFiniteLocallyConstant A X)
  obtain ⟨a, ha⟩ := (stacks03AJ X).bijective (representedSheaf D.group) |>.surjective
    ((coefficientIso D.iso).symm c)
  revert ha
  refine Quotient.inductionOn a ?_
  intro P hP
  let Y :=
    _root_.AlgebraicGeometry.Scheme.EtaleCohomology.Torsor.finiteEtaleRepresentative
      (P := P) (stacks03RV X) hG
  let e :=
    _root_.AlgebraicGeometry.Scheme.EtaleCohomology.Torsor.finiteEtaleRepresentativeIso
      (P := P) (stacks03RV X) hG
  have hY : Surjective Y.obj.hom :=
    _root_.AlgebraicGeometry.Scheme.EtaleCohomology.Torsor.represented_surjective
      (H := D.group) (P := P) (Y := Y) (e := e)
  let τ :=
    _root_.AlgebraicGeometry.Scheme.EtaleCohomology.Torsor.representedSchemeAction
      (H := D.group) (P := P) (Y := Y) (e := e)
  refine ⟨Y, τ, hY, ?_⟩
  have heq : torsorExtClass (torsorOfSchemeAction D.group Y τ) = torsorExtClass P :=
    torsorExtClass_iso
      (_root_.AlgebraicGeometry.Scheme.EtaleCohomology.Torsor.representedSchemeActionIso
        (H := D.group) (P := P) (Y := Y) (e := e))
  rw [heq]
  change coefficientIso D.iso (torsorExtClass P) = c
  change torsorExtClass P = (coefficientIso D.iso).symm c at hP
  rw [hP, AddEquiv.apply_symm_apply]

end AlgebraicGeometry.Scheme.EtaleCohomology.ConstantFinite
