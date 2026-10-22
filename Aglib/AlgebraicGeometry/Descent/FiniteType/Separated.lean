/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FiniteType.EventualClosedImmersion

/-!
# Eventual separatedness in a base-change family

The diagonal of an actual pulled morphism is compared explicitly with the
base-first pullback of its original diagonal. Global eventual closed
immersion then gives eventual separatedness. The diagonal is locally of
finite type because its composite with the first projection is identity;
no finite-presentation hypothesis on the diagonal is imposed.

This is base-change-family descent (Stacks 01ZQ), not separatedness descent
for a varying source system over a fixed base (Stacks 01ZH).
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme

/-- The original diagonal, retaining its structure over the original base. -/
def diagonalOverHom {X S : Scheme.{u}} (f : X ⟶ S) :
    Over.mk f ⟶ Over.mk (pullback.snd f f ≫ f) :=
  Over.homMk (pullback.diagonal f) (by simp)

/-- The actual target comparison for the base-first pulled diagonal. -/
def diagonalBaseChangeIso {X S T : Scheme.{u}} (b : T ⟶ S) (f : X ⟶ S) :
    pullback b (pullback.snd f f ≫ f) ≅ pullback.diagonalObj (pullback.fst b f) :=
  (pullbackSymmetry (pullback.snd f f ≫ f) b).symm ≪≫
    (diagonalObjPullbackFstIso b f).symm

/-- The literal pulled diagonal equals the original pulled arrow followed
by the specified diagonal-target isomorphism. -/
lemma diagonal_pullback_fst_eq_baseChangeOverHom
    {X S T : Scheme.{u}} (b : T ⟶ S) (f : X ⟶ S) :
    pullback.diagonal (pullback.fst b f) =
      baseChangeOverHom b (diagonalOverHom f) ≫ (diagonalBaseChangeIso b f).hom := by
  rw [baseChangeOverHom_eq_overPullback]
  simp only [diagonalBaseChangeIso, Over.mk_hom, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_assoc]
  exact diagonal_pullback_fst b f

/-- Separatedness is exactly closedness of the specified base-first pulled diagonal. -/
lemma isSeparated_pullback_fst_iff_baseChangeOverHom_diagonal
    {X S T : Scheme.{u}} (b : T ⟶ S) (f : X ⟶ S) :
    IsSeparated (pullback.fst b f) ↔
      IsClosedImmersion (baseChangeOverHom b (diagonalOverHom f)) := by
  rw [AlgebraicGeometry.isSeparated_iff, diagonal_pullback_fst_eq_baseChangeOverHom]
  exact MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _ _

/-- Separatedness descends in an actual affine-transition base-change family.
The original source is qcqs and its structural morphism is quasi-compact.
No affine base stages or finite-presentation assumptions are required. -/
lemma exists_isSeparated_pullback_fst_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ {j k} (q : j ⟶ k), IsAffineHom (D.map q)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    {X : Scheme.{u}} (f : X ⟶ D.obj i)
    [CompactSpace X] [QuasiSeparatedSpace X] [QuasiCompact f]
    [IsSeparated (pullback.fst (c.π.app i) f)] :
    ∃ j : Over i, IsSeparated (pullback.fst (D.map j.hom) f) := by
  have : CompactSpace ↥(pullback f f : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst f f)
  have : QuasiSeparatedSpace ↥(pullback f f : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.fst f f)
  have : LocallyOfFiniteType (pullback.diagonal f ≫ pullback.fst f f) := by
    simp only [pullback.diagonal_fst]
    infer_instance
  have : LocallyOfFiniteType (diagonalOverHom f).left :=
    locallyOfFiniteType_of_comp (pullback.diagonal f) (pullback.fst f f)
  have : IsClosedImmersion (baseChangeOverHom (c.π.app i) (diagonalOverHom f)) :=
    (isSeparated_pullback_fst_iff_baseChangeOverHom_diagonal (c.π.app i) f).mp inferInstance
  have : CompactSpace (Over.mk f).left := inferInstanceAs (CompactSpace X)
  have : QuasiSeparatedSpace (Over.mk f).left := inferInstanceAs (QuasiSeparatedSpace X)
  have : CompactSpace (Over.mk (pullback.snd f f ≫ f)).left :=
    inferInstanceAs (CompactSpace ↥(pullback f f : Scheme.{u}))
  have : QuasiSeparatedSpace (Over.mk (pullback.snd f f ≫ f)).left :=
    inferInstanceAs (QuasiSeparatedSpace ↥(pullback f f : Scheme.{u}))
  obtain ⟨j, hj⟩ := exists_isClosedImmersion_baseChangeOverHom_of_isLimit
    D c hc i (diagonalOverHom f)
  exact ⟨j, (isSeparated_pullback_fst_iff_baseChangeOverHom_diagonal (D.map j.hom) f).mpr hj⟩

end AlgebraicGeometry.Scheme
