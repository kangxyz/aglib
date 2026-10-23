/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.ProperSubalgebraModel
public import Aglib.AlgebraicGeometry.Morphisms.Proper.Chow.Projective
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Cartesian
public import Aglib.AlgebraicGeometry.Approximation.Proper.FiniteType

/-! # Original projective modification packets for proper affine-base reduction

Transport the published Noetherian Chow modification along an actual proper
arithmetic model and the original projective-space base-change isomorphism.
For an arbitrary proper morphism, a closed projection to the published proper
finite-presentation system reduces to that case. No Chow theorem or projective
geometry is reproved and the original structural morphism is retained.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper.Reduction

universe u

variable (R : Type u) [CommRing R]

/-- A proper finitely presented scheme over an arbitrary original spectrum
has an actual proper surjective modification embedded in standard projective space. -/
theorem exists_projective_modification_of_finitePresentation
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f]
    [LocallyOfFinitePresentation f] :
    ∃ (Y : Scheme.{u}) (p : Y ⟶ X) (m : ℕ)
      (j : Y ⟶ ProjectiveSpace R (ULift.{u} (Fin (m + 1)))),
      IsProper p ∧ Surjective p ∧ IsClosedImmersion j ∧
        j ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin (m + 1))) = p ≫ f := by
  obtain ⟨s, M, hM⟩ :=
    FiniteTypeSubalgebraLimit.exists_properModel_over_finiteTypeSubalgebra ℤ R f
  let B := Algebra.FiniteTypeSubalgebraLimit.stage ℤ R s
  let σ : B →+* R := (Algebra.FiniteTypeSubalgebraLimit.stage ℤ R s).val.toRingHom
  let π := Spec.map (CommRingCat.ofHom σ)
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing ℤ B
  have : IsProper M.f := hM
  obtain ⟨Y, p, m, j, _, hp, hs, hj, hbase, _, _⟩ :=
    Chow.exists_projective_modification B M.f
  let YO : Over (Spec (.of B)) := Over.mk (p ≫ M.f)
  let PO : Over (Spec (.of B)) :=
    Over.mk (ProjectiveSpace.toSpec B (ULift.{u} (Fin (m + 1))))
  let pO : YO ⟶ Over.mk M.f := Over.homMk p
  let jO : YO ⟶ PO := Over.homMk j hbase
  let YR := (Over.pullback π).obj YO
  let e : Over.mk (ProjectiveSpace.toSpec R (ULift.{u} (Fin (m + 1)))) ≅
      (Over.pullback π).obj PO :=
    Over.isoMk (ProjectiveSpace.baseChangeIso σ (ULift.{u} (Fin (m + 1))))
      (ProjectiveSpace.baseChangeIso_hom_snd σ (ULift.{u} (Fin (m + 1))))
  let pR : YR ⟶ Over.mk f := (Over.pullback π).map pO ≫ M.overIso.hom
  let jR : YR ⟶ Over.mk
      (ProjectiveSpace.toSpec R (ULift.{u} (Fin (m + 1)))) :=
    (Over.pullback π).map jO ≫ e.inv
  have hpp : IsProper ((Over.pullback π).map pO).left :=
    MorphismProperty.overPullbackMap (P := @IsProper) π pO hp
  have hsp : Surjective ((Over.pullback π).map pO).left :=
    MorphismProperty.overPullbackMap (P := @Surjective) π pO hs
  have hjp : IsClosedImmersion ((Over.pullback π).map jO).left :=
    MorphismProperty.overPullbackMap (P := @IsClosedImmersion) π jO hj
  refine ⟨YR.left, pR.left, m, jR.left, ?_, ?_, ?_, ?_⟩
  · change IsProper (((Over.pullback π).map pO).left ≫ M.overIso.hom.left)
    infer_instance
  · change Surjective (((Over.pullback π).map pO).left ≫ M.overIso.hom.left)
    infer_instance
  · change IsClosedImmersion (((Over.pullback π).map jO).left ≫ e.inv.left)
    infer_instance
  · exact (Over.w jR).trans (Over.w pR).symm

/-- The published closed-projection proper approximation removes finite
presentation from the original affine-base projective-modification packet. -/
theorem exists_projective_modification
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f] :
    ∃ (Y : Scheme.{u}) (p : Y ⟶ X) (m : ℕ)
      (j : Y ⟶ ProjectiveSpace R (ULift.{u} (Fin (m + 1)))),
      IsProper p ∧ Surjective p ∧ IsClosedImmersion j ∧
        j ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin (m + 1))) = p ≫ f := by
  classical
  obtain ⟨M⟩ := Approximation.nonempty_properFinitePresentationSystem f
  let i : M.index := Classical.choice IsCofiltered.nonempty
  let qO : Over.mk f ⟶ M.diagram.obj i := (eqToIso M.point).inv ≫ M.cone.π.app i
  let q := qO.left
  have : IsClosedImmersion q := by
    change IsClosedImmersion ((eqToIso M.point).inv.left ≫ (M.cone.π.app i).left)
    infer_instance
  obtain ⟨Y, p, m, j, hp, hs, hj, hbase⟩ :=
    exists_projective_modification_of_finitePresentation R (M.diagram.obj i).hom
  have : IsProper p := hp
  have : Surjective p := hs
  have : IsClosedImmersion j := hj
  let Z := pullback p q
  let r : Z ⟶ X := pullback.snd p q
  let jR : Z ⟶ ProjectiveSpace R (ULift.{u} (Fin (m + 1))) := pullback.fst p q ≫ j
  refine ⟨Z, r, m, jR, ?_, ?_, ?_, ?_⟩
  · dsimp [r]
    infer_instance
  · dsimp [r]
    infer_instance
  · dsimp [jR]
    infer_instance
  · change (pullback.fst p q ≫ j) ≫ _ = pullback.snd p q ≫ f
    rw [Category.assoc, hbase, ← Category.assoc, pullback.condition,
      Category.assoc, Over.w qO]
    rfl

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper.Reduction
