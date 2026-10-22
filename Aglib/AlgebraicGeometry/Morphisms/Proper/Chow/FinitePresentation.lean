/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.SeparatedSubalgebraModel
public import Aglib.AlgebraicGeometry.Morphisms.Proper.Chow.WeakAffine

/-!
# Weak Chow for finitely presented schemes over arbitrary affine bases

Descend the original separated finitely presented scheme to an actual
Noetherian arithmetic stage, construct weak Chow there, and pull the complete
modification packet back. The target is proper; no new projective embedding
or arbitrary finite-type Chow theorem is asserted.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Chow

/-- A complete actual modification packet over the original base. -/
structure ImmersionProperModification {S : Scheme.{u}} (X : Over S) where
  /-- The modifying scheme over the base. -/
  source : Over S
  /-- Its proper ambient target over the base. -/
  target : Over S
  /-- The original proper surjective modification map. -/
  toSource : source ⟶ X
  /-- The actual immersion into the proper target. -/
  toTarget : source ⟶ target
  /-- Properness of the modification. -/
  proper_toSource : IsProper toSource.left
  /-- Surjectivity of the modification. -/
  surjective_toSource : Surjective toSource.left
  /-- The map into the proper ambient scheme is immersive. -/
  immersion_toTarget : IsImmersion toTarget.left
  /-- The ambient target is proper over the original base. -/
  proper_target : IsProper target.hom

attribute [instance] ImmersionProperModification.proper_toSource
  ImmersionProperModification.surjective_toSource
  ImmersionProperModification.immersion_toTarget ImmersionProperModification.proper_target

namespace ImmersionProperModification

/-- Pull back the complete packet and transport its endpoint along the
specified native over-isomorphism. -/
def baseChange {S T : Scheme.{u}} {X : Over S}
    (M : ImmersionProperModification X) (f : T ⟶ S) {Z : Over T}
    (e : (Over.pullback f).obj X ≅ Z) : ImmersionProperModification Z := by
  have hp : IsProper ((Over.pullback f).map M.toSource).left :=
    MorphismProperty.overPullbackMap (P := @IsProper) f M.toSource inferInstance
  have hs : Surjective ((Over.pullback f).map M.toSource).left :=
    MorphismProperty.overPullbackMap (P := @Surjective) f M.toSource inferInstance
  have hq : IsImmersion ((Over.pullback f).map M.toTarget).left :=
    MorphismProperty.overPullbackMap (P := @IsImmersion) f M.toTarget inferInstance
  refine
    { source := (Over.pullback f).obj M.source
      target := (Over.pullback f).obj M.target
      toSource := (Over.pullback f).map M.toSource ≫ e.hom
      toTarget := (Over.pullback f).map M.toTarget
      proper_toSource := ?_
      surjective_toSource := ?_
      immersion_toTarget := hq
      proper_target := ?_ }
  · change IsProper (((Over.pullback f).map M.toSource).left ≫ e.hom.left)
    infer_instance
  · change Surjective (((Over.pullback f).map M.toSource).left ≫ e.hom.left)
    infer_instance
  · change IsProper (pullback.snd M.target.hom f)
    infer_instance

/-- Transport a complete packet from the spectrum presentation of an affine
base, preserving the specified original over-object. -/
def ofIsoBase {S T : Scheme.{u}} (e : S ≅ T) (X : Over S)
    (M : ImmersionProperModification (Over.mk (X.hom ≫ e.hom))) :
    ImmersionProperModification X := by
  let Y : Over S := Over.mk (M.source.hom ≫ e.inv)
  let P : Over S := Over.mk (M.target.hom ≫ e.inv)
  have hp : M.toSource.left ≫ X.hom = Y.hom := by
    simpa only [Y, Over.mk_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id] using
      congrArg (fun h => h ≫ e.inv) M.toSource.w
  have hq : M.toTarget.left ≫ P.hom = Y.hom := by
    simpa only [P, Y, Over.mk_hom, Category.assoc] using
      congrArg (fun h => h ≫ e.inv) M.toTarget.w
  exact
    { source := Y
      target := P
      toSource := Over.homMk M.toSource.left hp
      toTarget := Over.homMk M.toTarget.left hq
      proper_toSource := M.proper_toSource
      surjective_toSource := M.surjective_toSource
      immersion_toTarget := M.immersion_toTarget
      proper_target := by dsimp [P]; infer_instance }

end ImmersionProperModification

/-- A separated finitely presented scheme over an arbitrary spectrum has an
actual proper-surjective modification immersive in a proper target. -/
theorem nonempty_immersionProperModification_spec (R : Type u) [CommRing R]
    (X : Over (Spec (.of R)))
    [IsSeparated X.hom] [LocallyOfFinitePresentation X.hom] [QuasiCompact X.hom] :
    Nonempty (ImmersionProperModification X) := by
  obtain ⟨s, M, hM⟩ :=
    FiniteTypeSubalgebraLimit.exists_separatedModel_over_finiteTypeSubalgebra ℤ R X.hom
  let := hM
  let B := Algebra.FiniteTypeSubalgebraLimit.stage ℤ R s
  let : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing ℤ B
  have : IsSeparated (Over.mk M.f).hom := inferInstanceAs (IsSeparated M.f)
  have : LocallyOfFiniteType (Over.mk M.f).hom := inferInstanceAs (LocallyOfFiniteType M.f)
  have : QuasiCompact (Over.mk M.f).hom := inferInstanceAs (QuasiCompact M.f)
  obtain ⟨Y, P, p, q, hp, hs, hq, hP⟩ :=
    exists_immersion_proper_modification (Over.mk M.f)
  let N : ImmersionProperModification (Over.mk M.f) :=
    ⟨Y, P, p, q, hp, hs, hq, hP⟩
  exact ⟨N.baseChange (Spec.map (CommRingCat.ofHom
    (Algebra.FiniteTypeSubalgebraLimit.stage ℤ R s).val.toRingHom)) M.overIso⟩

/-- A separated finitely presented object over an arbitrary affine scheme
admits an actual proper surjective modification immersive in a proper object.
The modification is constructed internally, with no Noetherian base premise. -/
theorem exists_immersion_proper_modification_of_finitePresentation {S : Scheme.{u}}
    [IsAffine S] (X : Over S)
    [IsSeparated X.hom] [LocallyOfFinitePresentation X.hom] [QuasiCompact X.hom] :
    ∃ (Y P : Over S) (p : Y ⟶ X) (q : Y ⟶ P),
      IsProper p.left ∧ Surjective p.left ∧ IsImmersion q.left ∧ IsProper P.hom := by
  have : IsSeparated (Over.mk (X.hom ≫ S.isoSpec.hom)).hom :=
    inferInstanceAs (IsSeparated (X.hom ≫ S.isoSpec.hom))
  have : LocallyOfFinitePresentation (Over.mk (X.hom ≫ S.isoSpec.hom)).hom :=
    inferInstanceAs (LocallyOfFinitePresentation (X.hom ≫ S.isoSpec.hom))
  have : QuasiCompact (Over.mk (X.hom ≫ S.isoSpec.hom)).hom :=
    inferInstanceAs (QuasiCompact (X.hom ≫ S.isoSpec.hom))
  obtain ⟨M⟩ := nonempty_immersionProperModification_spec Γ(S, ⊤)
    (Over.mk (X.hom ≫ S.isoSpec.hom))
  let N := M.ofIsoBase S.isoSpec X
  exact ⟨N.source, N.target, N.toSource, N.toTarget,
    N.proper_toSource, N.surjective_toSource, N.immersion_toTarget, N.proper_target⟩

end AlgebraicGeometry.Scheme.Chow
