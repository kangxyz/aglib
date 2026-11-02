/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.GenericH1ClassEffacement.Affine
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.GenericCoefficientPresentation
public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.GenericCoefficientPresentationConsumer
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.CoefficientCompositeZero

/-! # Original generic pointed H1 effacement

The actual generic square identifies the produced finite coefficient stage.
Affine separable effacement and the original coefficient transport then kill
the original class, retaining its independent Ext world.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement
universe u eX
attribute [local instance] hasSheafifyLarge HasExt.standard
open FiniteEtale

section Generic
variable (B k K : Type u) [CommRing B] [Field k] [Field K]
  [Algebra B K] [Algebra k K]
  {Y U : Scheme.{u}} (e : Y ⟶ Spec (.of B)) [QuasiCompact e] [QuasiSeparated e]
  (p : U ⟶ Spec (.of k))

/-- The unique canonical comparison for the actual generic square and the
actual finite coefficient stage. No second coefficient sheaf is selected. -/
def genericCoefficientStageIso
    (aη : pullback e (Spec.algebraMap B K) ⟶ U)
    (Hη : IsPullback aη (pullback.snd e (Spec.algebraMap B K))
      p (Spec.algebraMap k K))
    (L : Type u) [Field L] [Algebra K L] [Algebra k L] [IsScalarTower k K L] :
    pullback (pullback.snd e (Spec.algebraMap B K)) (Spec.algebraMap K L) ≅
      pullback p (Spec.algebraMap k L) := by
  have ht : Spec.algebraMap K L ≫ Spec.algebraMap k K = Spec.algebraMap k L := by
    rw [← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext
      (IsScalarTower.algebraMap_eq k K L).symm)
  have H := (IsPullback.of_hasPullback
    (pullback.snd e (Spec.algebraMap B K)) (Spec.algebraMap K L)).paste_horiz Hη
  rw [ht] at H
  exact H.isoPullback

end Generic

end AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement
