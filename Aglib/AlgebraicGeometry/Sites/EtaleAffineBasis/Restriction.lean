/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import Mathlib.Algebra.Category.Grp.Limits

/-!
# Affine étale restriction at the large coefficient universe

The dense affine subsite compares the original small étale sheaf category with
abelian coefficients in universe `u + 1`. The inverse of the displayed
equivalence is the literal restriction functor, not a resized coefficient
category. This supplies the size-preserving restriction boundary for continuity.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleAffineBasis

/-- Restriction along the original affine étale inclusion with unchanged values. -/
abbrev abelianRestriction (S : Scheme.{u}) :
    Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf (Scheme.AffineEtale.topology S) AddCommGrpCat.{u + 1} :=
  (Scheme.AffineEtale.Spec S).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (Scheme.AffineEtale.topology S) S.smallEtaleTopology

instance abelianRestriction_isEquivalence (S : Scheme.{u}) :
    (abelianRestriction S).IsEquivalence := by
  dsimp only [abelianRestriction]
  infer_instance

/-- The affine-site comparison retains coefficients in `AddCommGrpCat.{u+1}`. -/
def abelianSheafEquiv (S : Scheme.{u}) :
    Sheaf (Scheme.AffineEtale.topology S) AddCommGrpCat.{u + 1} ≌
      Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (abelianRestriction S).asEquivalence.symm

/-- The inverse comparison is the original restriction functor. -/
theorem abelianSheafEquiv_inverse (S : Scheme.{u}) :
    (abelianSheafEquiv S).inverse = abelianRestriction S := rfl

/-- Restriction leaves the value on each affine étale object unchanged. -/
theorem abelianRestriction_obj (S : Scheme.{u})
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) (U : S.AffineEtale) :
    ((abelianRestriction S).obj F).obj.obj (op U) =
      F.obj.obj (op ((Scheme.AffineEtale.Spec S).obj U)) := rfl

instance abelianRestriction_preservesLimits (S : Scheme.{u}) :
    PreservesLimits (abelianRestriction S) := by infer_instance

instance abelianRestriction_preservesColimits (S : Scheme.{u}) :
    PreservesColimits (abelianRestriction S) := by infer_instance

end AlgebraicGeometry.Scheme.EtaleAffineBasis
