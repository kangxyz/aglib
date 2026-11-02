/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.CompositionBaseChangeRefinement
public import Aglib.AlgebraicGeometry.Compactification.Refinements.BaseChangeSourceIso

/-! # Refinement to the source-transported literal dense base change

Both models are compared inside the same raw proper pullback. This retains the
literal dense base change followed by its original source-isomorphism transport,
not a definitional identification with densification after source transport.
-/

@[expose] public noncomputable section
open CategoryTheory Limits
universe u
namespace AlgebraicGeometry.Scheme.Hom.DenseCompactification

variable {X S X' T : Scheme.{u}} {f : X ⟶ S} [QuasiCompact f]
  (C : DenseCompactification f) (f' : X' ⟶ T) (a : X' ⟶ X) (b : T ⟶ S)
  (sq : IsPullback a f' f b)
  (E : DenseCompactification f') (q : E.Xbar ⟶ C.Xbar)
  (hj : E.j ≫ q = a ≫ C.j) (hp : q ≫ C.p = E.p ≫ b)

local notation "D" => Functor.obj
  (sourceIso f' sq.flip.isoPullback sq.flip.isoPullback_hom_fst)
  (baseChangeObj b C)
local notation "r" => Compactification.cartesianRefinementRawMap C.toCompactification f' b E q hp

include hj in
/-- The two maps to the same raw ambient have the same original open restriction. -/
lemma cartesianSourceRefinement_open :
    E.j ≫ r = (D).j ≫ baseChangeNormalization b C := by
  have h := Compactification.j_cartesianRefinementRawMap
    C.toCompactification f' a b sq E q hj hp
  exact h.trans ((Category.assoc _ _ _).trans
    (congrArg (fun k => sq.flip.isoPullback.hom ≫ k) (baseChange_j_normalization b C))).symm

/-- The actual dense refinement to the literal dense pullback transported on its source. -/
def cartesianSourceRefinement : E ⟶ D :=
  @closedAmbientRefinement X' T (pullback b C.p) f' E D (pullback.fst b C.p) r
    (baseChangeNormalization b C) (baseChangeNormalization_isClosedImmersion b C)
    (cartesianSourceRefinement_open C f' a b sq E q hj hp)
    (Compactification.cartesianRefinementRawMap_fst C.toCompactification f' b E q hp)
    (baseChangeNormalization_fst b C)

/-- The actual refinement retains the original raw ambient lift. -/
@[reassoc]
lemma cartesianSourceRefinement_normalization :
    (cartesianSourceRefinement C f' a b sq E q hj hp).hom ≫ baseChangeNormalization b C = r :=
  @closedAmbientMap_comp X' T (pullback b C.p) f' E D r
    (baseChangeNormalization b C) (baseChangeNormalization_isClosedImmersion b C)
    (cartesianSourceRefinement_open C f' a b sq E q hj hp)

/-- Its projection to the original ambient is the given original ambient map. -/
@[reassoc]
lemma cartesianSourceRefinement_projection :
    (cartesianSourceRefinement C f' a b sq E q hj hp).hom ≫
      baseChangeNormalization b C ≫ pullback.snd b C.p = q := by
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ pullback.snd b C.p)
      (cartesianSourceRefinement_normalization C f' a b sq E q hj hp)).trans
        (Compactification.cartesianRefinementRawMap_snd C.toCompactification f' b E q hp))

end AlgebraicGeometry.Scheme.Hom.DenseCompactification
