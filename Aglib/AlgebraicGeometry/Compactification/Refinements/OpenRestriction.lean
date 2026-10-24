/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.Category
public import Aglib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant.OpenFactor

/-!
# Restricting a compactification over an open target

A dense compactification of a map followed by a quasi-compact open immersion
restricts to a dense compactification of the original map. The intermediate
scheme is the literal pullback, and both original projections are retained.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom.DenseCompactification

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (i : Y ⟶ Z)
  (C : DenseCompactification (f ≫ i))

/-- The original source factors through the actual inverse image of the open target. -/
def openRestrictionSource : X ⟶ pullback i C.p :=
  pullback.lift f C.j C.fac.symm

@[reassoc (attr := simp)]
lemma openRestrictionSource_fst :
    openRestrictionSource f i C ≫ pullback.fst i C.p = f :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma openRestrictionSource_snd :
    openRestrictionSource f i C ≫ pullback.snd i C.p = C.j :=
  pullback.lift_snd _ _ _

variable [IsOpenImmersion i]

instance openRestrictionSource_isOpenImmersion :
    IsOpenImmersion (openRestrictionSource f i C) := by
  have : IsOpenImmersion (openRestrictionSource f i C ≫ pullback.snd i C.p) := by
    rw [openRestrictionSource_snd]
    infer_instance
  exact IsOpenImmersion.of_comp (openRestrictionSource f i C) (pullback.snd i C.p)

variable [QuasiCompact i]

instance openRestrictionSource_isSchemeTheoreticallyDominant :
    IsSchemeTheoreticallyDominant (openRestrictionSource f i C) := by
  have : IsSchemeTheoreticallyDominant
      (openRestrictionSource f i C ≫ pullback.snd i C.p) := by
    rw [openRestrictionSource_snd]
    infer_instance
  exact IsSchemeTheoreticallyDominant.of_comp_left_of_isOpenImmersion
    (openRestrictionSource f i C) (pullback.snd i C.p)

/-- Restrict the proper ambient map to the open target, preserving the original source. -/
def openRestriction : DenseCompactification f where
  Xbar := pullback i C.p
  j := openRestrictionSource f i C
  p := pullback.fst i C.p
  isOpenImmersion_j := inferInstance
  isProper_p := inferInstance
  fac := openRestrictionSource_fst f i C
  isSchemeTheoreticallyDominant_j := inferInstance

/-- The proper map of the restricted compactification is the actual base change. -/
lemma isPullback_openRestriction :
    IsPullback (pullback.snd i C.p) (openRestriction f i C).p C.p i :=
  (IsPullback.of_hasPullback i C.p).flip

/-- The two open embeddings in the restricted tower compose to the original embedding. -/
@[simp, reassoc]
lemma openRestriction_j_snd :
    (openRestriction f i C).j ≫ pullback.snd i C.p = C.j :=
  openRestrictionSource_snd f i C

end AlgebraicGeometry.Scheme.Hom.DenseCompactification
