/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.Common
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# A refinement is Cartesian above the original open source

The original source maps to the literal pullback of the target open. This map is
an open immersion, a proper section, and dominant, hence an isomorphism. The
result retains both original projections and does not use proper base change
for sheaves.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom.DenseCompactification

variable {X S : Scheme.{u}} {f : X ⟶ S} [QuasiCompact f]
  {C D : DenseCompactification f} (a : C ⟶ D)

/-- The actual comparison from the original open to the pullback of the target open. -/
def openLift : X ⟶ pullback a.hom D.j :=
  pullback.lift C.j (𝟙 X) (by simp)

omit [QuasiCompact f] in
@[reassoc (attr := simp)]
lemma openLift_fst : openLift a ≫ pullback.fst a.hom D.j = C.j := by
  exact pullback.lift_fst _ _ _

omit [QuasiCompact f] in
@[reassoc (attr := simp)]
lemma openLift_snd : openLift a ≫ pullback.snd a.hom D.j = 𝟙 X := by
  exact pullback.lift_snd _ _ _

instance openLift_isOpenImmersion : IsOpenImmersion (openLift a) := by
  have : IsOpenImmersion (openLift a ≫ pullback.fst a.hom D.j) := by
    rw [openLift_fst]
    infer_instance
  exact IsOpenImmersion.of_comp _ (pullback.fst a.hom D.j)

instance openLift_isProper : IsProper (openLift a) := by
  have : IsProper (openLift a ≫ pullback.snd a.hom D.j) := by
    rw [openLift_snd]
    infer_instance
  exact IsProper.of_comp _ (pullback.snd a.hom D.j)

instance openLift_isDominant : IsDominant (openLift a) := by
  have : IsDominant (openLift a ≫ pullback.fst a.hom D.j) := by
    rw [openLift_fst]
    infer_instance
  exact IsDominant.of_comp_of_isOpenImmersion _ (pullback.fst a.hom D.j)

instance openLift_isIso : IsIso (openLift a) := by
  let : Surjective (openLift a) :=
    surjective_of_isDominant_of_isClosed_range (openLift a)
      (openLift a).isClosedMap.isClosed_range
  exact (isIso_iff_isOpenImmersion_and_surjective (openLift a)).mpr
    ⟨inferInstance, inferInstance⟩

/-- The open square of a refinement is Cartesian with its original maps. -/
lemma isPullback_open : IsPullback C.j (𝟙 X) a.hom D.j :=
  IsPullback.of_iso_pullback ⟨by simp⟩ (asIso (openLift a))
    (openLift_fst a) (openLift_snd a)

end AlgebraicGeometry.Scheme.Hom.DenseCompactification
