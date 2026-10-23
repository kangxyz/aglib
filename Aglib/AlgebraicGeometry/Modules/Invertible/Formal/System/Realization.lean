/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Formal.System.Adic

/-! # Original geometric reductions of a realization of a line-bundle system -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules.Coherent

namespace AlgebraicGeometry.Scheme.Modules.Invertible.CompatibleLineBundleSystem

universe u

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of R)} {I : Ideal R} [IsLocallyNoetherian X]
  (S : CompatibleLineBundleSystem f I)

/-- An isomorphism from a native coherent completion gives an actual
pullback isomorphism on every original geometric thickening. -/
def geometricReductionIso (M : X.CoherentSheaf)
    (β : (completionFunctor X (idealThickeningIdealSheaf f I)).obj M ≅ S.toAdicSystem)
    (n : ℕ) :
    (pullback (idealThickeningι f (I ^ (n + 1)))).obj M.obj ≅ (S.bundle n).val := by
  let i := idealThickeningι f (I ^ (n + 1))
  letI := pullbackPushforwardCounit_isIso_of_closedImmersion i ((pullback i).obj M.obj)
  exact (asIso ((pullbackPushforwardAdjunction i).counit.app
      ((pullback i).obj M.obj))).symm ≪≫
    (pullback i).mapIso
      ((nativeQuotientIso (f := f) (I := I) (n + 1) M.obj).symm ≪≫
        ((adicSystemToDiagram X (idealThickeningIdealSheaf f I)).mapIso β).app
          (op (n + 1))) ≪≫ S.positiveStageIso n

end AlgebraicGeometry.Scheme.Modules.Invertible.CompatibleLineBundleSystem
