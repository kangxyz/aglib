/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.ProperBinaryCoverModel
public import Aglib.AlgebraicGeometry.Modules.Invertible.Descent.OverIso
public import Aglib.AlgebraicGeometry.Modules.Invertible.Formal.Henselian.GeometricBaseChange
public import Aglib.RingTheory.Localization.IntegerLocalTarget

/-!
# Henselian Picard lifting for proper finitely presented schemes with two affine opens

The native integer localization supplies an actual characteristic-zero DVR
mapping to the arbitrary local base. The original proper fp scheme and its
affine binary cover descend to one finite arithmetic model. Geometric local
lifting and the marked residue limit then lift every original fibre bundle.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules.Invertible

universe u

/-- Every original residue-fibre bundle lifts on a proper finitely presented
scheme with an affine binary cover over any henselian local ring. -/
theorem exists_lineBundle_lift_residue_affineBinary_of_finitePresentation
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    {X : Scheme.{u}} (A : Scheme.AffineBinaryCover X)
    (f : X ⟶ Spec (.of R)) [IsProper f] [LocallyOfFinitePresentation f]
    (L : LineBundle (Limits.pullback f (LocalRing.residueSpecMap R))) :
    ∃ W : LineBundle X,
      Nonempty ((pullback (Limits.pullback.fst f (LocalRing.residueSpecMap R))).obj W.val ≅
        L.val) := by
  let D := Localization.IntegerLocalTarget.Ring R
  let : Algebra D R := (Localization.IntegerLocalTarget.map R).toAlgebra
  obtain ⟨C, hC, aC, hfinite, aR, M, hM, ⟨B⟩⟩ :=
    Scheme.FiniteTypeSubalgebraLimit.exists_properModel_with_affineBinaryCover D R f A
  let := hC
  let := aC
  let := hfinite
  let := aR
  let := hM
  exact exists_lineBundle_lift_of_overIso
    (Limits.pullback.snd M.f (Spec.algebraMap C R)) f (LocalRing.residueSpecMap R)
    M.overIso (fun N => exists_lineBundle_lift_affineBinary_geometricBaseChange D C R B M.f N) L

end AlgebraicGeometry.Scheme.Modules.Invertible
