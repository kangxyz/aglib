/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Formal.Completion
public import Aglib.AlgebraicGeometry.Modules.Invertible.Formal.Approximation.Geometric
public import Aglib.AlgebraicGeometry.Spec.ResidueFiber

/-!
# Actual ideal-fibre line-bundle lifting over geometric henselizations

The original ideal-fibre bundle first supplies an actual bundle on the
completion base change, with its original fibre comparison. The proved
finite-data Artin application specializes that bundle back to the original
geometric henselization. No completed-bundle, fibre-comparison, algebraization
or rank-one premise remains in these endpoints.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules.Invertible

universe u v

section Field

variable (k : Type u) [Field k] (B : Type v) [CommRing B] [Algebra k B]
  [Algebra.FiniteType k B] (q : Ideal B) [q.IsPrime]

include k in
/-- Actual ideal-fibre lifting on a proper scheme with an actual two-affine
cover over the henselization of a field-geometric local ring. -/
theorem exists_lineBundle_lift_affineBinary_geometricLocal
    {X : Scheme.{v}} (A : Scheme.AffineBinaryCover X)
    (f : X ⟶ Spec (CommRingCat.of (Henselization (Localization.AtPrime q)))) [IsProper f]
    (I : Ideal (Henselization (Localization.AtPrime q))) (hI : I ≠ ⊤)
    (L : LineBundle (idealThickeningSpace f I)) :
    ∃ M : LineBundle X, Nonempty ((pullback (idealThickeningι f I)).obj M.val ≅ L.val) := by
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  have : IsNoetherianRing (Henselization (Localization.AtPrime q)) :=
    Henselization.isNoetherianRing (Localization.AtPrime q)
  obtain ⟨Lhat, ⟨e⟩⟩ := exists_completedLineBundle_of_affineBinaryCover A f I L
  exact exists_lineBundle_lift_of_completion_geometricLocal k B q f I hI Lhat L e

include k in
/-- Every actual ideal-fibre line bundle lifts on a proper scheme affine
over the native projective line of a field-geometric henselization. -/
theorem exists_lineBundle_lift_projectiveLine_geometricLocal
    {X : Scheme.{v}}
    (p : X ⟶ Scheme.ProjectiveLine.projectiveP1
      (Henselization (Localization.AtPrime q))) [IsAffineHom p]
    (f : X ⟶ Spec (CommRingCat.of (Henselization (Localization.AtPrime q)))) [IsProper f]
    (_h : p ≫ Scheme.ProjectiveLine.structureMap
      (Henselization (Localization.AtPrime q)) = f)
    (I : Ideal (Henselization (Localization.AtPrime q))) (hI : I ≠ ⊤)
    (L : LineBundle (idealThickeningSpace f I)) :
    ∃ M : LineBundle X, Nonempty ((pullback (idealThickeningι f I)).obj M.val ≅ L.val) :=
  exists_lineBundle_lift_affineBinary_geometricLocal k B q
    (projectiveLineAffineBinaryCover p) f I hI L

include k in
/-- Surjectivity of the original literal residue-fibre Picard restriction
for a proper scheme with an actual affine binary cover over a field-geometric henselization. -/
theorem pullbackClass_residue_affineBinary_geometricLocal_surjective
    {X : Scheme.{v}} (A : Scheme.AffineBinaryCover X)
    (f : X ⟶ Spec (CommRingCat.of (Henselization (Localization.AtPrime q)))) [IsProper f] :
    Function.Surjective (pullbackClass (Limits.pullback.fst f
      (Scheme.LocalRing.residueSpecMap (Henselization (Localization.AtPrime q))))) := by
  change Function.Surjective
    (pullbackClass (idealThickeningι f
      (IsLocalRing.maximalIdeal (Henselization (Localization.AtPrime q)))))
  intro a
  induction a using Quotient.inductionOn with
  | h L =>
    obtain ⟨M, ⟨e⟩⟩ := exists_lineBundle_lift_affineBinary_geometricLocal k B q A f
      (IsLocalRing.maximalIdeal (Henselization (Localization.AtPrime q)))
      (IsLocalRing.maximalIdeal.isMaximal (Henselization (Localization.AtPrime q))).ne_top L
    exact ⟨classOf X M, Quotient.sound ⟨e⟩⟩

end Field

section DVR

variable (D : Type u) [CommRing D] [IsDomain D] [IsDiscreteValuationRing D] [CharZero D]
  (B : Type v) [CommRing B] [Algebra D B] [Algebra.FiniteType D B]
  (q : Ideal B) [q.IsPrime]

include D in
/-- Actual ideal-fibre lifting on a proper scheme with an actual two-affine
cover over the henselization of a characteristic-zero DVR-geometric local ring. -/
theorem exists_lineBundle_lift_affineBinary_geometricLocal_of_charZeroDVR
    {X : Scheme.{v}} (A : Scheme.AffineBinaryCover X)
    (f : X ⟶ Spec (CommRingCat.of (Henselization (Localization.AtPrime q)))) [IsProper f]
    (I : Ideal (Henselization (Localization.AtPrime q))) (hI : I ≠ ⊤)
    (L : LineBundle (idealThickeningSpace f I)) :
    ∃ M : LineBundle X, Nonempty ((pullback (idealThickeningι f I)).obj M.val ≅ L.val) := by
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing D B
  have : IsNoetherianRing (Henselization (Localization.AtPrime q)) :=
    Henselization.isNoetherianRing (Localization.AtPrime q)
  obtain ⟨Lhat, ⟨e⟩⟩ := exists_completedLineBundle_of_affineBinaryCover A f I L
  exact exists_lineBundle_lift_of_completion_geometricLocal_of_charZeroDVR
    D B q f I hI Lhat L e

include D in
/-- Every actual ideal-fibre line bundle lifts on a proper scheme affine
over the native projective line of a characteristic-zero DVR-geometric henselization. -/
theorem exists_lineBundle_lift_projectiveLine_geometricLocal_of_charZeroDVR
    {X : Scheme.{v}}
    (p : X ⟶ Scheme.ProjectiveLine.projectiveP1
      (Henselization (Localization.AtPrime q))) [IsAffineHom p]
    (f : X ⟶ Spec (CommRingCat.of (Henselization (Localization.AtPrime q)))) [IsProper f]
    (_h : p ≫ Scheme.ProjectiveLine.structureMap
      (Henselization (Localization.AtPrime q)) = f)
    (I : Ideal (Henselization (Localization.AtPrime q))) (hI : I ≠ ⊤)
    (L : LineBundle (idealThickeningSpace f I)) :
    ∃ M : LineBundle X, Nonempty ((pullback (idealThickeningι f I)).obj M.val ≅ L.val) :=
  exists_lineBundle_lift_affineBinary_geometricLocal_of_charZeroDVR D B q
    (projectiveLineAffineBinaryCover p) f I hI L

include D in
/-- Surjectivity of the original literal residue-fibre Picard restriction
for an actual affine binary cover over a characteristic-zero DVR-geometric henselization. -/
theorem pullbackClass_residue_affineBinary_geometricLocal_of_charZeroDVR_surjective
    {X : Scheme.{v}} (A : Scheme.AffineBinaryCover X)
    (f : X ⟶ Spec (CommRingCat.of (Henselization (Localization.AtPrime q)))) [IsProper f] :
    Function.Surjective (pullbackClass (Limits.pullback.fst f
      (Scheme.LocalRing.residueSpecMap (Henselization (Localization.AtPrime q))))) := by
  change Function.Surjective
    (pullbackClass (idealThickeningι f
      (IsLocalRing.maximalIdeal (Henselization (Localization.AtPrime q)))))
  intro a
  induction a using Quotient.inductionOn with
  | h L =>
    obtain ⟨M, ⟨e⟩⟩ := exists_lineBundle_lift_affineBinary_geometricLocal_of_charZeroDVR
      D B q A f (IsLocalRing.maximalIdeal (Henselization (Localization.AtPrime q)))
      (IsLocalRing.maximalIdeal.isMaximal (Henselization (Localization.AtPrime q))).ne_top L
    exact ⟨classOf X M, Quotient.sound ⟨e⟩⟩

end DVR

end AlgebraicGeometry.Scheme.Modules.Invertible
