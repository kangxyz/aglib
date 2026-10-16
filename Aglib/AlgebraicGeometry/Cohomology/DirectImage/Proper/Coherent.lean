/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Proper.Finiteness
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Restriction
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Restriction

/-!
# Coherent proper higher images over a locally Noetherian base

The affine-base proper finiteness theorem descends directly along actual
affine opens of the target. The original open-restriction comparison
identifies each restricted higher image with the higher image of the
original restricted coefficient. This requires neither a quasi-compact
target nor a relative-flatness condition on the coherent coefficient.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- All original higher direct images of a coherent coefficient under a proper
morphism are coherent over every locally Noetherian target. -/
theorem moduleHigherDirectImage_coherent_of_proper
    {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] (M : X.Modules)
    (hM : affineLocallyFiniteType X M) (q : ℕ) :
    affineLocallyFiniteType Y (((pushforward f).rightDerived q).obj M) := by
  intro A j _
  let : IsLocallyNoetherian (Spec A) := isLocallyNoetherian_of_isOpenImmersion j
  let : IsNoetherianRing A := isLocallyNoetherian_Spec.mp inferInstance
  let a := pullback.fst f j
  let b := pullback.snd f j
  let h := IsPullback.of_hasPullback f j
  let N := M.restrict a
  have hN : affineLocallyFiniteType (CategoryTheory.Limits.pullback f j) N :=
    affineLocallyFiniteType_restrict a hM
  have hcoh := Scheme.Cohomology.proper_higherDirectImage_coherent A b N hN q
  exact (affineFiniteSheaf A).prop_of_iso
    ((higherDirectImageOpenRestrictionIso a b f j h q).app M).symm
    ((affineLocallyFiniteType_spec_iff A _).mp hcoh)

end AlgebraicGeometry.Scheme.Modules
