/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Ample.Proper
public import Aglib.AlgebraicGeometry.Modules.Invertible.LocalRing
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.RingTheory.PrincipalIdealDomain

/-! Properness and ampleness of a pulled-back line bundle force finiteness. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible

private theorem isAffineHom_fromSpec_field {K : Type u} [Field K] {Y : Scheme.{u}}
    (b : Spec (.of K) ⟶ Y) : IsAffineHom b := by
  constructor
  intro U _
  let V := b ⁻¹ᵁ U
  by_cases hx : IsLocalRing.closedPoint K ∈ V
  · have hV : V = ⊤ := (IsLocalRing.closedPoint_mem_iff V).mp hx
    change IsAffineOpen V
    rw [hV]
    exact isAffineOpen_top _
  · have hV : V = ⊥ := by
      ext x
      have he : x = IsLocalRing.closedPoint K := Subsingleton.elim _ _
      rw [he]
      exact iff_false_intro hx
    change IsAffineOpen V
    rw [hV]
    exact isAffineOpen_bot _

/-- If the pullback of an original line bundle along a proper morphism is
ample, the morphism is finite. On each original residue-field fibre that
same pullback is trivial and ample; properness gives a finite fibre. -/
theorem LineBundle.isFinite_of_isProper_of_isAmple_pullback {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f] (L : LineBundle Y) (hL : (pullbackLineBundle f L).IsAmple) :
    IsFinite f := by
  let : LocallyQuasiFinite f := locallyQuasiFinite_iff_isFinite_fiber.mpr (fun y => by
    let b := Y.fromSpecResidueField y
    let j := f.fiberι y
    let p := f.fiberToSpecResidueField y
    let : IsAffineHom b := isAffineHom_fromSpec_field b
    let : IsAffineHom j := MorphismProperty.of_isPullback
      (IsPullback.of_hasPullback f b).flip (show IsAffineHom b by infer_instance)
    have hp : IsProper p := MorphismProperty.of_isPullback
      (IsPullback.of_hasPullback f b) (show IsProper f by infer_instance)
    let M := pullbackLineBundle j (pullbackLineBundle f L)
    have hM : M.IsAmple := hL.pullback_of_isAffineHom j
    have hz : pullbackClass b (classOf Y L) = 0 := Subsingleton.elim _ _
    have hzero : classOf (f.fiber y) M = 0 := by
      change pullbackClass j (pullbackClass f (classOf Y L)) = 0
      rw [← pullbackClass_comp, f.fiber_fac y, pullbackClass_comp]
      exact (congrArg (pullbackClass p) hz).trans (pullbackClass_zero p)
    have hP := (Field.toIsField (Y.residueField y)).isPrincipalIdealRing
    have hN := @PrincipalIdealRing.isNoetherianRing (Y.residueField y) _ hP
    exact @LineBundle.IsAmple.isFinite_of_isProper_of_classOf_eq_zero
      (Y.residueField y) _ hN _ p hp M hM hzero)
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

end AlgebraicGeometry.Scheme.Modules.Invertible
