/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Properties.Regular.Basic
public import Aglib.RingTheory.Smooth.GeometricRegularity
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Regular schemes over a perfect field are smooth

The finite-type regular-algebra smoothness criterion applies on each actual
affine chart. Both regularity and the structural morphism remain the original
scheme objects; no smoothness or geometric-regularity premise is added.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- The affine regular-algebra criterion applied to the original scheme map. -/
theorem Smooth.of_regularStalks_of_perfectField
    (K : Type u) [Field K] [PerfectField K] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) [LocallyOfFiniteType p] [IsLocallyNoetherian X]
    (hreg : Scheme.RegularStalks X) : Smooth p := by
  wlog hX : ∃ A, X = Spec A generalizing X p
  · rw [IsZariskiLocalAtSource.iff_of_openCover (P := @Smooth) X.affineCover]
    intro i
    exact this (X.affineCover.f i ≫ p)
      (hreg.of_isOpenImmersion (X.affineCover.f i)) ⟨_, rfl⟩
  obtain ⟨A, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective p
  have hf : φ.hom.FiniteType :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp inferInstance
  algebraize [φ.hom]
  let : IsNoetherianRing A := isLocallyNoetherian_Spec.mp inferInstance
  let : IsRegularRing A := (Scheme.regularStalks_spec_iff A).mp hreg
  apply HasRingHomProperty.Spec_iff.mpr
  apply RingHom.smooth_algebraMap.mpr
  exact Algebra.Smooth.of_isRegularRing_of_perfectField K A

end AlgebraicGeometry
