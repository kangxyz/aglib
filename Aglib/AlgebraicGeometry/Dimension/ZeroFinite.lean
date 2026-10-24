/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Finite morphisms from zero-dimensional geometry

A quasi-compact locally Noetherian scheme of dimension at most zero has finitely
many points. Applied to the actual ordinary fibres, this makes a finite-type
morphism locally quasi-finite. Properness then gives finiteness.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A quasi-compact locally Noetherian scheme of dimension at most zero has
finitely many points, including when it is empty. -/
theorem Scheme.finite_of_topologicalKrullDim_le_zero (X : Scheme.{u})
    [IsLocallyNoetherian X] [CompactSpace X] (hdim : topologicalKrullDim X ≤ 0) :
    Finite X := by
  let : IsLocallyArtinian X := .of_topologicalKrullDim_le_zero hdim
  let : IsArtinianScheme X := {}
  infer_instance

/-- A finite-type morphism with zero-dimensional ordinary fibres is locally
quasi-finite. No Noetherianity assumption is needed on the target. -/
theorem LocallyQuasiFinite.of_fiber_topologicalKrullDim_le_zero
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f]
    (hdim : ∀ s : S, topologicalKrullDim (f.fiber s) ≤ 0) :
    LocallyQuasiFinite f := by
  apply LocallyQuasiFinite.of_finite_preimage_singleton f
  intro s
  let : IsLocallyNoetherian (f.fiber s) :=
    inferInstanceAs (IsLocallyNoetherian
      (CategoryTheory.Limits.pullback f (S.fromSpecResidueField s)))
  let : Finite (f.fiber s) := (f.fiber s).finite_of_topologicalKrullDim_le_zero (hdim s)
  let : Finite (f ⁻¹' {s}) := (f.fiberHomeo s).finite_iff.mp inferInstance
  exact Set.toFinite _

/-- A proper morphism with zero-dimensional ordinary fibres is finite. -/
theorem IsFinite.of_isProper_of_fiber_topologicalKrullDim_le_zero
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (hdim : ∀ s : S, topologicalKrullDim (f.fiber s) ≤ 0) : IsFinite f := by
  let : LocallyQuasiFinite f := .of_fiber_topologicalKrullDim_le_zero f hdim
  exact .of_isProper_of_locallyQuasiFinite f

/-- A proper zero-dimensional scheme over a field is finite over that field. -/
theorem IsFinite.of_isProper_of_topologicalKrullDim_le_zero
    {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProper p]
    (hdim : topologicalKrullDim X ≤ 0) : IsFinite p := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : Finite X := X.finite_of_topologicalKrullDim_le_zero hdim
  let : LocallyQuasiFinite p :=
    .of_finite_preimage_singleton p fun _ => Set.toFinite _
  exact .of_isProper_of_locallyQuasiFinite p

end AlgebraicGeometry
