/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Homology
public import Aglib.AlgebraicGeometry.Modules.Perfect.Local
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Homology
public import Aglib.AlgebraicGeometry.Modules.Support
public import Mathlib.Data.Set.Finite.Lattice

/-! # Quasicoherent homology and bounds for locally perfect complexes

Actual local strict models imply quasicoherent homology and local
cohomological bounds for an arbitrary scheme. A single global cohomological
interval uses CompactSpace X. Neither termwise quasicoherence of the original
complex nor a global strict representative is assumed.

Source: `Quillen/AlgebraicGeometry/PerfectComplexes/Homology.lean`,
archive SHA-256
`16c127c5b7a5874cb4d841e1161b436190c35aeb08802b89cb19fd8c76ad1d48`,
source SHA-256 `bfb93dda9ff5df57674129b0a5255631ac11bebebaab26d50426b51f4fdbaf34`.
The accepted consumer-retargeted input has SHA-256
`5c3aa2c2a65dfad3868fb1cb2e0114e3bf41693497a51c3497640d7e6d0b5d8a`.
Admitted subset: locallyPerfect_quasicoherent_homology,
  locallyPerfect_exists_local_homology_bounds and locallyPerfect_homology_bounded.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules.Complex

attribute [local instance] standardDerived

/-- Every locally perfect complex has quasicoherent cohomology in the
ambient derived category of all module sheaves, with no global strict model
or termwise quasicoherence assumed. -/
theorem locallyPerfect_quasicoherent_homology {X : Scheme.{u}} {K : CochainComplex X.Modules ℤ}
    (hK : locallyPerfect X K) (i : ℤ) : (K.homology i).IsQuasicoherent := by
  apply AlgebraicGeometry.Scheme.Modules.QuasiCoherent.quasicoherent_of_openNeighborhoods
  intro x
  obtain ⟨U, hxU, P, ⟨e⟩⟩ := hK x
  have hP : (P.obj.homology i).IsQuasicoherent :=
    AlgebraicGeometry.Scheme.Modules.QuasiCoherent.quasicoherent_homology P.obj (fun n => by
      let := P.property.2 n
      infer_instance) i
  exact ⟨U, hxU,
    (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso
      ((homologyIsoOfDerivedIso e i).symm ≪≫ restrictHomologyIso U.ι K i) hP⟩


/-- A local strict model gives actual vanishing of homology sheaves outside
its term bounds, on the same neighborhood. -/
theorem locallyPerfect_exists_local_homology_bounds {X : Scheme.{u}}
    {K : CochainComplex X.Modules ℤ}
    (hK : locallyPerfect X K) (x : X) :
    ∃ (U : X.Opens), x ∈ U ∧ ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((Scheme.Modules.restrictFunctor U.ι).obj (K.homology i)) := by
  obtain ⟨U, hxU, P, ⟨e⟩⟩ := hK x
  obtain ⟨⟨a, b, hb⟩, _⟩ := P.property
  refine ⟨U, hxU, a, b, fun i hi => ?_⟩
  have hz : IsZero (P.obj.homology i) :=
    (P.obj.sc i).isZero_homology_of_isZero_X₂ (hb i hi)
  exact hz.of_iso ((restrictHomologyIso U.ι K i).symm ≪≫ homologyIsoOfDerivedIso e i)

/-- On a quasi-compact scheme, the actual cohomology sheaves of every
locally perfect complex vanish outside a single finite interval. The finite
subcover argument does not construct a global strict representative. -/
theorem locallyPerfect_homology_bounded {X : Scheme.{u}} [CompactSpace X]
    {K : CochainComplex X.Modules ℤ} (hK : locallyPerfect X K) :
    ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (K.homology i) := by
  classical
  choose U hx a b hvan using locallyPerfect_exists_local_homology_bounds hK
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X => (U x : Set X)) (fun x => (U x).isOpen)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hx x⟩)
  obtain ⟨A, hA⟩ := (s.finite_toSet.image a).bddBelow
  obtain ⟨B, hB⟩ := (s.finite_toSet.image b).bddAbove
  refine ⟨A, B, fun i hi => ?_⟩
  apply (AlgebraicGeometry.Scheme.Modules.isZero_iff_stalks _).mpr
  intro y
  obtain ⟨x, hxs, hy⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ y))
  have hAx : A ≤ a x := hA ⟨x, hxs, rfl⟩
  have hxB : b x ≤ B := hB ⟨x, hxs, rfl⟩
  have hz := hvan x i (by rcases hi with hi | hi <;> omega)
  have hs := (AlgebraicGeometry.Scheme.Modules.isZero_iff_stalks _).mp hz ⟨y, hy⟩
  exact hs.of_iso ((Scheme.Modules.restrictStalkNatIso (U x).ι ⟨y, hy⟩).app
    (K.homology i)).symm

end AlgebraicGeometry.Scheme.Modules.Complex
