/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Excellent.J2Criterion
public import Aglib.RingTheory.Nagata.CompleteLocalSurface
public import Mathlib.Topology.NoetherianSpace

/-!
# Finite singular support on actual finite-type normal surface charts

A closed set of closed points in a Noetherian sober space is finite.
Applied to the complement of an open regular locus, this proves finiteness
for a normal surface ring without a semilocality assumption on that ring.
The complete local base supplies J-2 for the actual finite-type chart.
-/

@[expose] public noncomputable section

open Set TopologicalSpace

universe u

namespace TopologicalSpace

/-- A closed set consisting of closed points in a Noetherian sober space is finite. -/
theorem finite_closed_of_closed_points {X : Type*} [TopologicalSpace X]
    [QuasiSober X] [NoetherianSpace X] {Z : Set X} (hZ : IsClosed Z)
    (hpoint : ∀ x ∈ Z, IsClosed ({x} : Set X)) : Z.Finite := by
  obtain ⟨S, hS, hclosed, hirred, hcover⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  rw [hcover]
  apply hS.sUnion
  intro t ht
  let x := (hirred t ht).genericPoint
  have hx : IsGenericPoint x t := (hirred t ht).isGenericPoint_genericPoint (hclosed t ht)
  have hxZ : x ∈ Z := by
    rw [hcover]
    exact mem_sUnion_of_mem hx.mem ht
  rw [← hx.def, (hpoint x hxZ).closure_eq]
  exact finite_singleton x

end TopologicalSpace

namespace PrimeSpectrum

/-- On a normal Noetherian surface ring, an open regular locus has finite
complement. The ring itself need not be semilocal. -/
theorem finite_compl_regularLocus_of_isOpen
    (B : Type u) [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [IsIntegrallyClosed B] (hdim : ringKrullDim B ≤ 2)
    (hopen : IsOpen (regularLocus B)) : (regularLocus B)ᶜ.Finite := by
  apply TopologicalSpace.finite_closed_of_closed_points hopen.isClosed_compl
  intro p hp
  apply (isClosed_singleton_iff_isMaximal p).mpr
  by_contra hn
  exact hp (mem_regularLocus_of_not_isMaximal hdim p hn)

/-- The actual J-2 base makes the singular set of each finite-type normal
surface algebra finite, without requiring that algebra to be semilocal. -/
theorem finite_compl_regularLocus_of_finiteType_of_isJ2Ring
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FiniteType A B] [IsDomain B] [IsIntegrallyClosed B]
    (hA : IsJ2Ring.{u, 0} A) (hdim : ringKrullDim B ≤ 2) :
    (regularLocus B)ᶜ.Finite := by
  let : IsNoetherianRing A := hA.1
  let : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  exact finite_compl_regularLocus_of_isOpen B hdim (hA.2 B)

/-- A complete Noetherian local base of dimension at most two supplies the
full J-2 hypothesis used by every actual finite-type normal surface chart. -/
theorem finite_compl_regularLocus_of_finiteType_complete_local
    (A B : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    [IsDomain B] [IsIntegrallyClosed B]
    (hdA : ringKrullDim A ≤ 2) (hdB : ringKrullDim B ≤ 2) :
    (regularLocus B)ᶜ.Finite := by
  let : Ring.KrullDimLE 2 A := Ring.krullDimLE_iff.mpr hdA
  have hN : IsNagataRing.{u, 0} A := IsNagataRing.of_complete_local_dimLE_two A
  have hJ : IsJ2Ring.{u, 0} A := hN.isJ2Ring_of_semilocal_dimLE_two A hdA
  exact finite_compl_regularLocus_of_finiteType_of_isJ2Ring A B hJ hdB

end PrimeSpectrum
