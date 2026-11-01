/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ResidueField.Constants
public import Mathlib.AlgebraicGeometry.Fiber

/-! # A finite residue specialization in the actual closed fibre

A point outside an open specializes, within its original scheme-theoretic
fibre, to a closed point of that fibre. Its residue extension is finite for
the original residue-constants map. The construction retains the original
fibre homeomorphism and inclusion and does not choose a tensor-fibre model
or an unrelated prime. No separation or perfect-field premise is used.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Hom

universe u

/-- A bad point has a closed specialization in the same actual fibre, still
outside the given open and with finite actual residue extension. -/
theorem exists_closed_fiber_specialization_outside_open
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (s : Y) (x : X) (hx : f x = s) (E : X.Opens) (hE : x ∉ E) :
    ∃ z : f.fiber s, IsClosed ({z} : Set (f.fiber s)) ∧
      x ⤳ f.fiberι s z ∧ f.fiberι s z ∉ E ∧
        (residueConstants (f.fiber s) (f.fiberToSpecResidueField s) z).Finite := by
  let hft : LocallyOfFiniteType (f.fiberToSpecResidueField s) :=
    inferInstanceAs (LocallyOfFiniteType
      (CategoryTheory.Limits.pullback.snd f (Y.fromSpecResidueField s)))
  let : JacobsonSpace (f.fiber s) :=
    LocallyOfFiniteType.jacobsonSpace (f.fiberToSpecResidueField s)
  let z₀ : f.fiber s := (f.fiberHomeo s).symm ⟨x, hx⟩
  have hz₀ : f.fiberι s z₀ = x := f.fiberι_fiberHomeo_symm s ⟨x, hx⟩
  have hnonempty : (closure ({z₀} : Set (f.fiber s))).Nonempty :=
    ⟨z₀, subset_closure (Set.mem_singleton z₀)⟩
  obtain ⟨z, hz, hzclosed⟩ := nonempty_inter_closedPoints hnonempty
    isClosed_closure.isLocallyClosed
  have hspecial : z₀ ⤳ z := specializes_iff_mem_closure.mpr hz
  have himage : x ⤳ f.fiberι s z := by
    have h := hspecial.map (f.fiberι s).continuous
    rwa [hz₀] at h
  have hout : f.fiberι s z ∉ E := fun h => hE (himage.mem_open E.isOpen h)
  refine ⟨z, hzclosed, himage, hout, ?_⟩
  let := residueAlgebra (f.fiber s) (f.fiberToSpecResidueField s) z
  have hfinite := @residue_finite (Y.residueField s) inferInstance (f.fiber s)
    (f.fiberToSpecResidueField s) hft ⟨z, hzclosed⟩
  exact RingHom.finite_algebraMap.mpr hfinite

end AlgebraicGeometry.Scheme.Hom
