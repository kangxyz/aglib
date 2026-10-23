/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Points closed in their literal relative fibres -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.FibrewiseClosed

universe u

variable {T S : Scheme.{u}}

/-- The underlying point is closed in its literal topological fibre over the base. -/
def IsFibrewiseClosed (p : T ⟶ S) (x : T) : Prop :=
  IsClosed ({⟨x, rfl⟩} : Set (p ⁻¹' {p x}))

/-- Fixing an equal base point preserves the literal relative closed-point condition. -/
theorem isFibrewiseClosed_iff_of_eq (p : T ⟶ S) (x : T) (s : S) (h : p x = s) :
    IsFibrewiseClosed p x ↔ IsClosed ({⟨x, h⟩} : Set (p ⁻¹' {s})) := by
  subst s
  rfl

/-- A closed point in the native scheme-theoretic fibre is closed in the literal fibre. -/
theorem isFibrewiseClosed_of_fibre (p : T ⟶ S) (s : S) (z : p.fiber s)
    (hz : IsClosed ({z} : Set (p.fiber s))) :
    IsFibrewiseClosed p (p.fiberι s z) := by
  have hs : p (p.fiberι s z) = s := by
    have h := Set.mem_range_self (f := p.fiberι s) z
    rw [p.range_fiberι s] at h
    exact h
  apply (isFibrewiseClosed_iff_of_eq p _ s hs).mpr
  have h := (p.fiberHomeo s).isClosedMap _ hz
  have he : p.fiberHomeo s z = ⟨p.fiberι s z, hs⟩ :=
    Subtype.ext (p.fiberHomeo_apply s z)
  simpa only [Set.image_singleton, he] using h

/-- A nonempty closed subset of any locally finite type test scheme contains
a point whose image is closed in its fibre over the original base. -/
theorem exists_mem_image_fibrewiseClosed (p : T ⟶ S) [LocallyOfFiniteType p]
    {U : Scheme.{u}} (f : U ⟶ T) [LocallyOfFiniteType f]
    (C : Set U) (hC : IsClosed C) (hne : C.Nonempty) :
    ∃ x ∈ C, IsFibrewiseClosed p (f x) := by
  obtain ⟨x, hx⟩ := hne
  let s := p (f x)
  let V := pullback f (p.fiberι s)
  let a : V ⟶ U := pullback.fst f (p.fiberι s)
  let b : V ⟶ p.fiber s := pullback.snd f (p.fiberι s)
  have : LocallyOfFiniteType b := by dsimp [b]; infer_instance
  have : LocallyOfFiniteType (p.fiberToSpecResidueField s) := by
    dsimp [Scheme.Hom.fiberToSpecResidueField]
    infer_instance
  have : JacobsonSpace V :=
    LocallyOfFiniteType.jacobsonSpace (b ≫ p.fiberToSpecResidueField s)
  have hclosed : IsClosed (a ⁻¹' C) := hC.preimage a.continuous
  have hnonempty : (a ⁻¹' C).Nonempty := by
    obtain ⟨z, hz, _⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := f) (g := p.fiberι s) x (p.asFiber (f x))
      (by exact (p.fiberι_asFiber (f x)).symm)
    have hza : a z = x := hz
    exact ⟨z, by change a z ∈ C; rwa [hza]⟩
  obtain ⟨z, hzC, hzclosed⟩ := nonempty_inter_closedPoints hnonempty hclosed.isLocallyClosed
  have hbclosed : IsClosed ({b z} : Set (p.fiber s)) :=
    b.closePoints_subset_preimage_closedPoints hzclosed
  refine ⟨a z, hzC, ?_⟩
  have hfb := congrArg (fun q : V ⟶ T => q z)
    (pullback.condition (f := f) (g := p.fiberι s))
  change f (a z) = p.fiberι s (b z) at hfb
  rw [hfb]
  exact isFibrewiseClosed_of_fibre p s (b z) hbclosed

/-- An actual algebraically closed field in the original scheme universe at a point. -/
abbrev pointField (x : T) := AlgebraicClosure (T.residueField x)

/-- The actual geometric point given by the algebraic closure of the residue field. -/
def geometricPoint (x : T) : Spec (.of (pointField x)) ⟶ T :=
  Spec.map (CommRingCat.ofHom (algebraMap (T.residueField x) (pointField x))) ≫
    T.fromSpecResidueField x

/-- The original underlying point of the chosen geometric map is exactly the index point. -/
theorem geometricPoint_apply (x : T) (a : Spec (.of (pointField x))) :
    geometricPoint x a = x := by
  exact T.fromSpecResidueField_apply x _

end AlgebraicGeometry.Scheme.EtaleCohomology.FibrewiseClosed
