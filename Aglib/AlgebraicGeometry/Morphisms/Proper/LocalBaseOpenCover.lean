/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.ResidueFiber
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Open neighborhoods of the closed fibre over a local base

An open containing the actual closed fibre of a universally closed scheme
over a local ring is the entire scheme. Thus good neighborhoods of closed-fibre
points already cover the scheme, with no finite-subcover assumption. This
applies to proper schemes without flatness or nonemptiness hypotheses.
-/

@[expose] public noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.LocalRing

universe u v
variable {R : Type u} [CommRing R] [IsLocalRing R]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [UniversallyClosed f]

/-- An open containing the literal residue-field pullback is all of a
universally closed scheme over a local base. -/
theorem open_eq_top_of_closedFiber_subset (U : X.Opens)
    (hU : Set.range (ResidueFiber.projection f) ⊆ U) : U = ⊤ := by
  apply top_le_iff.mp
  intro x _
  by_contra hx
  have hc : IsClosed (f '' (U : Set X)ᶜ) := f.isClosedMap _ U.isOpen.isClosed_compl
  have hm : IsLocalRing.closedPoint R ∈ f '' (U : Set X)ᶜ :=
    (IsLocalRing.specializes_closedPoint (f x)).mem_closed hc ⟨x, hx, rfl⟩
  obtain ⟨z, hz, hzm⟩ := hm
  apply hz
  apply hU
  rw [ResidueFiber.projection, Scheme.Pullback.range_fst]
  refine ⟨IsLocalRing.closedPoint (IsLocalRing.ResidueField R), ?_⟩
  exact (IsLocalRing.comap_closedPoint (IsLocalRing.residue R)).trans hzm.symm

/-- Any family of opens covering the closed fibre already covers the whole
universally closed model. The index set need not be finite. -/
theorem iSup_eq_top_of_closedFiber_subset {ι : Type v} (U : ι → X.Opens)
    (hU : ∀ x ∈ Set.range (ResidueFiber.projection f), ∃ i, x ∈ U i) :
    iSup U = ⊤ := by
  apply open_eq_top_of_closedFiber_subset f
  intro x hx
  obtain ⟨i, hi⟩ := hU x hx
  exact (le_iSup U i) hi

/-- A family of good opens which contains a neighborhood of every actual
closed-fibre point contains a neighborhood of every point of the model. -/
theorem exists_goodOpen_of_closedFiber {P : X.Opens → Prop}
    (hP : ∀ x ∈ Set.range (ResidueFiber.projection f), ∃ U, P U ∧ x ∈ U)
    (x : X) : ∃ U, P U ∧ x ∈ U := by
  have hcover : (⨆ U : {U : X.Opens // P U}, U.val) = ⊤ := by
    apply iSup_eq_top_of_closedFiber_subset f
    intro y hy
    obtain ⟨U, hU, hyU⟩ := hP y hy
    exact ⟨⟨U, hU⟩, hyU⟩
  have hx : x ∈ ⨆ U : {U : X.Opens // P U}, U.val := by rw [hcover]; trivial
  obtain ⟨U, hxU⟩ := Opens.mem_iSup.mp hx
  exact ⟨U.val, U.property, hxU⟩

end AlgebraicGeometry.Scheme.LocalRing
