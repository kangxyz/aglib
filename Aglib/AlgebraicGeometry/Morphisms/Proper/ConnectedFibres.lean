/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.Connected.Clopen

/-!
# Connectedness from actual global-section idempotents

A nontrivial clopen decomposition gives a product decomposition of actual
structural sections. Its characteristic idempotent excludes such a decomposition
when every global idempotent is zero or one. The proper fibre-image theorem and
the passage to geometric connectedness are separate obligations.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme

universe u

/-- Trivial idempotents in the actual structural section ring give connectedness. -/
theorem connectedSpace_of_globalSections_idempotents (X : Scheme.{u}) [Nonempty X]
    (h : ∀ e : Γ(X, ⊤), IsIdempotentElem e → e = 0 ∨ e = 1) :
    ConnectedSpace X := by
  classical
  apply connectedSpace_iff_clopen.mpr
  refine ⟨inferInstance, ?_⟩
  intro S hS
  by_cases hS0 : S = ∅
  · exact Or.inl hS0
  by_cases hS1 : S = Set.univ
  · exact Or.inr hS1
  let U : X.Opens := ⟨S, hS.2⟩
  let V : X.Opens := ⟨Sᶜ, hS.1.isOpen_compl⟩
  have hdisj : U ⊓ V = ⊥ := by
    ext x
    simp [U, V]
  have hcover : U ⊔ V = ⊤ := by
    ext x
    simp [U, V]
  let : Nonempty U := by
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hS0
    exact ⟨⟨x, hx⟩⟩
  let : Nonempty V := by
    obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem S).mp hS1
    exact ⟨⟨x, hx⟩⟩
  let : Nontrivial Γ(X, U) := Scheme.component_nontrivial _ _
  let : Nontrivial Γ(X, V) := Scheme.component_nontrivial _ _
  let iso : Γ(X, U ⊔ V) ≅ CommRingCat.of (Γ(X, U) × Γ(X, V)) :=
    (X.sheaf.isProductOfDisjoint U V hdisj).conePointUniqueUpToIso
      (CommRingCat.prodFanIsLimit _ _)
  let e : Γ(X, ⊤) ≃+* (Γ(X, U) × Γ(X, V)) :=
    ((X.presheaf.mapIso (eqToIso hcover).op) ≪≫ iso).commRingCatIsoToRingEquiv
  have hid : IsIdempotentElem ((1, 0) : Γ(X, U) × Γ(X, V)) := by
    rw [IsIdempotentElem]
    ext <;> simp
  rcases h (e.symm (1, 0)) (hid.map e.symm) with he | he
  · have h10 : (1 : Γ(X, U)) = 0 := by
      simpa using congrArg (fun a => (e a).1) he
    exact (one_ne_zero h10).elim
  · have h01 : (0 : Γ(X, V)) = 1 := by
      simpa using congrArg (fun a => (e a).2) he
    exact (zero_ne_one h01).elim

end AlgebraicGeometry.Scheme
