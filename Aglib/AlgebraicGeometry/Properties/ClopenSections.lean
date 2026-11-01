/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Original idempotent sections of clopen scheme opens

The structure sheaf glues the literal sections one and zero on the clopen
partition. No affine, quasi-compact, or Noetherian hypothesis is required.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u

/-- Every clopen open is the basic open of an idempotent of the original
ring of global sections. -/
theorem exists_idempotent_basicOpen_eq (X : Scheme.{u}) (U : X.Opens)
    (hU : IsClosed (U : Set X)) :
    ∃ e : Γ(X, ⊤), IsIdempotentElem e ∧ X.basicOpen e = U := by
  let V : X.Opens := ⟨(U : Set X)ᶜ, hU.isOpen_compl⟩
  have hUV : U ⊓ V = ⊥ := by
    ext x
    exact ⟨fun hx => hx.2 hx.1, False.elim⟩
  have hVU : V ⊓ U = ⊥ := by rw [inf_comm, hUV]
  let O : Bool → X.Opens := fun b => if b then V else U
  let sf : ∀ b : Bool, Γ(X, O b) := fun b => if b then 0 else 1
  have hcover : (⊤ : X.Opens) ≤ iSup O := by
    intro x _
    by_cases hx : x ∈ U
    · exact (le_iSup O false) hx
    · exact (le_iSup O true) hx
  have hcompat : TopCat.Presheaf.IsCompatible X.presheaf O sf := by
    intro i j
    cases i <;> cases j
    · simp only [O, sf, Bool.false_eq_true, ↓reduceIte, map_one]
    · exact @Subsingleton.elim _
        (CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hUV)) _ _
    · exact @Subsingleton.elim _
        (CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hVU)) _ _
    · simp only [O, sf, ↓reduceIte, map_zero]
  obtain ⟨e, he, heuniq⟩ := X.sheaf.existsUnique_gluing' O ⊤
    (fun _ => homOfLE le_top) hcover sf hcompat
  have heU : X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op e = 1 := he false
  have heV : X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op e = 0 := he true
  refine ⟨e, ?_, ?_⟩
  · change e * e = e
    apply heuniq
    intro b
    rw [map_mul, he b]
    cases b with
    | false =>
      change (1 : Γ(X, U)) * 1 = 1
      exact one_mul 1
    | true =>
      change (0 : Γ(X, V)) * 0 = 0
      exact zero_mul 0
  · have hbasicU : U ⊓ X.basicOpen e = U := by
      rw [← X.basicOpen_res e (homOfLE (show U ≤ ⊤ from le_top)).op, heU,
        X.basicOpen_one]
    have hbasicV : V ⊓ X.basicOpen e = ⊥ := by
      rw [← X.basicOpen_res e (homOfLE (show V ≤ ⊤ from le_top)).op, heV,
        X.basicOpen_zero]
    ext x
    constructor
    · intro hx
      by_contra hxU
      have hxV : x ∈ V := hxU
      have hxbot : x ∈ (⊥ : X.Opens) := hbasicV ▸ And.intro hxV hx
      exact hxbot
    · intro hx
      have h : x ∈ U ⊓ X.basicOpen e := hbasicU.symm ▸ hx
      exact h.2

end AlgebraicGeometry.Scheme
