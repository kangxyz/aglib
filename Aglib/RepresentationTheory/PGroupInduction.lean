/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RepresentationTheory.PGroup
public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Short-exact induction for finite prime-field p-group representations

The induction uses the native invariant subrepresentation and quotient, with
the actual inclusion and quotient maps. It requires neither semisimplicity nor
a separately chosen filtration.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe g v

namespace Rep

variable {k : Type*} [Field k] {G : Type g} [Group G]

/-- The original inclusion and quotient form a short complex of representations. -/
def subrepresentationShortComplex (A : Rep.{v} k G) (W : Submodule k A)
    (hW : ∀ g, W ≤ W.comap (A.ρ g)) : ShortComplex (Rep.{v} k G) :=
  ShortComplex.mk (A.subtype W hW) (A.mkQ W hW) (by
    ext x
    exact Submodule.Quotient.mk_eq_zero W |>.mpr x.property)

/-- Exactness retains the native representation maps and is reflected from modules. -/
theorem subrepresentationShortComplex_shortExact (A : Rep.{v} k G)
    (W : Submodule k A) (hW : ∀ g, W ≤ W.comap (A.ρ g)) :
    (subrepresentationShortComplex A W hW).ShortExact := by
  let S := subrepresentationShortComplex A W hW
  have hmono : Mono S.f := (mono_iff_injective S.f).2 W.subtype_injective
  have hepi : Epi S.g := (epi_iff_surjective S.g).2 W.mkQ_surjective
  refine { exact := ?_, mono_f := hmono, epi_g := hepi }
  apply (S.exact_map_iff_of_faithful (forget₂ (Rep.{v} k G) (ModuleCat.{v} k))).mp
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  have hxW : x ∈ W := (Submodule.Quotient.mk_eq_zero W).mp hx
  exact ⟨⟨x, hxW⟩, rfl⟩

variable (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G)

include hG in
/-- A property closed under actual short exact extensions follows from zero
representations and trivial lines for every finite-dimensional p-group representation. -/
theorem induction_of_isPGroup
    (P : Rep.{v} (ZMod p) G → Prop)
    (hzero : ∀ A : Rep.{v} (ZMod p) G, Subsingleton A → P A)
    (hline : ∀ A : Rep.{v} (ZMod p) G,
      Module.finrank (ZMod p) A = 1 → A.IsTrivial → P A)
    (hext : ∀ S : ShortComplex (Rep.{v} (ZMod p) G),
      S.ShortExact → P S.X₁ → P S.X₃ → P S.X₂)
    (A : Rep.{v} (ZMod p) G) [FiniteDimensional (ZMod p) A] : P A := by
  suffices h : ∀ n : ℕ, ∀ B : Rep.{v} (ZMod p) G,
      ∀ [FiniteDimensional (ZMod p) B], Module.finrank (ZMod p) B = n → P B from
    h _ A rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro B _ hdim
    rcases subsingleton_or_nontrivial B with hB | hB
    · exact hzero B hB
    · let := hB
      obtain ⟨W, hWdim, hWtriv, hdrop⟩ :=
        Representation.exists_trivial_line_of_isPGroup p B.ρ hG
      let hw : ∀ g, W.toSubmodule ≤ W.toSubmodule.comap (B.ρ g) :=
        fun g x hx => W.apply_mem_toSubmodule g hx
      let S := subrepresentationShortComplex B W.toSubmodule hw
      apply hext S (subrepresentationShortComplex_shortExact B W.toSubmodule hw)
      · apply hline _ hWdim
        exact hWtriv
      · let : FiniteDimensional (ZMod p) S.X₃ :=
          inferInstanceAs (FiniteDimensional (ZMod p) (B ⧸ W.toSubmodule))
        apply ih (Module.finrank (ZMod p) (B ⧸ W.toSubmodule))
          (by simpa only [hdim] using hdrop) S.X₃
        rfl

end Rep
