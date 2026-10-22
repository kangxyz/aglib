/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.AdmissibleSequence.Refinement
public import Aglib.AlgebraicGeometry.Blowup.AdmissibleSequence.ProtectedOpen
public import Aglib.AlgebraicGeometry.Morphisms.IsIso.OpenHomExt

/-!
# Local lifting into a modified target

Replay of an actual target sequence gives a source sequence. Its protected open
can be smaller than the inverse image of the target's protected open. Agreement
there follows from the target's actual restricted isomorphism, without any
schematic-density or flatness hypothesis on the original local map.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Blowup.AdmissibleSequence

/-- Lift a local map through an actual target sequence, retaining the comparison
triangle and agreement with the literal original source on its protected open. -/
theorem exists_local_lift
    {X M N O Z : Scheme.{u}} (ci : X ⟶ M) [IsOpenImmersion ci]
    {δ : N ⟶ M} (hδ : AdmissibleSequence ci.opensRange δ)
    (f : O ⟶ M) (V : O.Opens) (g : V.toScheme ⟶ X)
    (hg : g ≫ ci = V.ι ≫ f)
    (ti : X ⟶ N) (hti : ti ≫ δ = ci)
    (ei : N ⟶ Z) (cZ : X ⟶ Z) (hZ : ti ≫ ei = cZ) :
    ∃ (B : Scheme.{u}) (γ : B ⟶ O) (a : B ⟶ N),
      AdmissibleSequence V γ ∧ a ≫ δ = γ ≫ f ∧
      (γ ⁻¹ᵁ V).ι ≫ a ≫ ei = (γ ∣_ V) ≫ g ≫ cZ := by
  have hV : V ≤ f ⁻¹ᵁ ci.opensRange := by
    intro x hx
    refine ⟨g ⟨x, hx⟩, ?_⟩
    change (g ≫ ci) ⟨x, hx⟩ = (V.ι ≫ f) ⟨x, hx⟩
    rw [hg]
  obtain ⟨B, γ, a, hγ, ha⟩ := hδ.exists_domination f
  have hγ' : AdmissibleSequence V γ := hγ.mono hV
  let : IsIso (δ ∣_ ci.opensRange) := hδ.restrict_isIso
  let r := (γ ∣_ V) ≫ g ≫ ci.isoOpensRange.hom
  have hr : r ≫ ci.opensRange.ι = (γ ∣_ V) ≫ g ≫ ci := by
    simp only [r, Category.assoc, ci.isoOpensRange_hom_ι]
  have he : (γ ⁻¹ᵁ V).ι ≫ a = (γ ∣_ V) ≫ g ≫ ti := by
    apply δ.ext_of_isIso_restriction ci.opensRange r
    · calc
        ((γ ⁻¹ᵁ V).ι ≫ a) ≫ δ = (γ ⁻¹ᵁ V).ι ≫ γ ≫ f := by
          rw [Category.assoc, ha]
        _ = (γ ∣_ V) ≫ V.ι ≫ f := by rw [← morphismRestrict_ι_assoc]
        _ = (γ ∣_ V) ≫ g ≫ ci := by rw [← hg]
        _ = r ≫ ci.opensRange.ι := hr.symm
    · calc
        ((γ ∣_ V) ≫ g ≫ ti) ≫ δ = (γ ∣_ V) ≫ g ≫ ci := by
          rw [Category.assoc, Category.assoc, hti]
        _ = r ≫ ci.opensRange.ι := hr.symm
  refine ⟨B, γ, a, hγ', ha, ?_⟩
  rw [← Category.assoc, he, Category.assoc, Category.assoc, hZ]

end AlgebraicGeometry.Scheme.Blowup.AdmissibleSequence
