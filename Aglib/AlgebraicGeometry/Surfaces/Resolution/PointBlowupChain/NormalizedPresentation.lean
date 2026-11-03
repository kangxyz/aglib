/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Resolution.PointBlowupChain.NormalStages
public import Aglib.AlgebraicGeometry.Descent.LocalModification.ChainTransport
public import Aglib.AlgebraicGeometry.FunctionField.Normalization

/-!
# Literal normalized presentation of an ordinary normal-stage chain

The actual ordinary terminal is retained through an explicit isomorphism and
its original structural triangle. Each normalization is the original generic
normalization, proved isomorphic from genuine normality of that ordinary stage.
No equality of the different chosen schemes is asserted.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Blowup.PointBlowupChain

/-- An ordinary chain whose actual post-blowup stages are normal has a literal
normalized-point presentation of exactly the same length. The terminal
isomorphism preserves the original ordinary composite. -/
theorem exists_normalizedPresentation
    {X T : Scheme.{u}} {g : T ⟶ X} (c : PointBlowupChain g)
    (hX : IsIntegral X) (hN : c.NormalStages) :
    ∃ (Z : Scheme.{u}) (f : Z ⟶ X) (d : NormalizedPointBlowupChain f) (E : T ≅ Z),
      d.length = c.length ∧ E.hom ≫ f = g := by
  revert hX hN
  induction c with
  | refl X =>
    intro _ _
    exact ⟨X, 𝟙 X, .refl X, Iso.refl X, rfl, by simp⟩
  | @cons X T x hx hd g tail ih =>
    intro hX hN
    let : IsIntegral X := hX
    have hne : x ≠ genericPoint X := by
      intro h
      subst x
      change ringKrullDim X.functionField = 2 at hd
      rw [ringKrullDim_eq_zero_of_field] at hd
      norm_num at hd
    let B := blowupDatum (X.fromSpecResidueField x).ker
    let hB : IsIntegral B.Y := pointBlowup_isIntegral X x hx hne
    let : IsIntegral B.Y := hB
    have hnormal : NormalStalks B.Y := hN.1
    let (z : B.Y) : IsIntegrallyClosed (B.Y.presheaf.stalk z) := (hnormal z).2
    let N := normalizedPointBlowup X x hx hne
    let : IsIntegral N := normalizedPointBlowup_isIntegral X x hx hne
    let ν : N ⟶ B.Y := (B.Y.fromSpecStalk (genericPoint B.Y)).fromNormalization
    let : IsIso ν := inferInstance
    obtain ⟨V, k, upper, E₀, hlen₀, hE₀⟩ := ih hB hN.2
    obtain ⟨W, l, lower, E₁, hlen₁, hE₁⟩ := upper.transportIso N (asIso ν).symm
    refine ⟨W, l ≫ normalizedPointBlowupMap X x hx hne,
      .cons x hx hne l lower, E₀ ≪≫ E₁, ?_, ?_⟩
    · change lower.length + 1 = tail.length + 1
      rw [hlen₁, hlen₀]
    · change (E₀.hom ≫ E₁.hom) ≫ (l ≫ (ν ≫ B.map)) = g ≫ B.map
      calc
        _ = E₀.hom ≫ (E₁.hom ≫ l) ≫ ν ≫ B.map := by simp only [Category.assoc]
        _ = E₀.hom ≫ (k ≫ inv ν) ≫ ν ≫ B.map := by rw [hE₁]; rfl
        _ = (E₀.hom ≫ k) ≫ B.map := by
          simp only [Category.assoc, IsIso.inv_hom_id_assoc]
        _ = g ≫ B.map := by rw [hE₀]

end AlgebraicGeometry.Scheme.Blowup.PointBlowupChain
