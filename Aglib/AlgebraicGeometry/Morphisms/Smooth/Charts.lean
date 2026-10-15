/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.RingHom.StandardSmooth

/-! Affine polynomial coordinates and the global dimension bridge for schemes. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

universe u

/-- Scheme dimension is the supremum of the dimensions of its actual local
rings. No Noetherian or quasi-compact hypothesis is used. -/
theorem topologicalKrullDim_eq_iSup_stalk (X : Scheme.{u}) :
    topologicalKrullDim X = ⨆ x : X, ringKrullDim (X.presheaf.stalk x) := by
  simp only [ringKrullDim_stalk_eq_coheight]
  rw [topologicalKrullDim,
    Order.krullDim_eq_of_orderIso
      (irreducibleSetEquivPoints (α := X)),
    Order.krullDim_eq_iSup_coheight]

/-- A smooth scheme over a field admits affine etale polynomial coordinates
near each point, without a uniform relative dimension hypothesis. -/
theorem exists_etale_polynomial_chart_of_smooth
    (K : Type u) [Field K] (X : Scheme.{u}) (f : X ⟶ Spec (.of K))
    [Smooth f] (x : X) :
    ∃ (V : X.Opens), IsAffineOpen V ∧ x ∈ V ∧
      ∃ (n : ℕ) (g : MvPolynomial (Fin n) K →+* Γ(X, V)), g.Etale := by
  obtain ⟨U, hU, V, hV, hx, e, hf⟩ := Smooth.exists_isStandardSmooth f x
  have hUt : U = ⊤ := by
    apply top_unique
    intro z hz
    have hz' : z = f x := Subsingleton.elim _ _
    exact hz' ▸ e hx
  subst U
  let φ := ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appLE ⊤ V e).hom
  have hφ : φ.IsStandardSmooth := by
    dsimp only [φ]
    rw [CommRingCat.hom_comp, RingHom.isStandardSmooth_respectsIso.cancel_left_isIso]
    exact hf
  obtain ⟨n, g, _, hg⟩ := hφ.exists_etale_mvPolynomial
  exact ⟨V, hV, hx, n, g, hg⟩

/-- With displayed relative dimension n, the same affine coordinate map has
exactly n variables. The source open over the field is the whole spectrum. -/
theorem exists_etale_polynomial_chart_of_smoothOfRelativeDimension
    (K : Type u) [Field K] (X : Scheme.{u}) (f : X ⟶ Spec (.of K)) (n : ℕ)
    [SmoothOfRelativeDimension n f] (x : X) :
    ∃ (V : X.Opens), IsAffineOpen V ∧ x ∈ V ∧
      ∃ (g : MvPolynomial (Fin n) K →+* Γ(X, V)), g.Etale := by
  obtain ⟨U, hU, V, hV, hx, e, hf⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (f := f) (n := n) x
  have hUt : U = ⊤ := by
    apply top_unique
    intro z hz
    have hz' : z = f x := Subsingleton.elim _ _
    exact hz' ▸ e hx
  subst U
  let φ := ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appLE ⊤ V e).hom
  have hφ : φ.IsStandardSmoothOfRelativeDimension n := by
    dsimp only [φ]
    rw [CommRingCat.hom_comp,
      (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := n)).cancel_left_isIso]
    exact hf
  obtain ⟨g, _, hg⟩ := hφ.exists_etale_mvPolynomial
  exact ⟨V, hV, hx, g, hg⟩

end AlgebraicGeometry.Scheme
