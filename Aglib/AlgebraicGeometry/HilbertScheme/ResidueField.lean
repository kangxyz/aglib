/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.HilbertScheme.Affine
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.QuotientModule
public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# The fiber condition of the Hilbert functor at residue fields

`IsHilbertFamily ι Φ g Z` asks the fiber of `Z` at every field point `x : Spec K ⟶ T` to have
Hilbert polynomial `Φ`. This file proves that it suffices to ask it at the residue fields
`κ(t)` of the points `t ∈ T` (`isHilbertFamily_iff_residueField`), the form of Nitsure,
*Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, §1, pp. 3–4. Every field point
factors as `Spec K ⟶ Spec κ(t) ⟶ T` (Mathlib's `SpecToEquivOfField`), and Hilbert polynomials
of closed subschemes are invariant under field extension:

* `subschemeHilbertPolynomial_comap_map`: for a closed subscheme `W ⊆ P^n_k` and a field map
  `ψ : k →+* K`, `W_K` and `W` have the same Hilbert polynomial: the pullback of `𝒪_W` is `𝒪_{W_K}`
  (`quotientModulePullbackIso`) and Hilbert functions are invariant under field extension
  (`projectiveHilbertFunction_pullback_map`).
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open scoped Polynomial

universe u

namespace AlgebraicGeometry

namespace ProjectiveSpace

open Scheme.Cohomology

variable (ι : Type u)

section FieldBaseChange

variable {k K : Type u} [Field k] [Field K]

/-- **Hilbert polynomials of closed subschemes are invariant under field extension**: for finitely
many coordinates, `W ⊆ P^n_k` and its base change `W_K ⊆ P^n_K` along a field map `ψ : k →+* K`
have the same Hilbert polynomial. -/
theorem subschemeHilbertPolynomial_comap_map [Finite ι] (ψ : k →+* K)
    (W : (ProjectiveSpace k ι).IdealSheafData) :
    subschemeHilbertPolynomial ι K (W.comap (map ψ ι)) = subschemeHilbertPolynomial ι k W := by
  have hW := W.affineLocallyFiniteType_quotientModule
  have : W.quotientModule.IsQuasicoherent :=
    quasicoherent_of_affineCharts _ (fun R j _ => (hW R j).1)
  unfold subschemeHilbertPolynomial projectiveHilbertPolynomial
  rw [← projectiveHilbertFunction_congr K ι (W.quotientModulePullbackIso (map ψ ι)),
    projectiveHilbertFunction_pullback_map ι ψ]

end FieldBaseChange

variable {A : Type u} [CommRing A]

/-- **The fiber condition at residue fields** (Nitsure, arXiv:math/0504590v1, §1, pp. 3–4): for
finitely many coordinates, `Z` is a point of `Hilb^Φ(T)` if and only if it is flat over `T` and its
fiber `Z_t ⊆ P^n_{κ(t)}` at every point `t ∈ T` has Hilbert polynomial `Φ`. -/
theorem isHilbertFamily_iff_residueField [Finite ι] {Φ : ℚ[X]} {T : Scheme.{u}}
    {g : T ⟶ Spec (CommRingCat.of A)} (Z : (pullback (toSpec A ι) g).IdealSheafData) :
    IsHilbertFamily ι Φ g Z ↔ Flat (Z.subschemeι ≫ pullback.snd (toSpec A ι) g) ∧
      ∀ t : T, subschemeHilbertPolynomial ι (T.residueField t)
        (Z.comap (pointMap ι g (T.fromSpecResidueField t))) = Φ := by
  constructor
  · intro hZ
    exact ⟨hZ.flat, fun t => hZ.subschemeHilbertPolynomial_fiber _ (T.fromSpecResidueField t)⟩
  · rintro ⟨hflat, hfib⟩
    refine ⟨hflat, fun K _ x => ?_⟩
    obtain ⟨⟨t, ψ⟩, hx⟩ : ∃ y, (Scheme.SpecToEquivOfField K T).symm y = x :=
      ⟨_, (Scheme.SpecToEquivOfField K T).symm_apply_apply x⟩
    rw [← hx, Scheme.SpecToEquivOfField_symm_apply, ← CommRingCat.ofHom_hom ψ,
      ← map_comp_pointMap, Scheme.IdealSheafData.comap_comp,
      subschemeHilbertPolynomial_comap_map]
    exact hfib t

end ProjectiveSpace

end AlgebraicGeometry
