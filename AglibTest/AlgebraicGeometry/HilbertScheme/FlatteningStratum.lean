/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.HilbertScheme.FlatteningStratum

/-! Focused consumer of the flattening strata of the structure module of a closed subscheme of
`P^n_A ×_{Spec A} S` read as points of the Hilbert functor, with axiom guards. -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Cohomology
open scoped Polynomial

universe u

/-- For a locally Noetherian base and test scheme, `g : T ⟶ S` factors through the stratum
`S_Φ` of `𝒪_Z` iff `Z_T` is a point of `Hilb^Φ(T)`; the coherence of `𝒪_Z` is supplied by
`affineLocallyFiniteType_quotientModule`. -/
example {A : Type u} [CommRing A] (ι : Type u) [Finite ι] {S T : Scheme.{u}}
    [IsLocallyNoetherian S] [IsLocallyNoetherian T] (s : S ⟶ Spec (CommRingCat.of A)) (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (Z : (pullback (toSpec A ι) s).IdealSheafData) (Φ : ℚ[X])
    (g : T ⟶ S) :
    (∃ h : T ⟶ flatteningStratum ι s n e Z.affineLocallyFiniteType_quotientModule Φ,
        h ≫ flatteningStratumι ι s n e Z.affineLocallyFiniteType_quotientModule Φ = g) ↔
      IsHilbertFamily ι Φ (g ≫ s) (Z.comap (pullbackBaseChange ι s g)) :=
  exists_lift_flatteningStratumι_iff_isHilbertFamily ι s Z n e _ Φ g

/-- Without Noetherian hypotheses: `Z_T ∈ Hilb^Φ(T)` iff `F_T` is flat with chart fiber
polynomial `Φ` everywhere. -/
example {A : Type u} [CommRing A] (ι : Type u) [Finite ι] {S T : Scheme.{u}}
    (s : S ⟶ Spec (CommRingCat.of A)) (Z : (pullback (toSpec A ι) s).IdealSheafData) (Φ : ℚ[X])
    (g : T ⟶ S) :
    IsHilbertFamily ι Φ (g ≫ s) (Z.comap (pullbackBaseChange ι s g)) ↔
      Scheme.Modules.relativeFlat (pullback.snd (toSpec A ι) (g ≫ s))
          ((Scheme.Modules.pullback (pullbackBaseChange ι s g)).obj Z.quotientModule) ∧
        ∀ t : T, fiberHilbertPolynomialAt ι (g ≫ s)
          ((Scheme.Modules.pullback (pullbackBaseChange ι s g)).obj Z.quotientModule) t = Φ :=
  isHilbertFamily_comap_pullbackBaseChange_iff ι s Z g Φ

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.fiberHilbertPolynomialAt_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.fiberHilbertPolynomialAt_congr

/--
info: 'AlgebraicGeometry.ProjectiveSpace.isHilbertFamily_comap_pullbackBaseChange_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.isHilbertFamily_comap_pullbackBaseChange_iff

/--
info: 'AlgebraicGeometry.ProjectiveSpace.exists_lift_flatteningStratumι_iff_isHilbertFamily' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.exists_lift_flatteningStratumι_iff_isHilbertFamily
