/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.FlatteningStratification.FlatDecomposition

/-! Focused consumer of the decomposition of the base of a flat family into the open and closed
loci of its fibre Hilbert polynomials, over a finite set of polynomials, with axiom guards. -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Cohomology AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open scoped Polynomial

universe u

/-- The fibre polynomial of a flat family is locally constant. -/
example {A : Type u} [CommRing A] (ι : Type u) {S : Scheme.{u}} [IsLocallyNoetherian S]
    (s : S ⟶ Spec (CommRingCat.of A)) (n : ℕ) (e : ι ≃ Fin (n + 1))
    {F : (pullback (toSpec A ι) s).Modules}
    (hF : affineLocallyFiniteType (pullback (toSpec A ι) s) F)
    (hflat : relativeFlat (pullback.snd (toSpec A ι) s) F) :
    IsLocallyConstant (fiberHilbertPolynomialAt ι s F) :=
  isLocallyConstant_fiberHilbertPolynomialAt_of_relativeFlat ι s n e hF hflat

/-- The locus where the fibre polynomial of a flat family is `f` is open and closed. -/
example {A : Type u} [CommRing A] (ι : Type u) {S : Scheme.{u}} [IsLocallyNoetherian S]
    (s : S ⟶ Spec (CommRingCat.of A)) (n : ℕ) (e : ι ≃ Fin (n + 1))
    {F : (pullback (toSpec A ι) s).Modules}
    (hF : affineLocallyFiniteType (pullback (toSpec A ι) s) F)
    (hflat : relativeFlat (pullback.snd (toSpec A ι) s) F) (f : ℚ[X]) :
    IsClopen {y | fiberHilbertPolynomialAt ι s F y = f} :=
  isClopen_setOf_fiberHilbertPolynomialAt_eq_of_relativeFlat ι s n e hF hflat f

/-- For a finite set of polynomials containing every fibre polynomial, the strata decompose the
base. -/
example {A : Type u} [CommRing A] (ι : Type u) {S : Scheme.{u}} [IsLocallyNoetherian S]
    (s : S ⟶ Spec (CommRingCat.of A)) (n : ℕ) (e : ι ≃ Fin (n + 1))
    {F : (pullback (toSpec A ι) s).Modules}
    (hF : affineLocallyFiniteType (pullback (toSpec A ι) s) F)
    (hflat : relativeFlat (pullback.snd (toSpec A ι) s) F) (P : Finset ℚ[X])
    (hP : ∀ y, fiberHilbertPolynomialAt ι s F y ∈ P) :
    IsIso (Sigma.desc fun f : P => flatteningStratumι ι s n e hF f) :=
  isIso_sigmaDesc_flatteningStratumι_of_relativeFlat ι s n e hF hflat (fun f : P => (f : ℚ[X]))
    Subtype.val_injective fun y => ⟨⟨_, hP y⟩, rfl⟩

/-- The strata over a finite set of polynomials containing every fibre polynomial cover the base,
flat or not. -/
example {A : Type u} [CommRing A] (ι : Type u) {S : Scheme.{u}} [IsLocallyNoetherian S]
    (s : S ⟶ Spec (CommRingCat.of A)) (n : ℕ) (e : ι ≃ Fin (n + 1))
    {F : (pullback (toSpec A ι) s).Modules}
    (hF : affineLocallyFiniteType (pullback (toSpec A ι) s) F) (P : Finset ℚ[X])
    (hP : ∀ y, fiberHilbertPolynomialAt ι s F y ∈ P) (y : S) :
    ∃ (f : P) (z : flatteningStratum ι s n e hF f), flatteningStratumι ι s n e hF f z = y :=
  exists_flatteningStratumι_apply_eq ι s n e hF (fun f : P => (f : ℚ[X]))
    (fun y => ⟨⟨_, hP y⟩, rfl⟩) y

/-- Morphisms out of the base are determined by their restrictions to the strata. -/
example {A : Type u} [CommRing A] (ι : Type u) {S : Scheme.{u}} [IsLocallyNoetherian S]
    (s : S ⟶ Spec (CommRingCat.of A)) (n : ℕ) (e : ι ≃ Fin (n + 1))
    {F : (pullback (toSpec A ι) s).Modules}
    (hF : affineLocallyFiniteType (pullback (toSpec A ι) s) F)
    (hflat : relativeFlat (pullback.snd (toSpec A ι) s) F) (P : Finset ℚ[X])
    (hP : ∀ y, fiberHilbertPolynomialAt ι s F y ∈ P) {Y : Scheme.{u}} (a b : S ⟶ Y)
    (h : ∀ f : P, flatteningStratumι ι s n e hF f ≫ a = flatteningStratumι ι s n e hF f ≫ b) :
    a = b :=
  hom_ext_of_flatteningStratumι_of_relativeFlat ι s n e hF hflat (fun f : P => (f : ℚ[X]))
    Subtype.val_injective (fun y => ⟨⟨_, hP y⟩, rfl⟩) h

/-- A morphism out of the base is glued from morphisms out of the strata. -/
example {A : Type u} [CommRing A] (ι : Type u) {S : Scheme.{u}} [IsLocallyNoetherian S]
    (s : S ⟶ Spec (CommRingCat.of A)) (n : ℕ) (e : ι ≃ Fin (n + 1))
    {F : (pullback (toSpec A ι) s).Modules}
    (hF : affineLocallyFiniteType (pullback (toSpec A ι) s) F)
    (hflat : relativeFlat (pullback.snd (toSpec A ι) s) F) (P : Finset ℚ[X]) {Y : Scheme.{u}}
    (hP' : ∀ y, fiberHilbertPolynomialAt ι s F y ∈ Set.range fun f : P => (f : ℚ[X]))
    (a : ∀ f : P, flatteningStratum ι s n e hF f ⟶ Y) (f : P) :
    flatteningStratumι ι s n e hF f ≫
        (flatteningDecompositionIso ι s n e hF hflat (fun f : P => (f : ℚ[X]))
          Subtype.val_injective hP').inv ≫ Sigma.desc a = a f := by
  rw [flatteningStratumι_flatteningDecompositionIso_inv_assoc, Sigma.ι_comp_desc]

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.isLocallyConstant_fiberHilbertPolynomialAt_of_relativeFlat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.isLocallyConstant_fiberHilbertPolynomialAt_of_relativeFlat

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.isIso_sigmaDesc_flatteningStratumι_of_relativeFlat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.isIso_sigmaDesc_flatteningStratumι_of_relativeFlat

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.isClopen_setOf_fiberHilbertPolynomialAt_eq_of_relativeFlat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.isClopen_setOf_fiberHilbertPolynomialAt_eq_of_relativeFlat
