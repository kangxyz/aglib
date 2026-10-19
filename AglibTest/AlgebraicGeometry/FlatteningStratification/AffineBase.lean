/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.FlatteningStratification.AffineBase

/-! Focused consumer of the restriction of a projective family to the affine opens of its base,
of the fibre Hilbert polynomials on the base and of their base-change invariance, with axiom
guards. -/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace

universe u

/-- For quasi-coherent `F`, the fibre Hilbert polynomial at a point of `S` is computed in any
affine open around it, and along `g : T ⟶ S` the fibre Hilbert polynomial of the pullback of `F`
at `t` is that of `F` at `g t`. -/
example {A : Type u} [CommRing A] {ι : Type u} [Finite ι] {S T : Scheme.{u}}
    (s : S ⟶ Spec (CommRingCat.of A)) (F : (pullback (toSpec A ι) s).Modules) [F.IsQuasicoherent]
    (g : T ⟶ S) :
    (∀ (U : S.Opens) (hU : IsAffineOpen U) (y : S) (hy : y ∈ U),
        Scheme.Cohomology.fiberHilbertPolynomialAt ι s F y =
          Scheme.Cohomology.fiberHilbertPolynomial
            (Scheme.Cohomology.affineBaseModule ι s F hU) (hU.primeIdealOf ⟨y, hy⟩)) ∧
      ∀ t : T, Scheme.Cohomology.fiberHilbertPolynomialAt ι (g ≫ s)
          ((Scheme.Modules.pullback (pullbackBaseChange ι s g)).obj F) t =
        Scheme.Cohomology.fiberHilbertPolynomialAt ι s F (g t) :=
  ⟨fun _ hU y hy => Scheme.Cohomology.fiberHilbertPolynomialAt_eq ι s F hU y hy,
    Scheme.Cohomology.fiberHilbertPolynomialAt_pullbackBaseChange ι s F g⟩

/-- Only finitely many fibre Hilbert polynomials occur over a quasi-compact, locally Noetherian
base. -/
example {A : Type u} [CommRing A] {ι : Type u} (n : ℕ) (e : ι ≃ Fin (n + 1)) {S : Scheme.{u}}
    [IsLocallyNoetherian S] [CompactSpace S] (s : S ⟶ Spec (CommRingCat.of A))
    {F : (pullback (toSpec A ι) s).Modules}
    (hF : Scheme.Modules.QuasiCoherent.affineLocallyFiniteType (pullback (toSpec A ι) s) F) :
    (Set.range (Scheme.Cohomology.fiberHilbertPolynomialAt ι s F)).Finite :=
  Scheme.Cohomology.finite_range_fiberHilbertPolynomialAt ι s n e hF


/--
info: 'AlgebraicGeometry.Scheme.Cohomology.relativeFlat_pullback_affineBaseMap_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.relativeFlat_pullback_affineBaseMap_iff

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.relativeFlat_pullbackBaseChange_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.relativeFlat_pullbackBaseChange_iff

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.affineLocallyFiniteType_affineBaseModule' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.affineLocallyFiniteType_affineBaseModule

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.fiberHilbertPolynomial_affineBaseModule_restrict' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.fiberHilbertPolynomial_affineBaseModule_restrict

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.fiberHilbertPolynomialAt_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.fiberHilbertPolynomialAt_eq

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.fiberHilbertPolynomialAt_fromSpec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.fiberHilbertPolynomialAt_fromSpec

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.fiberHilbertPolynomialAt_pullbackBaseChange' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.fiberHilbertPolynomialAt_pullbackBaseChange

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.finite_range_fiberHilbertPolynomialAt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.finite_range_fiberHilbertPolynomialAt
