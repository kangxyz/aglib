/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.FlatteningStratification.StratumFlatness

/-! Focused consumer of the universal property of one affine stratum `S_f` in terms of flatness
and of its independence from the bound (Nitsure, arXiv:math/0504590v1, Thm 4.3 (ii)), with axiom
guards. -/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace

universe u

/-- Each affine stratum is independent of the bound of the fibre statements of (B) and (C). -/
example {A : Type u} [CommRing A] [IsNoetherianRing A] {ι : Type u} (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (F : (ProjectiveSpace A ι).Modules)
    (hF : Scheme.Modules.QuasiCoherent.affineLocallyFiniteType (ProjectiveSpace A ι) F) {N N' : ℕ}
    (hN : Scheme.Cohomology.IsFiberBaseChangeBound F N)
    (hN' : Scheme.Cohomology.IsFiberBaseChangeBound F N') (f : Polynomial ℚ)
    (hf : f ∈ Set.range (Scheme.Cohomology.fiberHilbertPolynomial F)) :
    ∃ φ : Scheme.Cohomology.hilbertPolynomialStratum n e F hF N f ≅
        Scheme.Cohomology.hilbertPolynomialStratum n e F hF N' f,
      φ.hom ≫ Scheme.Cohomology.hilbertPolynomialStratumι n e F hF N' f =
        Scheme.Cohomology.hilbertPolynomialStratumι n e F hF N f :=
  Scheme.Cohomology.exists_iso_hilbertPolynomialStratum n e F hF hN hN' f hf


/--
info: 'AlgebraicGeometry.Scheme.Cohomology.exists_lift_hilbertPolynomialStratumι_iff_relativeFlat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.exists_lift_hilbertPolynomialStratumι_iff_relativeFlat

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.exists_iso_hilbertPolynomialStratum' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.exists_iso_hilbertPolynomialStratum
