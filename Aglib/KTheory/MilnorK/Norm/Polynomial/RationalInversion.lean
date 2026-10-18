/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.Polynomial.FiniteComparison

/-!
# Rational inversion of the actual polynomial-presentation norm

For a presentation fixed literally by coefficient inversion, singleton
coefficient base change commutes the norm with the actual quotient-field map.
The actual infinity residue therefore reduces to the finite residue at `X`.
No normality, prime-degree, presentation-independence, or norm-tower premise
is used. Constant-coefficient presentations satisfy the fixedness condition.
-/

@[expose] public noncomputable section

namespace MilnorK.PolynomialNorm

open Polynomial Polynomial.LocalResidue PolynomialResidue

variable {k : Type*} [Field k]

/-- Literal constant-coefficient polynomials are fixed by rational inversion. -/
theorem polynomial_map_inversion_map_C (q : k[X]) :
    (q.map (RatFunc.C : k →+* RatFunc k)).map (RatFunc.inversion k).toRingHom =
      q.map (RatFunc.C : k →+* RatFunc k) := by
  rw [Polynomial.map_map]
  congr 1
  ext a
  exact RatFunc.inversion_C k a

variable [CharZero k] (p : MonicIrreducible (RatFunc k))
  (hp : p.val.map (RatFunc.inversion k).toRingHom = p.val)

/-- Coefficient inversion commutes with the actual polynomial norm in every
degree. The upper map is the original quotient map, not an assumed norm law. -/
theorem polynomialNorm_inversion (n : ℕ) (x : K (AdjoinRoot p.val) n) :
    map n (RatFunc.inversion k).toRingHom (polynomialNorm n p x) =
      polynomialNorm n p
        (map n (adjoinRootMap (RatFunc.inversion k).toRingHom p.val p.val
          (by rw [hp])) x) :=
  polynomialNorm_restrict_irreducible (RatFunc.inversion k).toRingHom n p p hp.symm x

/-- The inversion square as equality of the actual integer-linear maps. -/
theorem polynomialNorm_comp_inversion (n : ℕ) :
    (map n (RatFunc.inversion k).toRingHom).comp (polynomialNorm n p) =
      (polynomialNorm n p).comp
        (map n (adjoinRootMap (RatFunc.inversion k).toRingHom p.val p.val
          (by rw [hp]))) := by
  apply LinearMap.ext
  intro x
  exact polynomialNorm_inversion p hp n x

local instance : Fact (Irreducible (X : k[X])) := ⟨irreducible_X⟩

/-- Infinity of the actual rational presentation norm is the finite `X` residue
of the same norm after the literal upper quotient map induced by inversion. -/
theorem infinityResidue_polynomialNorm_eq_residueAt_X
    (n : ℕ) (x : K (AdjoinRoot p.val) (n + 1)) :
    InfinityResidue.residue k n (polynomialNorm (n + 1) p x) =
      map n (InfinityResidue.rootXEquiv k).toRingHom
        (residueAt (X : k[X]) n
          (polynomialNorm (n + 1) p
            (map (n + 1) (adjoinRootMap (RatFunc.inversion k).toRingHom p.val p.val
              (by rw [hp])) x))) := by
  change map n (InfinityResidue.rootXEquiv k).toRingHom
    (residueAt (X : k[X]) n
      (map (n + 1) (RatFunc.inversion k).toRingHom (polynomialNorm (n + 1) p x))) = _
  rw [polynomialNorm_inversion p hp]

end MilnorK.PolynomialNorm
