/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Torus.FiniteCorrespondence.Subscheme
public import Aglib.AlgebraicGeometry.Torus.FiniteCorrespondence.SimplexFaces
public import Aglib.RingTheory.Length.ExactSequence
public import Aglib.RingTheory.Multiplicity.PrincipalEuler.Basic
public import Aglib.RingTheory.Multiplicity.PrincipalEuler.Additivity
public import Aglib.RingTheory.ScalarHomology.Basic
public import Aglib.RingTheory.PrimeFiltration.Basic
public import Aglib.RingTheory.Multiplicity.PrincipalEuler.Filtration
public import Aglib.RingTheory.PrimeFiltration.Primes
public import Aglib.RingTheory.Multiplicity.PrincipalEuler.Support
public import Aglib.RingTheory.PrimeFiltration.Length
public import Aglib.RingTheory.PrimeFiltration.Support
public import Aglib.RingTheory.FiniteLength.Support
public import Aglib.RingTheory.PrimeFiltration.Multiplicity
public import Aglib.RingTheory.Multiplicity.PrincipalEuler.Associativity
public import Aglib.AlgebraicGeometry.Torus.FiniteCorrespondence.FibreSections

/-!
# LowSimplexFaces for finite correspondences on the two-dimensional torus

Native migration from `lean/R5Lab/Aglib/AlgebraicGeometry/Torus/FiniteCorrespondence/`
leaf `LowSimplexFaces.lean` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`55e439fca65bef8823449e397e3cd38c82388a12b659793c6c401bd18f913e5a`.

The Laurent object is `MonoidAlgebra R (Multiplicative (ℤ × ℤ))` in its original
coordinate order. Statements retain their displayed finiteness, normality,
Noetherianity, flatness, regularity and scalar-map hypotheses.
-/

/-!
The source records MVW, final December 2005, Construction 1.3 and composition
(p.6), Example 1A.14 (p.13), Definition 2.14 (p.18), and Definition 3.1;
retained PDF SHA-256
`be064d54ca742787bbff1f98a0c8ac82e30ab73e7a7d32c9e2a1574303594c13`.
The paper-to-code identification of the source face is separate from the
formal affine scheme and local-length equalities proved in this file.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.Torus.FiniteCorrespondence.Fibre
open _root_.Module.CommutingAutomorphisms
open _root_.Module.CommutingAutomorphisms.LaurentSupport
open MonoidAlgebra (FiniteDominantPrime)

open LaurentSupport Subscheme CategoryTheory AlgebraicGeometry
open scoped TensorProduct

universe u
variable {R S : Type u} [CommRing R] [CommRing S]

section LowFaces
variable (K : Type u) [Field K]

/-- j=0 gives Delta^1 -> Delta^0; j=1 gives Delta^2 -> Delta^1.
These are precisely the face pullbacks entering the existing three-term model. -/
def lowFaceGeometricLength (j : Fin 2) (i : Fin (j.val + 2))
    (p : FiniteDominantPrime (AlgebraicSimplex.CoordinateRing K (j.val + 1)))
    (q : FiniteDominantPrime (AlgebraicSimplex.CoordinateRing K j.val)) : ℕ∞ :=
  geometricFibreLength (ofPoint p).val (coefficientMap (AlgebraicSimplex.face K i)) q.val

theorem lowFaceGeometricLength_eq (j : Fin 2) (i : Fin (j.val + 2))
    (p : FiniteDominantPrime (AlgebraicSimplex.CoordinateRing K (j.val + 1)))
    (q : FiniteDominantPrime (AlgebraicSimplex.CoordinateRing K j.val)) :
    let := (AlgebraicSimplex.face K i).toAlgebra
    lowFaceGeometricLength K j i p q = quotientFibreLength p q := by
  let := (AlgebraicSimplex.face K i).toAlgebra
  exact geometricFibreLength_ofPoint p q

/-- Thus the geometric fibre gives honest finite integer multiplicities at
every actual target point; no target point is silently assumed flat. -/
theorem lowFaceGeometricLength_ne_top (j : Fin 2) (i : Fin (j.val + 2))
    (p : FiniteDominantPrime (AlgebraicSimplex.CoordinateRing K (j.val + 1)))
    (q : FiniteDominantPrime (AlgebraicSimplex.CoordinateRing K j.val)) :
    lowFaceGeometricLength K j i p q ≠ ⊤ := by
  let := (AlgebraicSimplex.face K i).toAlgebra
  rw [lowFaceGeometricLength_eq]
  exact quotientFibreLength_ne_top p q

/-- Exact coefficient dictionary for the maintained unreduced face operator.
This does not declare the operator to be motivic correspondence composition. -/
theorem lowFace_cycle_coefficient (j : Fin 2) (i : Fin (j.val + 2))
    (p : FiniteDominantPrime (AlgebraicSimplex.CoordinateRing K (j.val + 1)))
    (q : FiniteDominantPrime (AlgebraicSimplex.CoordinateRing K j.val)) :
    FreeAbelianGroup.coeff q (simplexFaceCycle K j.val i (FreeAbelianGroup.of p)) =
      ((lowFaceGeometricLength K j i p q).toNat : ℤ) := by
  let := (AlgebraicSimplex.face K i).toAlgebra
  rw [lowFaceGeometricLength_eq]
  exact quotientFibreCycleMap_of_coeff p q

/-- The Cartier coordinate is not in an actual finite dominant source prime.
This is the concrete condition that removes the positive Tor term in the
ordinary source argument; no Tor formalization is asserted. -/
theorem lowFaceCoordinate_not_mem (j : Fin 2) (i : Fin (j.val + 2))
    (p : FiniteDominantPrime (AlgebraicSimplex.CoordinateRing K (j.val + 1))) :
    algebraMap (AlgebraicSimplex.CoordinateRing K (j.val + 1))
      (Laurent (AlgebraicSimplex.CoordinateRing K (j.val + 1)))
      (AlgebraicSimplex.coordinate K (j.val + 1) i) ∉ p.val := by
  intro h
  change AlgebraicSimplex.coordinate K (j.val + 1) i ∈
    p.val.under (AlgebraicSimplex.CoordinateRing K (j.val + 1)) at h
  rw [MonoidAlgebra.FiniteDominantPrime.under_eq_bot, Ideal.mem_bot] at h
  exact AlgebraicSimplex.coordinate_ne_zero K (j.val + 1) i h

/-- Actual source-prime quotient regularity at each of the five low faces. -/
theorem lowFaceCoordinate_regular (j : Fin 2) (i : Fin (j.val + 2))
    (p : FiniteDominantPrime (AlgebraicSimplex.CoordinateRing K (j.val + 1))) :
    IsSMulRegular (Laurent (AlgebraicSimplex.CoordinateRing K (j.val + 1)) ⧸ p.val)
      (algebraMap (AlgebraicSimplex.CoordinateRing K (j.val + 1))
        (Laurent (AlgebraicSimplex.CoordinateRing K (j.val + 1)))
        (AlgebraicSimplex.coordinate K (j.val + 1) i)) :=
  _root_.Module.scalar_regular_primeQuotient p.val _
    (lowFaceCoordinate_not_mem K j i p)

end LowFaces

end AlgebraicGeometry.Torus.FiniteCorrespondence.Fibre
