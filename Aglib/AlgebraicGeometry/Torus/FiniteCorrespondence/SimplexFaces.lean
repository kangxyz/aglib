/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Torus.FiniteCorrespondence.PrincipalFibres
public import Aglib.AlgebraicGeometry.AlgebraicSimplex.Basic

/-!
# SimplexFaces for finite correspondences on the two-dimensional torus

Native migration from `lean/R5Lab/Aglib/AlgebraicGeometry/Torus/FiniteCorrespondence/`
leaf `SimplexFaces.lean` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`3edfbf6b83c95fd72c5f78747c045a28c787d1151e618e5bfd25336098cb9f6c`.

The Laurent object is `MonoidAlgebra R (Multiplicative (ℤ × ℤ))` in its original
coordinate order. Statements retain their displayed finiteness, normality,
Noetherianity, flatness, regularity and scalar-map hypotheses.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AlgebraicGeometry.Torus.FiniteCorrespondence
open _root_.Module.CommutingAutomorphisms
open _root_.Module.CommutingAutomorphisms.LaurentSupport
open MonoidAlgebra (FiniteDominantPrime)
open LaurentSupport
universe u
variable {R : Type u} [CommRing R]

/-- The encoded finite-cycle face operator. Naturality on original objects requires the
principal Euler-length argument; it is not an input here.

Source mapping: supporting generalized local construction for
`K2-018#prop:k2018-arithmetic-characters`, source snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Encoded actual-face prerequisite subset: every Field K, n : Nat and i : Fin(n + 2)
define the additive finite-cycle operator through the actual face algebra instance; no
original-object face equality or face-flatness premise is supplied. -/
def simplexFaceCycle (K : Type u) [Field K] (n : ℕ) (i : Fin (n + 2)) :
    FreeAbelianGroup (FiniteDominantPrime (AlgebraicSimplex.CoordinateRing K (n + 1))) →+
      FreeAbelianGroup (FiniteDominantPrime (AlgebraicSimplex.CoordinateRing K n)) := by
  let := (AlgebraicSimplex.face K i).toAlgebra
  exact quotientFibreCycleMap

end AlgebraicGeometry.Torus.FiniteCorrespondence
