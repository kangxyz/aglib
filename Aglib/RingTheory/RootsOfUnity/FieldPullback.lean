/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.RootsOfUnity.Galois

/-!
# Field pullback on actual continuous weight-two Galois H¹

A compatible algebra structure on two fields and their algebraic closures
constructs a continuous restriction homomorphism of the actual absolute Galois
groups. The same closure embedding maps roots of unity, hence their tensor
squares. Relative equivariance is proved from normal restriction of field
automorphisms, and the resulting maps descend to continuous Galois H¹.

The closure tower is explicit input. This file does not claim independence of
the choice of closure embedding, and it does not assert naturality of a
motivic Bockstein or supply a motivic/étale comparison map.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace Field.absoluteGaloisGroup.RootsOfUnity.FieldPullback

open Field.absoluteGaloisGroup.RootsOfUnity

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
  [Algebra (AlgebraicClosure K) (AlgebraicClosure L)]
  [IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure L)]
  (n : ℕ)

/-- The genuine closure embedding maps the actual roots-of-unity groups. -/
def muMap : Mu K n →ₗ[ℤ] Mu L n :=
  (restrictRootsOfUnity (algebraMap (AlgebraicClosure K) (AlgebraicClosure L))
    n).toAdditive.toIntLinearMap

omit [Algebra K L] [IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure L)] in
@[simp] theorem muMap_value (x : Mu K n) :
    (((muMap K L n x).toMul : (AlgebraicClosure L)ˣ) : AlgebraicClosure L) =
      algebraMap (AlgebraicClosure K) (AlgebraicClosure L)
        ((x.toMul : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) := rfl

/-- Normal restriction commutes with the selected embedding of algebraic closures. -/
theorem restriction_commutes (g : Field.absoluteGaloisGroup L) (x : AlgebraicClosure K) :
    algebraMap (AlgebraicClosure K) (AlgebraicClosure L)
      ((show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from
        Field.absoluteGaloisGroup.mapOfAlgebra K L g) x) =
      (show AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L from g)
        (algebraMap (AlgebraicClosure K) (AlgebraicClosure L) x) := by
  exact ((show AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L from g).restrictScalarsHom
    K).restrictNormal_commutes (AlgebraicClosure K) x

/-- The actual root map is equivariant relative to continuous Galois restriction. -/
theorem muMap_smul (g : Field.absoluteGaloisGroup L) (x : Mu K n) :
    muMap K L n (Field.absoluteGaloisGroup.mapOfAlgebra K L g • x) =
      g • muMap K L n x := by
  ext
  exact restriction_commutes K L g
    ((x.toMul : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)

end Field.absoluteGaloisGroup.RootsOfUnity.FieldPullback
