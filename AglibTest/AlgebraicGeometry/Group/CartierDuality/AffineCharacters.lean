/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Group.CartierDuality.AffineCharacters

/-! Affine characters use the actual scalar Hopf Spec, existing Gm and literal coevaluation unit. -/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite Module
open AlgebraicGeometry.Scheme.Group
open CartierDuality
open scoped TensorProduct Module.Dual.FiniteDual

universe u

variable {k : Type u} [Field k] (A : CommHopfAlgCat.{u} k)
  [FiniteDimensional k A] (R : Type u) [CommRing R] [Algebra k R]

example : (Dual k A →ₐ[k] R) ≃
    ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj
        (op (CommHopfAlgCat.of R (R ⊗[k] A))) ⟶
      MultiplicativeGroup.groupScheme (Spec (CommRingCat.of R))) := scalarCharacterEquiv A R

example (f : Dual k A →ₐ[k] R) :
    specUnitsEquiv (CommAlgCat.of R (R ⊗[k] A)) (scalarCharacterEquiv A R f).hom.hom =
      Units.map (Module.Dual.characterTensorHom k A R f).toMonoidHom
        (HopfAlgebra.coevaluationUnit k A) := scalarCharacterEquiv_coevaluation A R f
