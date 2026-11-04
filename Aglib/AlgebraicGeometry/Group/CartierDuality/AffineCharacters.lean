/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Group.CartierDuality.GroupLikeCharacters
public import Aglib.RingTheory.HopfAlgebra.FiniteDualCharacters

/-!
# Finite-dual algebra points and actual affine characters

Over every commutative coefficient algebra, the original finite-dual algebra
points are exactly the actual characters of the native scalar Hopf Spec into
the existing multiplicative group. The original universal coevaluation unit
is the whole coordinate unit of this character, naturally in coefficients.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite Module
open scoped TensorProduct Module.Dual.FiniteDual

namespace AlgebraicGeometry.Scheme.Group.CartierDuality

universe u

variable {k : Type u} [Field k] (A : CommHopfAlgCat.{u} k)
  [FiniteDimensional k A] (R : Type u) [CommRing R] [Algebra k R]

/-- The actual affine character correspondence, on the native scalar-extended Hopf algebra. -/
def scalarCharacterEquiv :
    (Dual k A →ₐ[k] R) ≃
      ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj
          (op (CommHopfAlgCat.of R (R ⊗[k] A))) ⟶
        MultiplicativeGroup.groupScheme (Spec (CommRingCat.of R))) :=
  (Module.Dual.algHomGroupLikeEquiv k A R).trans
    (groupLikeCharacterEquiv (CommHopfAlgCat.of R (R ⊗[k] A)))

/-- The represented character has precisely the original native group-like unit. -/
theorem scalarCharacterEquiv_units (f : Dual k A →ₐ[k] R) :
    specUnitsEquiv (CommAlgCat.of R (R ⊗[k] A))
        (scalarCharacterEquiv A R f).hom.hom =
      (Module.Dual.algHomGroupLikeUnitsEquiv k A R f).val :=
  groupLikeCharacterEquiv_units (CommHopfAlgCat.of R (R ⊗[k] A))
    (Module.Dual.algHomGroupLikeEquiv k A R f)

/-- The whole character unit is the original universal coevaluation unit pulled by its character. -/
theorem scalarCharacterEquiv_coevaluation (f : Dual k A →ₐ[k] R) :
    specUnitsEquiv (CommAlgCat.of R (R ⊗[k] A))
        (scalarCharacterEquiv A R f).hom.hom =
      Units.map (Module.Dual.characterTensorHom k A R f).toMonoidHom
        (HopfAlgebra.coevaluationUnit k A) :=
  (scalarCharacterEquiv_units A R f).trans
    (Module.Dual.algHomGroupLikeUnitsEquiv_eq_map_coevaluationUnit k A R f)

/-- The original character coordinates are natural for arbitrary coefficient-algebra maps. -/
theorem scalarCharacterEquiv_units_naturality {S : Type u} [CommRing S] [Algebra k S]
    (f : Dual k A →ₐ[k] R) (g : R →ₐ[k] S) :
    specUnitsEquiv (CommAlgCat.of S (S ⊗[k] A))
        (scalarCharacterEquiv A S (g.comp f)).hom.hom =
      Units.map (Algebra.TensorProduct.map g (AlgHom.id k A)).toMonoidHom
        (specUnitsEquiv (CommAlgCat.of R (R ⊗[k] A))
          (scalarCharacterEquiv A R f).hom.hom) := by
  rw [scalarCharacterEquiv_units, scalarCharacterEquiv_units]
  exact Module.Dual.algHomGroupLikeUnitsEquiv_naturality k A R f g

end AlgebraicGeometry.Scheme.Group.CartierDuality
