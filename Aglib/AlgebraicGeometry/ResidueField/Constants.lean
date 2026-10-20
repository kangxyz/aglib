/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Points.Closed
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Canonical constants in actual scheme residue fields
-/

@[expose] public section


noncomputable section
open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Scheme
universe u
variable {k : Type u} [Field k] (X : Scheme.{u}) (p : X ⟶ Spec (.of k))
/-- Scalars in an actual residue field are induced by the actual structure morphism. -/
def residueConstants (x : X) : k →+* X.residueField x :=
  (Spec.preimage (X.fromSpecResidueField x ≫ p)).hom

@[instance_reducible] def residueAlgebra (x : X) : Algebra k (X.residueField x) :=
  (residueConstants X p x).toAlgebra


/-- Closed-point residue fields have finite dimension over the actual base field. -/
theorem residue_finite [LocallyOfFiniteType p] (x : ClosedPoint X) :
    letI := residueAlgebra X p x.val
    Module.Finite k (X.residueField x.val) := by
  let := residueAlgebra X p x.val
  have : IsClosedImmersion (X.fromSpecResidueField x.val) :=
    isClosed_singleton_iff_isClosedImmersion.mp x.property
  have hf : IsFinite (X.fromSpecResidueField x.val ≫ p) := by
    rw [isFinite_iff_locallyOfFiniteType_of_jacobsonSpace]
    infer_instance
  apply RingHom.finite_algebraMap.mp
  change (Spec.preimage (X.fromSpecResidueField x.val ≫ p)).hom.Finite
  rw [← IsFinite.SpecMap_iff, Spec.map_preimage]
  exact hf

end AlgebraicGeometry.Scheme

/- Migration source: R5Lab/Aglib/AlgebraicGeometry/ResidueField/Constants.lean
Frozen packet R5 f8a3314ddecffcada2ec721d26d56a937bed9690.
SHA-256 976cc0d2373fa66acd086a3d58d87bd81c9d87379879f6ab89f1a0cace794861.
Native names and imports replace source wrappers; stated conditions and maps are retained. -/
