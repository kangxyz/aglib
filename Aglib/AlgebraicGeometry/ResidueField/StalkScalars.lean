/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ResidueField.Constants
public import Aglib.AlgebraicGeometry.Stalk.Scalar
public import Mathlib.RingTheory.LocalRing.Length

/-!
# Compatibility of actual residue-field and stalk constants
-/

@[expose] public section


noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite IsLocalRing
namespace AlgebraicGeometry.Scheme
section StalkScalars

universe u
variable {k : Type u} [Field k] (X : Scheme.{u}) (p : X ⟶ Spec (.of k))

/-- Constants from the structural map, followed by the actual germ at `x`. -/
abbrev stalkConstants (x : X) : k →+* X.presheaf.stalk x :=
  p.stalkScalar x

/-- Field constants are the literal specialization of the general structural stalk map. -/
theorem stalkConstants_eq_stalkScalar (x : X) :
    stalkConstants X p x = p.stalkScalar x := rfl

/-- The divisor-degree residue map is the reduction of the actual constant germ. -/
theorem residueConstants_eq_stalk (x : X) :
    Scheme.residueConstants X p x = (X.residue x).hom.comp (stalkConstants X p x) := by
  have hc : Spec.preimage (X.fromSpecResidueField x ≫ p) =
      (Scheme.ΓSpecIso (.of k)).inv ≫ (X.fromSpecResidueField x ≫ p).appTop ≫
        (Scheme.ΓSpecIso (X.residueField x)).hom := by
    calc
      _ = (Scheme.ΓSpecIso (.of k)).inv ≫
          (Spec.map (Spec.preimage (X.fromSpecResidueField x ≫ p))).appTop ≫
          (Scheme.ΓSpecIso (X.residueField x)).hom := by
        rw [Scheme.ΓSpecIso_naturality]
        simp
      _ = _ := by rw [Spec.map_preimage]
  change (Spec.preimage _).hom = _
  rw [hc, Scheme.Hom.comp_appTop, Scheme.fromSpecResidueField, Scheme.Hom.comp_appTop,
    Scheme.fromSpecStalk_appTop]
  simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id, Category.comp_id,
    ΓSpecIso_inv_naturality, Category.assoc, ΓSpecIso_inv_naturality_assoc,
    ΓSpecIso_naturality, ΓSpecIso_naturality_assoc, Iso.inv_hom_id_assoc,
    CommRingCat.hom_comp]
  ext a
  rfl

/-- The structural base-field algebra on the actual stalk. -/
abbrev stalkConstantsAlgebra (x : X) : Algebra k (X.presheaf.stalk x) :=
  (stalkConstants X p x).toAlgebra

/-- The residue algebra induced by those same actual stalk constants. -/
abbrev residueAlgebraFromStalk (x : X) : Algebra k (X.residueField x) := by
  let := stalkConstantsAlgebra X p x
  exact inferInstanceAs (Algebra k (ResidueField (X.presheaf.stalk x)))

/-- Equality of algebra structures, rather than an unrelated residue-field isomorphism. -/
theorem residueAlgebra_eq_stalk (x : X) :
    Scheme.residueAlgebra X p x = residueAlgebraFromStalk X p x := by
  apply Algebra.algebra_ext
  intro a
  change Scheme.residueConstants X p x a = (X.residue x).hom (stalkConstants X p x a)
  exact congrArg (fun f : k →+* X.residueField x => f a) (residueConstants_eq_stalk X p x)

/-- Closed-point residue finiteness transported across that equality of scalar maps. -/
theorem residue_finite_from_stalk [LocallyOfFiniteType p]
    (x : X) (hx : IsClosed ({x} : Set X)) :
    letI := stalkConstantsAlgebra X p x
    letI := residueAlgebraFromStalk X p x
    Module.Finite k (X.residueField x) := by
  let := stalkConstantsAlgebra X p x
  let := residueAlgebraFromStalk X p x
  have h := Scheme.residue_finite X p ⟨x, hx⟩
  rw [residueAlgebra_eq_stalk X p x] at h
  exact h

end StalkScalars
end AlgebraicGeometry.Scheme

/- Migration source: R5Lab/Aglib/AlgebraicGeometry/ResidueField/StalkScalars.lean
Frozen packet R5 f8a3314ddecffcada2ec721d26d56a937bed9690.
SHA-256 d223aefd0106f3fde88e2a7c78adbf362079b2747d0169fd2aeaf727056df134.
Native names and imports replace source wrappers; stated conditions and maps are retained. -/
