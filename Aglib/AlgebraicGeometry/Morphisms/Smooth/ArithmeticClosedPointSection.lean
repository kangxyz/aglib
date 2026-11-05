/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Smooth.FinitePointEtaleSection
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.RationalPointEtaleLocal
public import Aglib.AlgebraicGeometry.Points.FiniteResidue
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # An actual etale base-change section through an arithmetic closed point

The unchanged scheme residue point of a closed point has a finite field.
Its original algebra map extends over a genuine etale base algebra. The
resulting native pullback section passes through that same residue point.
The new base remains finite type over the integers. No section through an
arbitrary transcendental geometric point is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

universe u

/-- Every closed point of an affine smooth arithmetic family lies on the
actual section after one genuine etale affine base change. The original
residue field, residue point, family and both pullback projections are kept. -/
theorem exists_etale_baseChangeSection_through_arithmetic_closedPoint
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
    [Algebra.FiniteType ℤ R] [Algebra.Smooth R B]
    (x : Spec (.of B)) (hx : IsClosed ({x} : Set (Spec (.of B)))) :
    ∃ (E : Type u) (_ : CommRing E) (_ : Algebra R E),
      Algebra.Etale R E ∧ Algebra.FiniteType ℤ E ∧
      ∃ (σ : Spec (.of E) ⟶ pullback (Spec.algebraMap R B) (Spec.algebraMap R E))
        (l : Spec (.of ((Spec (.of B)).residueField x)) ⟶ Spec (.of E)),
        σ ≫ pullback.snd (Spec.algebraMap R B) (Spec.algebraMap R E) = 𝟙 _ ∧
        l ≫ σ ≫ pullback.fst (Spec.algebraMap R B) (Spec.algebraMap R E) =
          (Spec (.of B)).fromSpecResidueField x := by
  let X : Scheme.{u} := Spec (.of B)
  let L := X.residueField x
  let f : X ⟶ Spec (.of R) := Spec.algebraMap R B
  let η : Spec (.of L) ⟶ X := X.fromSpecResidueField x
  let φ : B →+* L := (Spec.preimage η).hom
  let : Algebra R L := (φ.comp (algebraMap R B)).toAlgebra
  let ψ : B →ₐ[R] L := { __ := φ, commutes' := fun _ => rfl }
  let : Smooth f := HasRingHomProperty.Spec_iff.mpr
    (RingHom.smooth_algebraMap.mpr (inferInstance : Algebra.Smooth R B))
  let : Finite L := finite_residueField_of_closed R X f x hx
  obtain ⟨E, hE, hRE, het, ε, l, hε⟩ :=
    Algebra.Smooth.exists_etale_lift_of_finite_field R B L ψ
  let : CommRing E := hE
  let : Algebra R E := hRE
  let : Algebra.Etale R E := het
  let : IsScalarTower ℤ R E := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have hft : Algebra.FiniteType ℤ E := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType ℤ R) (inferInstance : Algebra.FiniteType R E)
  refine ⟨E, hE, hRE, het, hft, rationalPointBaseChangeSection ε,
    Spec.map (CommRingCat.ofHom l.toRingHom), rationalPointBaseChangeSection_snd ε, ?_⟩
  rw [rationalPointBaseChangeSection_fst, ← Spec.map_comp]
  have hcomp : (CommRingCat.ofHom ε.toRingHom) ≫ CommRingCat.ofHom l.toRingHom =
      CommRingCat.ofHom ψ.toRingHom :=
    congrArg (fun a : B →ₐ[R] L => CommRingCat.ofHom a.toRingHom) hε
  rw [hcomp]
  exact Spec.map_preimage η

end AlgebraicGeometry.Scheme
