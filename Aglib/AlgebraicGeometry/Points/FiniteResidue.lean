/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Smooth.FiniteResidueFibre
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Finite closed residue fields inside prescribed open sets

Actual finite closed residue points in each nonempty open over finite-type integer algebra.
Source88–108 PrimeRootUnits wrapper stays downstream; do not import R5 MilnorK2 namespace.

Source: `R5Lab.Aglib.AlgebraicGeometry.Points.FiniteResidue`, frozen R5
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`989a338b71c004190639883060f060c0cbf89b2265ebbaa588dcc5993a92406d`. Selected lines: [[37, 87]].
The actual objects, canonical maps, universes and stated premises are retained.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u

/-- Evaluation on the actual residue field, induced by the original structure map. -/
def residueEvaluation (A : Type u) [CommRing A] (X : Scheme.{u})
    (p : X ⟶ Spec (.of A)) (x : X) : A →+* X.residueField x :=
  (Spec.preimage (X.fromSpecResidueField x ≫ p)).hom

@[simp] theorem Spec_map_residueEvaluation (A : Type u) [CommRing A]
    (X : Scheme.{u}) (p : X ⟶ Spec (.of A)) (x : X) :
    Spec.map (CommRingCat.ofHom (residueEvaluation A X p x)) =
      X.fromSpecResidueField x ≫ p :=
  Spec.map_preimage _

/-- Every actual closed-point residue field on a scheme locally of finite
type over a finite-type integer algebra is finite. -/
theorem finite_residueField_of_closed
    (A : Type u) [CommRing A] [Algebra ℤ A] [Algebra.FiniteType ℤ A]
    (X : Scheme.{u}) (p : X ⟶ Spec (.of A)) [LocallyOfFiniteType p]
    (x : X) (hx : IsClosed ({x} : Set X)) :
    Finite (X.residueField x) := by
  let φ : A →+* X.residueField x :=
    (Spec.preimage (X.fromSpecResidueField x ≫ p)).hom
  let : Algebra A (X.residueField x) := φ.toAlgebra
  have : IsClosedImmersion (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  have hφ : φ.FiniteType := by
    apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp
    rw [Spec.map_preimage]
    infer_instance
  let : Algebra.FiniteType A (X.residueField x) :=
    RingHom.finiteType_algebraMap.mp hφ
  let : Algebra.FiniteType ℤ (X.residueField x) := by
    have h := RingHom.FiniteType.comp hφ
      (RingHom.finiteType_algebraMap.mpr (inferInstance : Algebra.FiniteType ℤ A))
    have heq : φ.comp (algebraMap ℤ A) = algebraMap ℤ (X.residueField x) :=
      Subsingleton.elim _ _
    exact RingHom.finiteType_algebraMap.mp (heq ▸ h)
  exact Algebra.FiniteType.finite_of_finiteType_int (X.residueField x)

/-- A nonempty open set of an actual finite-type integer-base scheme
contains a closed point with finite residue field. -/
theorem exists_finite_closedPoint_in_open
    (A : Type u) [CommRing A] [Algebra ℤ A] [Algebra.FiniteType ℤ A]
    (X : Scheme.{u}) (p : X ⟶ Spec (.of A)) [LocallyOfFiniteType p] (U : X.Opens)
    (hU : (U : Set X).Nonempty) :
    ∃ x : X, x ∈ U ∧ IsClosed ({x} : Set X) ∧ Finite (X.residueField x) := by
  let : IsJacobsonRing ℤ := Algebra.Smooth.integers_jacobson
  let : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := ℤ) (B := A)
  let : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
  obtain ⟨x, hx, hc⟩ := nonempty_inter_closedPoints hU U.isOpen.isLocallyClosed
  exact ⟨x, hx, hc, finite_residueField_of_closed A X p x hc⟩

end AlgebraicGeometry.Scheme
