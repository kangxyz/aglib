/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedSections
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedDegreeZero
public import Aglib.AlgebraicGeometry.Modules.IdealPowers.AffineSections
public import Aglib.RingTheory.AssociatedGraded.ExternalScalars
public import Aglib.RingTheory.TensorProduct.CommutingActions

/-! # The actual tensor-ring action on affine formal graded sections -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite DirectSum GradedMonoid
open scoped TensorProduct
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
  (F : AdicSystem X (idealThickeningIdealSheaf f I)) (U : X.Opens)

omit [IsLocallyNoetherian X] in
/-- The original coordinate-ring algebra on an open. -/
@[instance_reducible]
def formalGradedSectionAlgebra : Algebra A Γ(X, U) :=
  (idealSectionRingHom X (idealThickeningBaseScalar f) U).toAlgebra

/-- Base scalars act on each graded-piece section through the original structural map. -/
local instance (n : ℕ) : Module A Γ(F.gradedPiece n, U) :=
  idealSectionModule X (idealThickeningBaseScalar f) (F.gradedPiece n) U
/-- The original homogeneous sheaf maps act on the graded-piece sections. -/
local instance : DirectSum.Gmodule (fun n => I.associatedGradedGrading n)
    (fun n => Γ(F.gradedPiece n, U)) := formalGradedSectionsGModule f I F U

/-- The external graded ring acts through the original homogeneous sheaf maps. -/
@[instance_reducible]
def formalGradedExternalSectionsModule :
    Module I.associatedGraded (⨁ n, Γ(F.gradedPiece n, U)) :=
  I.associatedGradedExternalModule (fun n => Γ(F.gradedPiece n, U))

/-- The native direct sum carries the original external associated-graded action. -/
local instance : Module I.associatedGraded (⨁ n, Γ(F.gradedPiece n, U)) :=
  formalGradedExternalSectionsModule f I F U

/-- Coordinate scalars commute because each homogeneous action is a genuine sheaf morphism. -/
theorem formalGradedExternalSectionsComm :
    SMulCommClass Γ(X, U) I.associatedGraded (⨁ n, Γ(F.gradedPiece n, U)) := by
  apply I.associatedGradedExternalModule_smulComm
  intro r n a b x
  exact ((formalGradedHomogeneousAction f I F r n a).val.app (op U)).hom.map_smul b x

private theorem directSum_of_heq {M : ℕ → Type u} [∀ n, AddCommGroup (M n)]
    {r n : ℕ} (h : r = n) (x : M r) (y : M n) (hxy : HEq x y) :
    DirectSum.of M r x = DirectSum.of M n y := by
  subst n
  rw [eq_of_heq hxy]

omit [IsLocallyNoetherian X] in
private theorem section_value_heq {M N N' : X.Modules} (hN : N = N')
    (φ : M ⟶ N) (ψ : M ⟶ N') (h : HEq φ ψ) (x : Γ(M, U)) :
    HEq (φ.app U x) (ψ.app U x) := by
  subst N'
  rw [eq_of_heq h]

/-- The degree-zero action retains the original structural-ring action. -/
theorem formalGradedExternalSectionsTower :
    IsScalarTower A I.associatedGraded (⨁ n, Γ(F.gradedPiece n, U)) := by
  apply I.associatedGradedExternalModule_scalarTower
  intro a n x
  rw [I.associatedGradedExternalModule_smul]
  change DirectSum.of (fun k => Γ(F.gradedPiece k, U)) (0 + n)
    ((formalGradedHomogeneousAction f I F 0 n
      (I.associatedGradedComponentMap 0 ⟨a, by simp⟩)).app U x) = _
  rw [formalGradedHomogeneousAction_componentMap]
  apply directSum_of_heq (Nat.zero_add n)
  have hh := section_value_heq U (congrArg F.gradedPiece (Nat.zero_add n)) _ _
    (formalGradedScalarMap_degreeZero f I F n a) x
  exact hh.trans (heq_of_eq (globalScalarEndomorphism_app X (F.gradedPiece n)
    (idealThickeningBaseScalar f a) U x))

local instance : SMulCommClass Γ(X, U) I.associatedGraded (⨁ n, Γ(F.gradedPiece n, U)) :=
  formalGradedExternalSectionsComm f I F U
local instance : IsScalarTower A I.associatedGraded (⨁ n, Γ(F.gradedPiece n, U)) :=
  formalGradedExternalSectionsTower f I F U

/-- The canonical affine tensor action, with no flatness or algebraization assumption. -/
@[instance_reducible]
def formalGradedAffineModule :
    letI := formalGradedSectionAlgebra f U
    Module (Γ(X, U) ⊗[A] I.associatedGraded) (⨁ n, Γ(F.gradedPiece n, U)) := by
  letI := formalGradedSectionAlgebra f U
  letI (n : ℕ) : IsScalarTower A Γ(X, U) Γ(F.gradedPiece n, U) :=
    IsScalarTower.of_compHom A Γ(X, U) Γ(F.gradedPiece n, U)
  exact Algebra.TensorProduct.commutingModule A Γ(X, U) I.associatedGraded _

end AlgebraicGeometry.Scheme.Cohomology
