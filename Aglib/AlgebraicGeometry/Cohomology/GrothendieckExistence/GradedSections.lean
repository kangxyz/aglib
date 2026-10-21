/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedHomogeneousAction
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedActionLaws
public import Aglib.RingTheory.AssociatedGraded.Multiplication
public import Mathlib.Algebra.Module.GradedModule

/-! # The actual graded action on sections of the formal successive pieces -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent
open GradedMonoid

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
  (F : AdicSystem X (idealThickeningIdealSheaf f I))

omit [IsLocallyNoetherian X] in
private theorem section_apply_heq {M N N' : X.Modules} (hN : N = N')
    (φ : M ⟶ N) (ψ : M ⟶ N') (h : HEq φ ψ) (U : X.Opens) (x : Γ(M, U)) :
    HEq (φ.app U x) (ψ.app U x) := by
  subst N'
  have hh : φ = ψ := eq_of_heq h
  subst ψ
  rfl

/-- The native heterogeneous graded module structure on original sections.
All its scalar maps are the original finite-stage maps descended through
native associated-graded components. -/
abbrev formalGradedSectionsGModule (U : X.Opens) :
    DirectSum.Gmodule (fun n => I.associatedGradedGrading n)
      (fun n => Γ(F.gradedPiece n, U)) where
  smul a x := (formalGradedHomogeneousAction f I F _ _ a).app U x
  one_smul := by
    rintro ⟨n, x⟩
    apply Sigma.ext (Nat.zero_add n)
    have h1 : (GOne.one (A := fun n => I.associatedGradedGrading n) : I.associatedGradedGrading 0) =
        I.associatedGradedComponentMap 0 ⟨1, by simp⟩ := by
      apply Subtype.ext
      simp [I.associatedGradedComponentMap_zero]
    change HEq ((formalGradedHomogeneousAction f I F 0 n
      (GOne.one (A := fun n => I.associatedGradedGrading n))).app U x) x
    rw [h1, formalGradedHomogeneousAction_componentMap]
    exact section_apply_heq (congrArg F.gradedPiece (Nat.zero_add n)) _ _
      (formalGradedScalarMap_one f I F n) U x
  mul_smul := by
    rintro ⟨r, a⟩ ⟨s, b⟩ ⟨n, x⟩
    obtain ⟨a, rfl⟩ := I.associatedGradedComponentMap_surjective r a
    obtain ⟨b, rfl⟩ := I.associatedGradedComponentMap_surjective s b
    apply Sigma.ext (Nat.add_assoc r s n)
    have hab : GMul.mul (A := fun n => I.associatedGradedGrading n)
        (I.associatedGradedComponentMap r a)
        (I.associatedGradedComponentMap s b) =
        I.associatedGradedComponentMap (r + s)
          ⟨(a : A) * b, by rw [pow_add]; exact Ideal.mul_mem_mul a.property b.property⟩ := by
      apply Subtype.ext
      exact I.associatedGradedComponentMap_mul r s a b
    change HEq ((formalGradedHomogeneousAction f I F (r + s) n
      (GMul.mul (A := fun n => I.associatedGradedGrading n) (I.associatedGradedComponentMap r a)
        (I.associatedGradedComponentMap s b))).app U x)
      ((formalGradedHomogeneousAction f I F r (s + n)
        (I.associatedGradedComponentMap r a)).app U
          ((formalGradedHomogeneousAction f I F s n
            (I.associatedGradedComponentMap s b)).app U x))
    rw [hab, formalGradedHomogeneousAction_componentMap,
      formalGradedHomogeneousAction_componentMap, formalGradedHomogeneousAction_componentMap]
    have hh := section_apply_heq (congrArg F.gradedPiece (Nat.add_assoc r s n).symm) _ _
      (formalGradedScalarMap_mul f I F r s n a b) U x
    simpa only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] using hh.symm
  smul_add a x y := by
    exact map_add ((formalGradedHomogeneousAction f I F _ _ a).app U).hom x y
  smul_zero a := map_zero ((formalGradedHomogeneousAction f I F _ _ a).app U).hom
  add_smul a b x := by
    simp only [map_add, Scheme.Modules.Hom.add_app]
    rfl
  zero_smul x := by
    simp only [map_zero]
    rfl

end AlgebraicGeometry.Scheme.Cohomology
