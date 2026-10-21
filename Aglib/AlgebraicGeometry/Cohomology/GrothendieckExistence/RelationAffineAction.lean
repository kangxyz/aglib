/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.RelationAffineModule
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.RelationHomogeneousAction
public import Aglib.RingTheory.TensorProduct.KernelTransport

/-! # Original homogeneous action equations for the actual relation tensor module -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite DirectSum
open scoped TensorProduct
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent
open AlgebraicGeometry.Scheme.Modules.Coherent.AdicSystem
namespace AlgebraicGeometry.Scheme.Cohomology
universe u
variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A) (U : X.Opens)
  {P F : AdicSystem X (idealThickeningIdealSheaf f I)} (φ : P ⟶ F)

/-- Coefficient graded sections carry the actual tensor-coordinate action. -/
local instance (G : AdicSystem X (idealThickeningIdealSheaf f I)) :
    letI := formalGradedSectionAlgebra f U
    letI : Semiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
      Algebra.TensorProduct.instSemiring (R := A) (A := Γ(X, U)) (B := I.associatedGraded)
    letI : NonAssocSemiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
      (inferInstance : Semiring (Γ(X, U) ⊗[A] I.associatedGraded)).toNonAssocSemiring
    Module (Γ(X, U) ⊗[A] I.associatedGraded) (⨁ n, Γ(G.gradedPiece n, U)) := by
  letI := formalGradedSectionAlgebra f U
  letI : Semiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
    Algebra.TensorProduct.instSemiring (R := A) (A := Γ(X, U)) (B := I.associatedGraded)
  letI : NonAssocSemiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
    (inferInstance : Semiring (Γ(X, U) ⊗[A] I.associatedGraded)).toNonAssocSemiring
  exact formalGradedAffineModule f I G U
/-- The source formal coefficient retains its original homogeneous section action. -/
local instance : DirectSum.Gmodule (fun n => I.associatedGradedGrading n)
    (fun n => Γ(P.gradedPiece n, U)) := formalGradedSectionsGModule f I P U
/-- The source graded section total retains its external associated-graded action. -/
local instance : Module I.associatedGraded (⨁ n, Γ(P.gradedPiece n, U)) :=
  formalGradedExternalSectionsModule f I P U
/-- Relation graded sections carry the action transported from the actual tensor kernel. -/
local instance :
    letI := formalGradedSectionAlgebra f U
    letI : Semiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
      Algebra.TensorProduct.instSemiring (R := A) (A := Γ(X, U)) (B := I.associatedGraded)
    letI : NonAssocSemiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
      (inferInstance : Semiring (Γ(X, U) ⊗[A] I.associatedGraded)).toNonAssocSemiring
    Module (Γ(X, U) ⊗[A] I.associatedGraded)
      (⨁ n, Γ(relationGradedPiece φ n, U)) := by
  letI := formalGradedSectionAlgebra f U
  letI : Semiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
    Algebra.TensorProduct.instSemiring (R := A) (A := Γ(X, U)) (B := I.associatedGraded)
  letI : NonAssocSemiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
    (inferInstance : Semiring (Γ(X, U) ⊗[A] I.associatedGraded)).toNonAssocSemiring
  exact relationGradedAffineModule f I U φ

/-- The original componentwise inclusion, retaining coordinate linearity. -/
def relationGradedTotalInclusion :
    (⨁ n, Γ(relationGradedPiece φ n, U)) →ₗ[Γ(X, U)] (⨁ n, Γ(P.gradedPiece n, U)) :=
  DirectSum.lmap fun n => ((relationGradedι f I φ n).val.app (op U)).hom

@[simp]
theorem relationGradedTotalInclusion_of (n : ℕ) (x : Γ(relationGradedPiece φ n, U)) :
    relationGradedTotalInclusion f I U φ (DirectSum.of _ n x) =
      DirectSum.of _ n ((relationGradedι f I φ n).app U x) := by
  exact DirectSum.lmap_of
    (fun k => ((relationGradedι f I φ k).val.app (op U)).hom) n x

/-- The transported kernel coordinates retain exactly the original total inclusion. -/
theorem relationGradedAffineKernelAddEquiv_coe (x : ⨁ n, Γ(relationGradedPiece φ n, U)) :
    (relationGradedAffineKernelAddEquiv f I U φ x : ⨁ n, Γ(P.gradedPiece n, U)) =
      relationGradedTotalInclusion f I U φ x := by
  ext n
  exact relationGradedTotalKernelEquiv_apply_component φ U x n

theorem relationGradedTotalInclusion_injective :
    Function.Injective (relationGradedTotalInclusion f I U φ) := by
  apply (DirectSum.lmap_injective _).mpr
  intro n
  have : Mono (relationGradedι f I φ n) := by
    dsimp [relationGradedι]
    infer_instance
  exact moduleHom_app_injective (relationGradedι f I φ n) U

/-- Restriction of the actual tensor-kernel action to the original graded scalar ring. -/
@[instance_reducible]
def relationGradedExternalModule :
    Module I.associatedGraded (⨁ n, Γ(relationGradedPiece φ n, U)) := by
  letI := formalGradedSectionAlgebra f U
  letI : Semiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
    Algebra.TensorProduct.instSemiring (R := A) (A := Γ(X, U)) (B := I.associatedGraded)
  letI : NonAssocSemiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
    (inferInstance : Semiring (Γ(X, U) ⊗[A] I.associatedGraded)).toNonAssocSemiring
  exact Algebra.TensorProduct.kernelTransportScalarModule
    (A := A) (B := Γ(X, U)) (S := I.associatedGraded) (formalGradedAffineMap f I U φ)
    (relationGradedAffineKernelAddEquiv f I U φ)

/-- Restriction of the tensor-kernel action gives the original graded scalar action. -/
local instance : Module I.associatedGraded (⨁ n, Γ(relationGradedPiece φ n, U)) :=
  relationGradedExternalModule f I U φ

private theorem coefficient_tmul_smul (b : Γ(X, U)) (s : I.associatedGraded)
    (x : ⨁ n, Γ(P.gradedPiece n, U)) :
    letI := formalGradedSectionAlgebra f U
    letI : Semiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
      Algebra.TensorProduct.instSemiring (R := A) (A := Γ(X, U)) (B := I.associatedGraded)
    letI : NonAssocSemiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
      (inferInstance : Semiring (Γ(X, U) ⊗[A] I.associatedGraded)).toNonAssocSemiring
    (b ⊗ₜ[A] s) • x = b • s • x := by
  let := formalGradedSectionAlgebra f U
  let : Semiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
    Algebra.TensorProduct.instSemiring (R := A) (A := Γ(X, U)) (B := I.associatedGraded)
  let : NonAssocSemiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
    (inferInstance : Semiring (Γ(X, U) ⊗[A] I.associatedGraded)).toNonAssocSemiring
  rfl

/-- The actual transported tensor action preserves the original total inclusion. -/
theorem relationGradedAffineModule_inclusion
    (t : letI := formalGradedSectionAlgebra f U; Γ(X, U) ⊗[A] I.associatedGraded)
    (x : ⨁ n, Γ(relationGradedPiece φ n, U)) :
    letI := formalGradedSectionAlgebra f U
    letI : Semiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
      Algebra.TensorProduct.instSemiring (R := A) (A := Γ(X, U)) (B := I.associatedGraded)
    letI : NonAssocSemiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
      (inferInstance : Semiring (Γ(X, U) ⊗[A] I.associatedGraded)).toNonAssocSemiring
    relationGradedTotalInclusion f I U φ (t • x) =
      t • relationGradedTotalInclusion f I U φ x := by
  let := formalGradedSectionAlgebra f U
  let : Semiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
    Algebra.TensorProduct.instSemiring (R := A) (A := Γ(X, U)) (B := I.associatedGraded)
  let : NonAssocSemiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
    (inferInstance : Semiring (Γ(X, U) ⊗[A] I.associatedGraded)).toNonAssocSemiring
  let e : (⨁ n, Γ(relationGradedPiece φ n, U)) ≃+
      (formalGradedAffineMap f I U φ).ker := relationGradedAffineKernelAddEquiv f I U φ
  have h := congrArg (fun z : (formalGradedAffineMap f I U φ).ker => z.val)
    ((e.linearEquiv (Γ(X, U) ⊗[A] I.associatedGraded)).map_smul t x)
  change (e (t • x)).val = t • (e x).val at h
  simpa only [e, relationGradedAffineKernelAddEquiv_coe] using h

/-- Restriction to the graded scalar ring preserves the same original inclusion. -/
theorem relationGradedExternalModule_inclusion (s : I.associatedGraded)
    (x : ⨁ n, Γ(relationGradedPiece φ n, U)) :
    relationGradedTotalInclusion f I U φ (s • x) =
      s • relationGradedTotalInclusion f I U φ x := by
  let := formalGradedSectionAlgebra f U
  let : Semiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
    Algebra.TensorProduct.instSemiring (R := A) (A := Γ(X, U)) (B := I.associatedGraded)
  let : NonAssocSemiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
    (inferInstance : Semiring (Γ(X, U) ⊗[A] I.associatedGraded)).toNonAssocSemiring
  change relationGradedTotalInclusion f I U φ (((1 : Γ(X, U)) ⊗ₜ[A] s) • x) = _
  rw [relationGradedAffineModule_inclusion, coefficient_tmul_smul, one_smul]

/-- Literal tensor action retains the original coordinate scalar multiplication. -/
theorem relationGradedAffineModule_tmul_smul (b : Γ(X, U)) (s : I.associatedGraded)
    (x : ⨁ n, Γ(relationGradedPiece φ n, U)) :
    letI := formalGradedSectionAlgebra f U
    letI : Semiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
      Algebra.TensorProduct.instSemiring (R := A) (A := Γ(X, U)) (B := I.associatedGraded)
    letI : NonAssocSemiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
      (inferInstance : Semiring (Γ(X, U) ⊗[A] I.associatedGraded)).toNonAssocSemiring
    (b ⊗ₜ[A] s) • x = b • s • x := by
  let := formalGradedSectionAlgebra f U
  let : Semiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
    Algebra.TensorProduct.instSemiring (R := A) (A := Γ(X, U)) (B := I.associatedGraded)
  let : NonAssocSemiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
    (inferInstance : Semiring (Γ(X, U) ⊗[A] I.associatedGraded)).toNonAssocSemiring
  apply relationGradedTotalInclusion_injective f I U φ
  rw [relationGradedAffineModule_inclusion, coefficient_tmul_smul, _root_.map_smul,
    relationGradedExternalModule_inclusion]

/-- The transported scalar action is the original homogeneous relation map
on every original pure component. -/
theorem relationGradedExternalModule_smul (r n : ℕ)
    (a : I.associatedGradedGrading r) (y : Γ(relationGradedPiece φ n, U)) :
    (a : I.associatedGraded) • DirectSum.of (fun k => Γ(relationGradedPiece φ k, U)) n y =
      DirectSum.of (fun k => Γ(relationGradedPiece φ k, U)) (r + n)
        ((relationGradedHomogeneousAction f I φ r n a).app U y) := by
  let := formalGradedSectionAlgebra f U
  let : Semiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
    Algebra.TensorProduct.instSemiring (R := A) (A := Γ(X, U)) (B := I.associatedGraded)
  let : NonAssocSemiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
    (inferInstance : Semiring (Γ(X, U) ⊗[A] I.associatedGraded)).toNonAssocSemiring
  apply relationGradedTotalInclusion_injective f I U φ
  rw [relationGradedExternalModule_inclusion]
  rw [relationGradedTotalInclusion_of, relationGradedTotalInclusion_of,
    I.associatedGradedExternalModule_smul]
  apply congrArg (DirectSum.of (fun k => Γ(P.gradedPiece k, U)) (r + n))
  change (formalGradedHomogeneousAction f I P r n a).app U
    ((relationGradedι f I φ n).app U y) = _
  have h := congrArg (fun k => k.app U y)
    (relationGradedHomogeneousAction_ι f I φ r n a)
  simpa only [Modules.Hom.comp_app, ConcreteCategory.comp_apply] using h.symm

end AlgebraicGeometry.Scheme.Cohomology
