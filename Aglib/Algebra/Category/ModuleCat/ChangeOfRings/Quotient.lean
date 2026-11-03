/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Algebra
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Original quotient source under scalar extension

The native quotient-tensor comparison preserves unit tensors and composes
through the actual scalar-extension associator and equality of mapped ideals.
No new quotient object or independently chosen comparison is introduced.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory TensorProduct
open scoped TensorProduct ModuleCat.Algebra ChangeOfRings

universe u

namespace ModuleCat

/-- The original quotient-source comparison retains the scalar unit. -/
theorem quotientScalarExtensionIso_one_tmul
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (r : R) :
    ((ModuleCat.extendScalarsAlgebraObjIso R S (ModuleCat.of R (R ⧸ I)) ≪≫
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).symm.toLinearEquiv.toModuleIso).hom)
        ((1 : S) ⊗ₜ[R,algebraMap R S] (Ideal.Quotient.mk I r)) =
      Ideal.Quotient.mk (I.map (algebraMap R S)) (algebraMap R S r) := by
  change (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).symm
    ((ModuleCat.extendScalarsAlgebraObjIso R S (ModuleCat.of R (R ⧸ I))).hom
      ((1 : S) ⊗ₜ[R,algebraMap R S] (Ideal.Quotient.mk I r))) = _
  rw [ModuleCat.extendScalarsAlgebraObjIso_hom_tmul,
    Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul]
  simp only [Algebra.smul_def, mul_one]
  rfl

/-- The native quotient-source square for two scalar extensions, with the
actual iterated-ideal comparison rather than a chosen quotient isomorphism. -/
theorem quotientScalarExtensionIso_comp
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (φ : R →+* S) (ψ : S →+* T) (I : Ideal R) :
    letI : Algebra R S := φ.toAlgebra
    letI : Algebra S T := ψ.toAlgebra
    letI : Algebra R T := (ψ.comp φ).toAlgebra
    let qRS := ModuleCat.extendScalarsAlgebraObjIso R S (ModuleCat.of R (R ⧸ I)) ≪≫
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).symm.toLinearEquiv.toModuleIso
    let qST := ModuleCat.extendScalarsAlgebraObjIso S T
        (ModuleCat.of S (S ⧸ I.map φ)) ≪≫
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot T
        (I.map φ)).symm.toLinearEquiv.toModuleIso
    let qRT := ModuleCat.extendScalarsAlgebraObjIso R T (ModuleCat.of R (R ⧸ I)) ≪≫
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot T I).symm.toLinearEquiv.toModuleIso
    qRT.hom = (ModuleCat.extendScalarsComp φ ψ).hom.app (ModuleCat.of R (R ⧸ I)) ≫
      (ModuleCat.extendScalars ψ).map qRS.hom ≫ qST.hom ≫
      (Ideal.quotientEquivAlgOfEq T
        (Ideal.map_map (I := I) φ ψ)).toLinearEquiv.toModuleIso.hom := by
  let : Algebra R S := φ.toAlgebra
  let : Algebra S T := ψ.toAlgebra
  let : Algebra R T := (ψ.comp φ).toAlgebra
  dsimp only
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [ConcreteCategory.comp_apply]
  let qRS := ModuleCat.extendScalarsAlgebraObjIso R S (ModuleCat.of R (R ⧸ I)) ≪≫
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).symm.toLinearEquiv.toModuleIso
  let qST := ModuleCat.extendScalarsAlgebraObjIso S T
      (ModuleCat.of S (S ⧸ I.map φ)) ≪≫
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot T
      (I.map φ)).symm.toLinearEquiv.toModuleIso
  let c := (Ideal.quotientEquivAlgOfEq T
    (Ideal.map_map (I := I) φ ψ)).toLinearEquiv.toModuleIso.hom
  have hRS := quotientScalarExtensionIso_one_tmul (S := S) I r
  have hST := quotientScalarExtensionIso_one_tmul (S := T) (I.map φ) (φ r)
  have hRT := quotientScalarExtensionIso_one_tmul (S := T) I r
  have hcomp := ModuleCat.extendScalarsComp_hom_app_one_tmul φ ψ
    (ModuleCat.of R (R ⧸ I)) (Ideal.Quotient.mk I r)
  have hmap := ModuleCat.ExtendScalars.map_tmul ψ qRS.hom (1 : T)
    ((1 : S) ⊗ₜ[R,φ] Ideal.Quotient.mk I r)
  have h₁ := congrArg
    (fun x : (ModuleCat.extendScalars ψ).obj
        ((ModuleCat.extendScalars φ).obj (ModuleCat.of R (R ⧸ I))) =>
      c (qST.hom ((ModuleCat.extendScalars ψ).map qRS.hom x))) hcomp
  have h₂ := congrArg
    (fun x : (ModuleCat.extendScalars ψ).obj (ModuleCat.of S (S ⧸ I.map φ)) =>
      c (qST.hom x)) hmap
  have h₃ := congrArg
    (fun x : S ⧸ I.map φ => c (qST.hom ((1 : T) ⊗ₜ[S,ψ] x))) hRS
  have h₄ := congrArg
    (fun x : T ⧸ (I.map φ).map ψ => c x) hST
  have h₅ := Ideal.quotientEquivAlgOfEq_mk T
    (Ideal.map_map (I := I) φ ψ) (ψ (φ r))
  exact hRT.trans (h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))).symm

/-- Inverting an original composite isolates its source comparison. -/
private theorem sourceInverse_of_comp
    {C : Type*} [Category C] {A B D E F : C}
    (q : A ≅ F) (c : A ≅ B) (d : B ≅ D) (e : D ≅ E) (t : E ≅ F)
    (h : q.hom = c.hom ≫ d.hom ≫ e.hom ≫ t.hom) :
    q.inv ≫ c.hom = t.inv ≫ e.inv ≫ d.inv := by
  apply (q.inv_comp_eq).2
  rw [h]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

/-- The original inverse quotient sources compose through the native scalar
associator and the same mapped-ideal isomorphism. -/
theorem quotientScalarExtensionIso_inv_comp
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (φ : R →+* S) (ψ : S →+* T) (I : Ideal R) :
    letI : Algebra R S := φ.toAlgebra
    letI : Algebra S T := ψ.toAlgebra
    letI : Algebra R T := (ψ.comp φ).toAlgebra
    let qRS := ModuleCat.extendScalarsAlgebraObjIso R S (ModuleCat.of R (R ⧸ I)) ≪≫
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).symm.toLinearEquiv.toModuleIso
    let qST := ModuleCat.extendScalarsAlgebraObjIso S T
        (ModuleCat.of S (S ⧸ I.map φ)) ≪≫
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot T
        (I.map φ)).symm.toLinearEquiv.toModuleIso
    let qRT := ModuleCat.extendScalarsAlgebraObjIso R T (ModuleCat.of R (R ⧸ I)) ≪≫
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot T I).symm.toLinearEquiv.toModuleIso
    qRT.inv ≫ (ModuleCat.extendScalarsComp φ ψ).hom.app (ModuleCat.of R (R ⧸ I)) =
      (Ideal.quotientEquivAlgOfEq T
        (Ideal.map_map (I := I) φ ψ)).toLinearEquiv.toModuleIso.inv ≫
      qST.inv ≫ (ModuleCat.extendScalars ψ).map qRS.inv := by
  let : Algebra R S := φ.toAlgebra
  let : Algebra S T := ψ.toAlgebra
  let : Algebra R T := (ψ.comp φ).toAlgebra
  dsimp only
  let qRS := ModuleCat.extendScalarsAlgebraObjIso R S (ModuleCat.of R (R ⧸ I)) ≪≫
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).symm.toLinearEquiv.toModuleIso
  let qST := ModuleCat.extendScalarsAlgebraObjIso S T
      (ModuleCat.of S (S ⧸ I.map φ)) ≪≫
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot T
      (I.map φ)).symm.toLinearEquiv.toModuleIso
  let qRT := ModuleCat.extendScalarsAlgebraObjIso R T (ModuleCat.of R (R ⧸ I)) ≪≫
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot T I).symm.toLinearEquiv.toModuleIso
  let eI := (Ideal.quotientEquivAlgOfEq T
    (Ideal.map_map (I := I) φ ψ)).toLinearEquiv.toModuleIso
  have h := quotientScalarExtensionIso_comp φ ψ I
  exact sourceInverse_of_comp qRT
    ((ModuleCat.extendScalarsComp φ ψ).app (ModuleCat.of R (R ⧸ I)))
    ((ModuleCat.extendScalars ψ).mapIso qRS) qST eI h

end ModuleCat
