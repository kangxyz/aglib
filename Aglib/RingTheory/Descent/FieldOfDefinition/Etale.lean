/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Descent.FieldOfDefinition.Presentation

/-!
# Finite and étale properties of the actual finite-field model

This supplies finite and étale properties for
`Algebra.Descent.FieldOfDefinition.finitePresentationModel`.
The coefficient homomorphism is the actual tensor product of the inclusion of
an intermediate field. No injectivity or Noetherian hypothesis is imposed on R.

## Extraction basis

Transferred from `R5Lab.RingTheory.Descent.FieldObjectProperties` at source revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`, SHA-256
`472a68131c346a7bc316954adff365ab339cadd2eb87ef0d897d8cd4230c394b`.
The source interface retains its objects, maps and assumptions under native
mathematical declaration namespaces.
-/

@[expose] public section

open _root_.TensorProduct
noncomputable section

namespace Algebra.Descent.FieldOfDefinition

section FaithfullyFlatTensor

variable {K : Type*} [CommRing K] (R : Type*) [CommRing R] [Algebra K R]
  {E Ω : Type*} [CommRing E] [CommRing Ω] [Algebra K E] [Algebra K Ω]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- Faithful flatness of the actual tensor map; the proof uses the canonical
iterated-base-change equivalence, with its scalar compatibility retained. -/
lemma faithfullyFlat_lTensor (f : E →ₐ[K] Ω) (hf : f.toRingHom.FaithfullyFlat) :
    (Algebra.TensorProduct.lTensor (S := R) R f).toRingHom.FaithfullyFlat := by
  algebraize [f.toRingHom, (Algebra.TensorProduct.lTensor (S := R) R f).toRingHom]
  let e : R ⊗[K] Ω ≃ₐ[R ⊗[K] E] (R ⊗[K] E) ⊗[E] Ω :=
    { __ := (Algebra.IsPushout.cancelBaseChangeAlg _ _ _ _ _).symm,
      commutes' x := congr($(Algebra.IsPushout.cancelBaseChange_symm_comp_lTensor K E Ω R) x) }
  exact Module.FaithfullyFlat.of_linearEquiv _ _ e.toLinearEquiv

end FaithfullyFlatTensor

universe u

variable (K Ω R : Type u) [Field K] [Field Ω] [Algebra K Ω]
  [CommRing R] [Algebra K R]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
instance stage_faithfullyFlat (s : Finset Ω) :
    Module.FaithfullyFlat (stageRing K Ω R s) (R ⊗[K] Ω) := by
  change RingHom.FaithfullyFlat (R := stageRing K Ω R s) (S := R ⊗[K] Ω)
    (stageMap K Ω R s).toRingHom
  apply faithfullyFlat_lTensor R
  change (algebraMap (stageField K Ω s) Ω).FaithfullyFlat
  rw [RingHom.faithfullyFlat_algebraMap_iff]
  infer_instance

variable (B : Type u) [CommRing B] [Algebra (R ⊗[K] Ω) B]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
instance FPModel.module (M : FPModel K Ω R B) :
    Module (stageRing K Ω R M.stage) M.Model := M.algebra.toModule

instance FPModel.finite (M : FPModel K Ω R B) [Module.Finite (R ⊗[K] Ω) B] :
    Module.Finite (stageRing K Ω R M.stage) M.Model := by
  let : Module.Finite (R ⊗[K] Ω)
      ((R ⊗[K] Ω) ⊗[stageRing K Ω R M.stage] M.Model) :=
    Module.Finite.equiv M.equiv.symm.toLinearEquiv
  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat
    (R := stageRing K Ω R M.stage) (M := M.Model) (R ⊗[K] Ω)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
instance FPModel.etale (M : FPModel K Ω R B) [Algebra.Etale (R ⊗[K] Ω) B] :
    Algebra.Etale (stageRing K Ω R M.stage) M.Model := by
  let : Algebra.Etale (R ⊗[K] Ω)
      ((R ⊗[K] Ω) ⊗[stageRing K Ω R M.stage] M.Model) :=
    Algebra.Etale.of_equiv M.equiv.symm
  exact Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat (R ⊗[K] Ω)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- An actual finite étale algebra model at a finite intermediate field, including
its base-change equivalence. The field stage need not be separable over K. -/
structure FiniteEtaleModel [Algebra.IsAlgebraic K Ω] extends FPModel K Ω R B where
  [finite : @Module.Finite (stageRing K Ω R stage) Model
    _ _ toFPModel.algebra.toModule]
  [etale : Algebra.Etale (stageRing K Ω R stage) Model]

attribute [instance] FiniteEtaleModel.finite FiniteEtaleModel.etale

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Finite étale algebras over `R ⊗[K] Ω` descend as actual algebra objects to
an actual finite intermediate field of the algebraic extension Ω/K. -/
def finiteEtaleModel [Algebra.IsAlgebraic K Ω]
    [Module.Finite (R ⊗[K] Ω) B] [Algebra.Etale (R ⊗[K] Ω) B] :
    FiniteEtaleModel K Ω R B :=
  { toFPModel := finitePresentationModel K Ω R B }

end Algebra.Descent.FieldOfDefinition
