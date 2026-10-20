/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Module.CommutingAutomorphisms.SupportNaturality
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.RingTheory.TensorProduct.MonoidAlgebra
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Actual flat base change of the Laurent annihilator

The endomorphism comparison is constructed from finite projective tensor-Hom
contraction. Its injectivity and exactness of tensoring by a flat algebra prove
the kernel equality. The desired support equation is not a premise.
-/
/-!
## Migration source

Native extraction from `lean/R5Lab/Aglib/Algebra/Module/CommutingAutomorphisms/FlatSupport.lean` at
R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`fc37e6e417fd7373c496fb9253635ec617c3394763f88369429e472b1542ec91`.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped _root_.TensorProduct
open _root_.TensorProduct
namespace Module.CommutingAutomorphisms.LaurentSupport
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- The actual endomorphism comparison for the original finite projective module. -/
def endScalarEquiv (X : Object R) :
    S ⊗[R] Module.End R X.carrier ≃ₗ[R] Module.End S (S ⊗[R] X.carrier) :=
  (lTensorHomEquivHomLTensor R X.carrier S X.carrier).trans
    ((LinearMap.liftBaseChangeEquiv S).restrictScalars R)

@[simp] theorem endScalarEquiv_tmul (X : Object R) (s : S) (f : Module.End R X.carrier) :
    endScalarEquiv (S := S) X (s ⊗ₜ[R] f) = s • f.baseChange S := by
  ext x
  change (LinearMap.liftBaseChange S
    (lTensorHomEquivHomLTensor R X.carrier S X.carrier (s ⊗ₜ[R] f)))
      (1 ⊗ₜ[R] x) = s • (1 ⊗ₜ[R] f x)
  rw [LinearMap.liftBaseChange_tmul]
  simp only [lTensorHomEquivHomLTensor_apply, lTensorHomToHomLTensor_apply, one_smul]
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- The finite-projective endomorphism comparison pastes with the actual
Laurent-coefficient square and the canonical torus tensor equivalence. -/
theorem representation_tensor_baseChange (X : Object R) (z : S ⊗[R] Laurent R) :
    endScalarEquiv X (AlgebraTensorModule.lTensor S S (representation X).toLinearMap z) =
      representation (X.baseChange S) (MonoidAlgebra.scalarTensorEquiv R S z) := by
  induction z using TensorProduct.inductionOn with
  | tmul s p =>
    change endScalarEquiv X (s ⊗ₜ[R] representation X p) = _
    rw [endScalarEquiv_tmul, MonoidAlgebra.scalarTensorEquiv_tmul, map_smul]
    congr 1
    exact (representation_baseChange X p).symm
  | add z w hz hw => simp only [map_add, hz, hw]

/-- The tensor image of every original annihilator lies in the extended ideal. -/
theorem tensor_kernel_mem_map (X : Object R)
    (w : S ⊗[R] LinearMap.ker (representation X).toLinearMap) :
    MonoidAlgebra.scalarTensorEquiv R S
      (AlgebraTensorModule.lTensor S S (LinearMap.ker (representation X).toLinearMap).subtype w) ∈
      (supportIdeal X).map (coefficientMap (algebraMap R S)) := by
  induction w using TensorProduct.inductionOn with
  | tmul s p =>
    change MonoidAlgebra.scalarTensorEquiv R S (s ⊗ₜ[R] (p : Laurent R)) ∈ _
    rw [MonoidAlgebra.scalarTensorEquiv_tmul]
    rw [Algebra.smul_def]
    apply Ideal.mul_mem_left
    exact Ideal.mem_map_of_mem _ p.property
  | add z w hz hw =>
    simp only [map_add]
    exact Ideal.add_mem _ hz hw

/-- Flat extension commutes with the ACTUAL annihilator ideal. -/
theorem supportIdeal_baseChange [Module.Flat R S] (X : Object R) :
    supportIdeal (X.baseChange S) = (supportIdeal X).map (coefficientMap (algebraMap R S)) := by
  apply le_antisymm
  · intro p hp
    change representation (X.baseChange S) p = 0 at hp
    let z := (MonoidAlgebra.scalarTensorEquiv R S).symm p
    have hz : z ∈ LinearMap.ker
        (AlgebraTensorModule.lTensor S S (representation X).toLinearMap) := by
      change AlgebraTensorModule.lTensor S S (representation X).toLinearMap z = 0
      apply (endScalarEquiv X).injective
      rw [map_zero, representation_tensor_baseChange]
      simpa only [z, AlgEquiv.apply_symm_apply] using hp
    rw [Module.Flat.ker_lTensor_eq] at hz
    obtain ⟨w, hw⟩ := hz
    have hmem := tensor_kernel_mem_map X w
    rw [hw] at hmem
    simpa only [z, AlgEquiv.apply_symm_apply] using hmem
  · exact Ideal.map_le_iff_le_comap.mpr (supportIdeal_map_le X)

/-- The torus tensor equivalence restricts to the literal coefficient map. -/
theorem scalarTensorEquiv_includeRight :
    (MonoidAlgebra.scalarTensorEquiv R S (M := Character)).toRingHom.comp
      Algebra.TensorProduct.includeRight.toRingHom = coefficientMap (algebraMap R S) := by
  apply RingHom.ext
  intro p
  change MonoidAlgebra.scalarTensorEquiv R S (1 ⊗ₜ[R] p) = coefficientMap (algebraMap R S) p
  rw [MonoidAlgebra.scalarTensorEquiv_tmul, one_smul]
  rfl

/-- The ACTUAL support algebra commutes with flat scalar extension. -/
def supportBaseChangeEquiv [Module.Flat R S] (X : Object R) :
    S ⊗[R] Support X ≃ₐ[S] Support (X.baseChange S) :=
  (Algebra.TensorProduct.tensorQuotientEquiv (R := R) S (Laurent R) S (supportIdeal X)).trans
    (Ideal.quotientEquivAlg _ _ (MonoidAlgebra.scalarTensorEquiv R S)
      (by
        have hmap := Ideal.map_map (I := supportIdeal X)
          (Algebra.TensorProduct.includeRight : Laurent R →ₐ[R] S ⊗[R] Laurent R).toRingHom
          (MonoidAlgebra.scalarTensorEquiv R S (M := Character)).toRingHom
        have hcoeff := congrArg (fun f : Laurent R →+* Laurent S => (supportIdeal X).map f)
          (scalarTensorEquiv_includeRight (R := R) (S := S))
        exact (supportIdeal_baseChange X).trans (hmap.trans hcoeff).symm))

@[simp] theorem supportBaseChangeEquiv_tmul_mk [Module.Flat R S] (X : Object R)
    (s : S) (p : Laurent R) :
    supportBaseChangeEquiv X (s ⊗ₜ[R] Ideal.Quotient.mk (supportIdeal X) p) =
      Ideal.Quotient.mk (supportIdeal (X.baseChange S))
        (s • coefficientMap (algebraMap R S) p) := by
  change Ideal.Quotient.mk (supportIdeal (X.baseChange S))
      (MonoidAlgebra.scalarTensorEquiv R S (s ⊗ₜ[R] p)) = _
  rw [MonoidAlgebra.scalarTensorEquiv_tmul]
  rfl

end Module.CommutingAutomorphisms.LaurentSupport
