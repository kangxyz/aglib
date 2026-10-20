/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.FiniteEtale.TorsorExtension
public import Mathlib.RingTheory.HopfAlgebra.TensorProduct

/-!
# The literal generic coefficient Hopf algebra

Supporting K2-018#prop:k2018-arithmetic-characters at
 e73d98b1b5c1e5abcdebf7d058e436d792b87982. These identities compare the actual
Mathlib Hopf structure on K ⊗[R] H with the exact BaseChange.counit/BaseChange.comul
used in OriginalTorsorData. They supply no torsor or final class equality.
-/

/-!
Extraction source: `R5Lab.Aglib.RingTheory.IntegralClosure.FiniteEtale.GenericCoefficientHopf`,
R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`e731b42e078fd161cfbc99cd6076d42b570b1572a4ca105cfb58a8c29989113b`.
Historical source locators retain their original basis. -/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct
open Algebra.TensorProduct
open Algebra.FiniteEtale.GenericMaps Algebra.FiniteEtale.TorsorExtension

namespace Algebra.FiniteEtale.TensorHopf
universe u
variable (R K H : Type u) [CommRing R] [Field K] [Algebra R K]
  [CommRing H] [HopfAlgebra R H]

/-- The actual scalar-extended Hopf counit is the existing literal generic counit. -/
theorem tensor_counit_eq_generic :
    Bialgebra.counitAlgHom K (K ⊗[R] H) = BaseChange.counit R K (Bialgebra.counitAlgHom R H) := by
  rw [Bialgebra.TensorProduct.counitAlgHom_def, Bialgebra.counitAlgHom_self]
  rfl

/-- The actual scalar-extended Hopf comultiplication is the existing literal
generic comultiplication, through the canonical generic tensor comparison. -/
theorem tensor_comul_eq_generic :
    Bialgebra.comulAlgHom K (K ⊗[R] H) = BaseChange.comul R K (Bialgebra.comulAlgHom R H) := by
  apply Algebra.TensorProduct.ext'
  intro k h
  apply (BaseChange.tensorEquiv R K (B := H) (H := H)).injective
  change BaseChange.tensorEquiv R K (Coalgebra.comul (R := K) (k ⊗ₜ[R] h)) =
    BaseChange.tensorEquiv R K ((BaseChange.tensorEquiv R K (B := H) (H := H)).symm
      (k ⊗ₜ[R] Coalgebra.comul (R := R) h))
  rw [AlgEquiv.apply_symm_apply, TensorProduct.comul_tmul, CommSemiring.comul_apply]
  generalize Coalgebra.comul (R := R) h = z
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    change BaseChange.tensorEquiv R K (((1 : K) ⊗ₜ[R] a) ⊗ₜ[K] (k ⊗ₜ[R] b)) =
      k ⊗ₜ[R] (a ⊗ₜ[R] b)
    rw [BaseChange.tensorEquiv_tmul, one_mul]
  | add z w hz hw =>
    simp only [TensorProduct.tmul_add, map_add, hz, hw]

variable (A : Type u) [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]

/-- Re-express a DERIVED field coaction using the exact original generic
coefficient maps. Its coaction map itself is unchanged. -/
def originalCoactionOfField
    (α : AlgebraCoaction K A (K ⊗[R] H) (Bialgebra.counitAlgHom K (K ⊗[R] H))
      (Bialgebra.comulAlgHom K (K ⊗[R] H))) :
    OriginalCoaction R K (A := A) (Bialgebra.counitAlgHom R H) (Bialgebra.comulAlgHom R H) where
  coact := α.coact
  counit := by
    rw [← tensor_counit_eq_generic R K H]
    exact α.counit
  coassoc := by
    rw [← tensor_comul_eq_generic R K H]
    exact α.coassoc

/-- The actual field algebra/coaction/point construction supplies these inputs;
this adapter only identifies the fixed generic coefficient maps. -/
def originalTorsorOfField
    (α : AlgebraCoaction K A (K ⊗[R] H) (Bialgebra.counitAlgHom K (K ⊗[R] H))
      (Bialgebra.comulAlgHom K (K ⊗[R] H)))
    (hA : Nontrivial A) (hT : Function.Bijective (transporter K A (K ⊗[R] H) α.coact)) :
    OriginalTorsorData R K A H (Bialgebra.counitAlgHom R H) (Bialgebra.comulAlgHom R H) where
  coaction := originalCoactionOfField R K H A α
  nontrivial := hA
  transporter_bijective := hT

end Algebra.FiniteEtale.TensorHopf
