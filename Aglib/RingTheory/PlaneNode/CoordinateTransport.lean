/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.PlaneNode.Basic
public import Aglib.RingTheory.AdjoinRoot.BivariateTensor
public import Mathlib.RingTheory.RingHom.Etale

/-!
Source: node-algebra part of
`R5Lab.AlgebraicGeometry.Curves.LocalModels.PointedResolution.Nodal.CoordinateTransport`.
R5 packet revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`1653a07650513593b903cc7b5db4793870399c969bebf70aa4ca0c159c759984`.
The original commutative-ring hypotheses and coefficient/scaling maps are
retained; no geometric blowup identification or existence is asserted.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Polynomial
open scoped Polynomial.Bivariate TensorProduct
universe u
namespace PlaneNode
variable {R : Type u} [CommRing R]
variable (S : Type u) [CommRing S] [Algebra R S]

/-- The same literal tensor comparison for a node parameter. -/
def tensorEquiv (c : R) :
    S ⊗[R] Ring c ≃ₐ[S] Ring (algebraMap R S c) :=
  AdjoinRoot.bivariateTensorEquiv (poly c) (poly (algebraMap R S c)) (by
    simp [poly])

/-- The map of node algebras induced by extension of coefficients from `R` to `S`. -/
def coefficientMap (c : R) :
    Ring c →ₐ[R] Ring (algebraMap R S c) :=
  ((tensorEquiv S c).toAlgHom.restrictScalars R).comp
    Algebra.TensorProduct.includeRight

@[simp] theorem coefficientMap_U (c : R) :
    coefficientMap S c (U c) = U (algebraMap R S c) := by
  change (tensorEquiv S c) (1 ⊗ₜ[R] U c) = _
  unfold tensorEquiv AdjoinRoot.bivariateTensorEquiv
  rw [AlgEquiv.trans_apply]
  rw [show U c = AdjoinRoot.of _ X from rfl, AdjoinRoot.tensorAlgEquiv_of]
  rw [AdjoinRoot.coe_mapAlgEquiv, AdjoinRoot.map_of]
  simp [U, AdjoinRoot.algebraMap_eq]


@[simp] theorem coefficientMap_V (c : R) :
    coefficientMap S c (V c) = V (algebraMap R S c) := by
  change (tensorEquiv S c) (1 ⊗ₜ[R] V c) = _
  unfold tensorEquiv AdjoinRoot.bivariateTensorEquiv
  rw [AlgEquiv.trans_apply]
  rw [AdjoinRoot.tensorAlgEquiv_root]
  rw [AdjoinRoot.coe_mapAlgEquiv, AdjoinRoot.map_root]


theorem coefficientMap_etale [Algebra.Etale R S] (c : R) :
    (coefficientMap S c).toRingHom.Etale := by
  let e := Algebra.TensorProduct.comm R S (Ring c)
  have hi : (Algebra.TensorProduct.includeRight :
      Ring c →ₐ[R] S ⊗[R] Ring c).toRingHom.Etale := by
    have hl : (algebraMap (Ring c) (Ring c ⊗[R] S)).Etale :=
      RingHom.etale_algebraMap.mpr inferInstance
    exact RingHom.Etale.stableUnderComposition _ _ hl
      (RingHom.Etale.of_bijective (f := e.symm.toRingHom) e.symm.bijective)
  exact RingHom.Etale.stableUnderComposition _ _ hi
    (RingHom.Etale.of_bijective (f := (tensorEquiv S c).toRingHom)
      (tensorEquiv S c).bijective)

variable {S} in
/-- The node-algebra equivalence induced by an equality of the defining coefficients. -/
def congr {c d : S} (h : c = d) : Ring c ≃ₐ[S] Ring d := by
  subst d
  exact AlgEquiv.refl

variable {S} in
@[simp] theorem congr_U {c d : S} (h : c = d) :
    congr h (U c) = U d := by subst d; rfl
variable {S} in
@[simp] theorem congr_V {c d : S} (h : c = d) :
    congr h (V c) = V d := by subst d; rfl
variable {S} in
@[simp] theorem congr_symm_U {c d : S} (h : c = d) :
    (congr h).symm (U d) = U c := by subst d; rfl
variable {S} in
@[simp] theorem congr_symm_V {c d : S} (h : c = d) :
    (congr h).symm (V d) = V c := by subst d; rfl

variable {S} in
/-- The node-algebra equivalence obtained when the defining coefficients differ by the specified
unit factor. -/
def scaledEquiv (c : S) (a : Sˣ) (d : S) (h : d = (a : S) * c) :
    Ring d ≃ₐ[S] Ring c :=
  (congr h).trans (unitScale c a)

variable {S} in
@[simp] theorem scaledEquiv_symm_U (c : S) (a : Sˣ) (d : S) (h) :
    (scaledEquiv c a d h).symm (U c) =
      algebraMap S _ (↑a⁻¹ : S) * U d := by
  simp [scaledEquiv, unitScale, unscaleHom, AlgEquiv.symm_trans_apply]

variable {S} in
@[simp] theorem scaledEquiv_symm_V (c : S) (a : Sˣ) (d : S) (h) :
    (scaledEquiv c a d h).symm (V c) = V d := by
  simp [scaledEquiv, unitScale, unscaleHom, AlgEquiv.symm_trans_apply]


end PlaneNode
