/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Module.MatrixBaseChange
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Actual finite matrix presentations for explicit scalar extensions

The standard finite-Pi tensor comparison retains each explicit scalar map, original
inclusion/retraction and mapped projector. Rectangular matrices of a given overlap
isomorphism satisfy the actual projector identities even when the two scalar maps differ.
-/

/-!
Source: `quillen-k-theory/Quillen/Aglib/Algebra/Category/ModuleCat/FiniteMatrixBaseChange.lean`
from the supplied frozen Quillen snapshot.
SHA-256: `7918b0c8c74d651f952deefbdf46c563698bd1137f0392076381ee6d2bff9fe2`.
Only native objects, maps and mathematical namespaces are used in this extraction.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped TensorProduct Matrix ChangeOfRings
universe u v
namespace ModuleCat
variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)

/-- The standard finite-Pi tensor isomorphism for the actual explicit extension functor. -/
def extendScalarsPiIso (n : ℕ) :
    (extendScalars φ).obj (ModuleCat.of R (Fin n → R)) ≅ ModuleCat.of S (Fin n → S) := by
  letI : Algebra R S := φ.toAlgebra
  exact (TensorProduct.piScalarRight R S S (Fin n)).toModuleIso

/-- The actual finite-free comparison retains the specified ring map on pure tensors. -/
theorem extendScalarsPiIso_tmul (n : ℕ) (a : S) (x : Fin n → R) (j : Fin n) :
    (extendScalarsPiIso φ n).hom (a ⊗ₜ[R,φ] x) j = φ (x j) * a := by
  let : Algebra R S := φ.toAlgebra
  exact TensorProduct.piScalarRight_tmul_apply S a x j

/-- The original extension-functor map becomes the coefficientwise mapped matrix. -/
theorem extendScalarsPiIso_map {m n : ℕ} (f : (Fin n → R) →ₗ[R] (Fin m → R)) :
    (extendScalars φ).map (ModuleCat.ofHom f) ≫ (extendScalarsPiIso φ m).hom =
      (extendScalarsPiIso φ n).hom ≫
        ModuleCat.ofHom ((LinearMap.toMatrix' f).map φ).mulVecLin := by
  let : Algebra R S := φ.toAlgebra
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  exact TensorProduct.piScalarRight_toMatrix S f z

end ModuleCat

namespace ModuleCat
open Module.Projective
variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
variable {M : ModuleCat.{u} R} {n : ℕ}

/-- The original finite-free inclusion under the explicit scalar-extension functor. -/
def extendScalarsInclusion (i : M →ₗ[R] Fin n → R) :
    (extendScalars φ).obj M ⟶ ModuleCat.of S (Fin n → S) :=
  (extendScalars φ).map (ModuleCat.ofHom i) ≫ (extendScalarsPiIso φ n).hom

/-- The original finite-free retraction under the explicit scalar-extension functor. -/
def extendScalarsRetraction (r : (Fin n → R) →ₗ[R] M) :
    ModuleCat.of S (Fin n → S) ⟶ (extendScalars φ).obj M :=
  (extendScalarsPiIso φ n).inv ≫ (extendScalars φ).map (ModuleCat.ofHom r)

/-- The explicit extension functor preserves the original inclusion/retraction identity. -/
theorem extendScalars_retraction (i : M →ₗ[R] Fin n → R) (r : (Fin n → R) →ₗ[R] M)
    (h : r.comp i = LinearMap.id) :
    (extendScalarsRetraction φ r).hom.comp (extendScalarsInclusion φ i).hom = LinearMap.id := by
  let : Algebra R S := φ.toAlgebra
  exact baseChange_split S i r h

/-- The actual extended projector is the original matrix mapped by the specified ring
homomorphism. -/
theorem extendScalars_retractMatrix (i : M →ₗ[R] Fin n → R) (r : (Fin n → R) →ₗ[R] M) :
    retractMatrix (extendScalarsInclusion φ i).hom (extendScalarsRetraction φ r).hom =
      (retractMatrix i r).map φ := by
  let : Algebra R S := φ.toAlgebra
  exact baseChange_retractMatrix S i r

end ModuleCat

namespace ModuleCat
open Module.Projective
variable {A S : Type u} [CommRing A] [CommRing S] (φ : A →+* S)
variable (M : ModuleCat.{u} A) {n : ℕ}

/-- The actual scalar-extended module is the image of its original mapped projector. -/
def extendScalarsRetractImageIso (i : M →ₗ[A] Fin n → A) (r : (Fin n → A) →ₗ[A] M)
    (h : r.comp i = LinearMap.id) :
    (extendScalars φ).obj M ≅ ModuleCat.of S
      (LinearMap.range ((retractMatrix i r).map φ).mulVecLin) :=
  ((retractMatrixImageIso (extendScalarsInclusion φ i).hom (extendScalarsRetraction φ r).hom
      (extendScalars_retraction φ i r h)).trans
    (LinearEquiv.ofEq _ _ (congrArg (fun p : Matrix (Fin n) (Fin n) S =>
      LinearMap.range p.mulVecLin) (extendScalars_retractMatrix φ i r)))).toModuleIso

/-- The image comparison retains the original extended inclusion on every element. -/
theorem extendScalarsRetractImageIso_apply
    (i : M →ₗ[A] Fin n → A) (r : (Fin n → A) →ₗ[A] M)
    (h : r.comp i = LinearMap.id) (x : (extendScalars φ).obj M) :
    ((extendScalarsRetractImageIso φ M i r h).hom x).val = extendScalarsInclusion φ i x := rfl

end ModuleCat

namespace ModuleCat
open Module.Projective
variable {A B S : Type u} [CommRing A] [CommRing B] [CommRing S]
variable (φ : A →+* S) (ψ : B →+* S)
variable {M : ModuleCat.{u} A} {N : ModuleCat.{u} B} {m n : ℕ}

/-- The rectangular matrix of the given overlap isomorphism for two explicit scalar maps. -/
def extensionTransitionMatrix (i : M →ₗ[A] Fin m → A) (s : (Fin n → B) →ₗ[B] N)
    (e : (extendScalars ψ).obj N ≅ (extendScalars φ).obj M) : Matrix (Fin m) (Fin n) S :=
  transitionMatrix (extendScalarsInclusion φ i).hom (extendScalarsRetraction ψ s).hom
    e.toLinearEquiv

/-- The matrix and the original overlap isomorphism agree on the actual included module. -/
theorem extensionTransitionMatrix_inclusion
    (i : M →ₗ[A] Fin m → A) (j : N →ₗ[B] Fin n → B) (s : (Fin n → B) →ₗ[B] N)
    (hs : s.comp j = LinearMap.id)
    (e : (extendScalars ψ).obj N ≅ (extendScalars φ).obj M) (y : (extendScalars ψ).obj N) :
    extensionTransitionMatrix φ ψ i s e *ᵥ extendScalarsInclusion ψ j y =
      extendScalarsInclusion φ i (e.hom y) :=
  transitionMatrix_inclusion _ _ _ _ (extendScalars_retraction ψ j s hs) y

/-- Opposite original overlap maps compose to the literal positive mapped projector. -/
theorem extensionTransitionMatrix_mul_inverse
    (i : M →ₗ[A] Fin m → A) (r : (Fin m → A) →ₗ[A] M)
    (j : N →ₗ[B] Fin n → B) (s : (Fin n → B) →ₗ[B] N)
    (hs : s.comp j = LinearMap.id)
    (e : (extendScalars ψ).obj N ≅ (extendScalars φ).obj M) :
    extensionTransitionMatrix φ ψ i s e * extensionTransitionMatrix ψ φ j r e.symm =
      (retractMatrix i r).map φ := by
  rw [← extendScalars_retractMatrix φ i r]
  exact transitionMatrix_mul_inverse _ _ _ _ _ (extendScalars_retraction ψ j s hs)

/-- The target mapped projector fixes the actual overlap transition matrix. -/
theorem mappedProjector_mul_extensionTransition
    (i : M →ₗ[A] Fin m → A) (r : (Fin m → A) →ₗ[A] M)
    (s : (Fin n → B) →ₗ[B] N) (hr : r.comp i = LinearMap.id)
    (e : (extendScalars ψ).obj N ≅ (extendScalars φ).obj M) :
    (retractMatrix i r).map φ * extensionTransitionMatrix φ ψ i s e =
      extensionTransitionMatrix φ ψ i s e := by
  rw [← extendScalars_retractMatrix φ i r]
  exact retractMatrix_mul_transition _ _ _ _ (extendScalars_retraction φ i r hr)

/-- The actual overlap transition matrix factors through the source mapped projector. -/
theorem extensionTransition_mul_mappedProjector
    (i : M →ₗ[A] Fin m → A) (j : N →ₗ[B] Fin n → B) (s : (Fin n → B) →ₗ[B] N)
    (hs : s.comp j = LinearMap.id)
    (e : (extendScalars ψ).obj N ≅ (extendScalars φ).obj M) :
    extensionTransitionMatrix φ ψ i s e * (retractMatrix j s).map ψ =
      extensionTransitionMatrix φ ψ i s e := by
  rw [← extendScalars_retractMatrix ψ j s]
  exact transitionMatrix_mul_retract _ _ _ _ (extendScalars_retraction ψ j s hs)

end ModuleCat
