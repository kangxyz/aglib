/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Algebra.Sections
public import Aglib.AlgebraicGeometry.Modules.Coherent.Algebra.ScalarExtension
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.OpenRestrictionSections
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Algebra
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Sections

/-!
# The canonical affine-open algebra restriction equivalence

The algebra base-change map is constructed from the original section restriction.
Its underlying linear map is the actual `affineOpenRestrictionSectionsIso`,
identified by the original unit-tensor equation. In particular its `includeRight`
map is literally restriction, as required for the native spectrum pullback square.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory Opposite
open scoped MonObj TensorProduct
open scoped AlgebraicGeometry.Scheme.Modules.Algebra

namespace AlgebraicGeometry.Scheme.Modules.Algebra

/-- One abstract packet retains a scalar-extension equivalence and its original restriction. -/
structure ScalarRestrictionData (R S A B : Type*) [CommRing R] [CommRing S]
    [CommRing A] [CommRing B] [Algebra R S] [Algebra R A] [Algebra S B] where
  /-- The actual algebra equivalence from the original scalar extension. -/
  equiv : S ⊗[R] A ≃ₐ[S] B
  /-- The original restriction map recovered by evaluating on right unit tensors. -/
  restriction : A →+* B
  one_tmul : ∀ a, equiv (1 ⊗ₜ[R] a) = restriction a

/-- The complete ring-map relation, with its native instances fixed abstractly. -/
def ScalarRestrictionData.Compatible {R S A B : Type*}
    [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra S B] (d : ScalarRestrictionData R S A B) : Prop :=
  d.equiv.toRingEquiv.toRingHom.comp
    (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := A)).toRingHom = d.restriction

/-- The packet's right-inclusion equation is proved before any concrete sheaf is supplied. -/
theorem ScalarRestrictionData.comp_includeRight {R S A B : Type*}
    [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra S B] (d : ScalarRestrictionData R S A B) :
    d.Compatible := by
  ext a
  exact d.one_tmul a

variable {X : Scheme.{u}} (U V : X.affineOpens) (i : V.val ⟶ U.val)
  (M : X.Modules) [MonObj M] [IsCommMonObj M]

/-- Scalar extension uses the original coordinate-ring restriction. -/
@[instance_reducible]
def affineRestrictionBaseAlgebra : Algebra Γ(X, U) Γ(X, V) :=
  (X.presheaf.map i.op).hom.toAlgebra

/-- The smaller section ring viewed over the larger coordinate ring by original restriction. -/
@[instance_reducible]
def affineRestrictionSectionAlgebra : Algebra Γ(X, U) Γ(M, V) :=
  ((algebraMap Γ(X, V) Γ(M, V)).comp (X.presheaf.map i.op).hom).toAlgebra

/-- The original two scalar maps form the canonical scalar tower. -/
theorem affineRestrictionSectionScalarTower :
    letI := affineRestrictionBaseAlgebra U V i
    letI := affineRestrictionSectionAlgebra U V i M
    IsScalarTower Γ(X, U) Γ(X, V) Γ(M, V) := by
  let hBase := affineRestrictionBaseAlgebra U V i
  let hSection := affineRestrictionSectionAlgebra U V i M
  exact IsScalarTower.of_algebraMap_eq' rfl

/-- The original restriction as an algebra map over the larger coordinate ring. -/
def sectionRestrictionAlgHom :
    letI := affineRestrictionSectionAlgebra U V i M
    Γ(M, U) →ₐ[Γ(X, U)] Γ(M, V) := by
  letI := affineRestrictionSectionAlgebra U V i M
  exact { sectionRestriction M i with commutes' := sectionRestriction_algebraMap M i }

@[simp] theorem sectionRestrictionAlgHom_apply (m : Γ(M, U)) :
    sectionRestrictionAlgHom U V i M m = M.val.map i.op m := rfl

/-- The original affine section comparison, spelled with the ordinary algebra tensor product. -/
def affineRestrictionLinearEquiv [M.IsQuasicoherent] :
    letI := affineRestrictionBaseAlgebra U V i
    Γ(X, V) ⊗[Γ(X, U)] Γ(M, U) ≃ₗ[Γ(X, V)] Γ(M, V) := by
  letI := affineRestrictionBaseAlgebra U V i
  exact ((ModuleCat.extendScalarsAlgebraObjIso Γ(X, U) Γ(X, V)
    (ModuleCat.of Γ(X, U) Γ(M, U))).symm ≪≫
      affineOpenRestrictionSectionsIso U V i M).toLinearEquiv

/-- The original linear comparison retains the actual restriction unit. -/
@[simp] theorem affineRestrictionLinearEquiv_one_tmul [M.IsQuasicoherent] (m : Γ(M, U)) :
    letI := affineRestrictionBaseAlgebra U V i
    affineRestrictionLinearEquiv U V i M (1 ⊗ₜ[Γ(X, U)] m) = M.val.map i.op m := by
  let hBase := affineRestrictionBaseAlgebra U V i
  exact affineOpenRestrictionSectionsIso_one_tmul U V i M m

/-- The canonical algebra scalar-extension equivalence along an affine-open inclusion. -/
def affineRestrictionAlgEquiv [M.IsQuasicoherent] :
    letI := affineRestrictionBaseAlgebra U V i
    Γ(X, V) ⊗[Γ(X, U)] Γ(M, U) ≃ₐ[Γ(X, V)] Γ(M, V) := by
  letI hBase := affineRestrictionBaseAlgebra U V i
  letI hSection := affineRestrictionSectionAlgebra U V i M
  letI hTower := affineRestrictionSectionScalarTower U V i M
  exact baseChangeAlgEquiv (sectionRestrictionAlgHom U V i M)
    (affineRestrictionLinearEquiv U V i M)
    (affineRestrictionLinearEquiv_one_tmul U V i M)

/-- The affine algebra equivalence keeps every original unit tensor. -/
@[simp] theorem affineRestrictionAlgEquiv_one_tmul [M.IsQuasicoherent] (m : Γ(M, U)) :
    letI := affineRestrictionBaseAlgebra U V i
    affineRestrictionAlgEquiv U V i M (1 ⊗ₜ[Γ(X, U)] m) = M.val.map i.op m := by
  let hBase := affineRestrictionBaseAlgebra U V i
  let hSection := affineRestrictionSectionAlgebra U V i M
  let hTower := affineRestrictionSectionScalarTower U V i M
  exact baseChangeAlgEquiv_one_tmul (sectionRestrictionAlgHom U V i M)
    (affineRestrictionLinearEquiv U V i M)
    (affineRestrictionLinearEquiv_one_tmul U V i M) m

/-- The algebra equivalence has the original affine restriction linear map. -/
theorem affineRestrictionAlgEquiv_toLinearEquiv [M.IsQuasicoherent] :
    (affineRestrictionAlgEquiv U V i M).toLinearEquiv =
      affineRestrictionLinearEquiv U V i M := by
  let hBase := affineRestrictionBaseAlgebra U V i
  let hSection := affineRestrictionSectionAlgebra U V i M
  let hTower := affineRestrictionSectionScalarTower U V i M
  exact baseChangeAlgEquiv_toLinearEquiv (sectionRestrictionAlgHom U V i M)
    (affineRestrictionLinearEquiv U V i M)
    (affineRestrictionLinearEquiv_one_tmul U V i M)

/-- Specialize the complete abstract ring-map packet once to original affine sections. -/
def affineRestrictionData [M.IsQuasicoherent] :
    letI := affineRestrictionBaseAlgebra U V i
    ScalarRestrictionData Γ(X, U) Γ(X, V) Γ(M, U) Γ(M, V) := by
  letI := affineRestrictionBaseAlgebra U V i
  exact
    { equiv := affineRestrictionAlgEquiv U V i M
      restriction := sectionRestriction M i
      one_tmul := affineRestrictionAlgEquiv_one_tmul U V i M }

/-- Its original right inclusion is exactly the section restriction ring homomorphism. -/
theorem affineRestrictionAlgEquiv_comp_includeRight [M.IsQuasicoherent] :
    letI := affineRestrictionBaseAlgebra U V i
    (affineRestrictionData U V i M).Compatible := by
  let hBase := affineRestrictionBaseAlgebra U V i
  exact (affineRestrictionData U V i M).comp_includeRight

/-- Coherent finite-type underlying modules give finite affine section algebras. -/
theorem finite_sectionAlgebra (hM : QuasiCoherent.affineLocallyFiniteType X M)
    (U : X.affineOpens) : Module.Finite Γ(X, U) Γ(M, U) :=
  QuasiCoherent.finite_sections_of_affineLocallyFiniteType M hM U

end AlgebraicGeometry.Scheme.Modules.Algebra
