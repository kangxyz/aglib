/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.RestrictionExact
public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.Support
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeSupport
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Restriction.Comparison
public import Aglib.AlgebraicGeometry.Modules.Coherent.Restriction
public import Aglib.Algebra.Category.FGModuleCat.Localization.Quotient
public import Mathlib.CategoryTheory.Localization.Equivalence

/-!
# Principal-open coherent localization

For a Noetherian coefficient ring, affine and global coherent restriction to a principal open
are Serre localizations by the actual restriction kernel, equivalently by sheaves supported in
its closed complement. The proof uses the original finite-module comparison square.
-/

/-!
Source: frozen dirty Quillen `6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
`Quillen/AlgebraicGeometry/Scheme/Coherent/Affine/RestrictionExact.lean`.
SHA-256: `6edc74f97df9ce1f5b01e4c98621a18b3b2e20966c5d9a4646e9d9b0af654c4e`.
`Quillen/AlgebraicGeometry/Scheme/Coherent/PrincipalRestriction.lean`.
SHA-256: `7406934ff4707a5c3be34e57ffcf420758a1cbec35455aa99406b13c2008eec8`.
Selected original statements and proofs; canonical lower APIs replace the recorded source wrappers.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ModuleCat
open AlgebraicGeometry.Scheme.Modules
attribute [local instance] Abelian.hasFiniteBiproducts
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open CategoryTheory.ExactCategory
namespace AlgebraicGeometry.Scheme.Modules.Coherent
variable (R : CommRingCat.{u}) [IsNoetherianRing R] (r : R)

/-- The actual coherent restriction functor has the Serre localization
universal property for its actual kernel. -/
instance affinePrincipalRestriction_isLocalization_kernel :
    (affinePrincipalRestriction R r).IsLocalization
      (affinePrincipalRestriction R r).kernel.isoModSerre := by
  let L := ModuleCat.FiniteLocalization.functor (Submonoid.powers r)
  let P := ModuleCat.FiniteLocalization.torsion (Submonoid.powers r)
  let e := affineFiniteTypeModuleEquivalence R
  let e' := affineFiniteTypeModuleEquivalence (CommRingCat.of (Localization.Away r))
  let square : CatCommSq e.functor (affinePrincipalRestriction R r) L e'.functor :=
    ⟨affinePrincipalRestrictionSquare R r⟩
  let : CatCommSq e.symm.functor L (affinePrincipalRestriction R r) e'.symm.functor :=
    CatCommSq.hInv e _ _ e' square
  have hinv : (affinePrincipalRestriction R r).kernel.isoModSerre.IsInvertedBy
      (affinePrincipalRestriction R r) := by
    rw [Abelian.isoModSerre_kernel_eq_inverseImage_isomorphisms]
    intro M N f hf
    exact hf
  apply Functor.IsLocalization.of_equivalences L P.isoModSerre
    (affinePrincipalRestriction R r) (affinePrincipalRestriction R r).kernel.isoModSerre
    e.symm e'.symm ?_ hinv
  have hi : P.isoModSerre.IsInvertedBy (e.symm.functor ⋙ affinePrincipalRestriction R r) :=
    (MorphismProperty.IsInvertedBy.iff_of_iso _
      (CatCommSq.iso e.symm.functor L (affinePrincipalRestriction R r) e'.symm.functor)).2
        (Localization.inverts (L ⋙ e'.symm.functor) P.isoModSerre)
  intro M N f hf
  apply MorphismProperty.le_isoClosure
  rw [Abelian.isoModSerre_kernel_eq_inverseImage_isomorphisms]
  exact hi f hf

/-- Principal-open coherent restriction is localization by sheaves whose
ordinary support lies in the closed complement. -/
instance affinePrincipalRestriction_isLocalization :
    (affinePrincipalRestriction R r).IsLocalization
      (affineSupportedAway R (principalOpen R r)).isoModSerre := by
  have h : (affinePrincipalRestriction R r).kernel.isoModSerre =
      (affineSupportedAway R (principalOpen R r)).isoModSerre := by
    funext M N f
    apply propext
    change ((affinePrincipalRestriction R r).kernel (kernel f) ∧
      (affinePrincipalRestriction R r).kernel (cokernel f)) ↔ _
    rw [principalRestriction_kernel_eq_support]
    rfl
  rw [← h]
  infer_instance

/-- Actual restriction on the global coherent categories of two spectra is
the Serre localization by its actual kernel. -/
instance coherentPrincipalRestriction_isLocalization_kernel :
    (finiteTypeSheavesRestriction (principalOpen R r)).IsLocalization
      (finiteTypeSheavesRestriction (principalOpen R r)).kernel.isoModSerre := by
  let L := affinePrincipalRestriction R r
  let P := L.kernel
  let e := finiteTypeSheavesAffineEquivalence R
  let e' := finiteTypeSheavesAffineEquivalence (CommRingCat.of (Localization.Away r))
  let square : CatCommSq e.functor (finiteTypeSheavesRestriction (principalOpen R r)) L e'.functor
    :=
    ⟨finiteTypePrincipalRestrictionSquare R r⟩
  let : CatCommSq e.symm.functor L (finiteTypeSheavesRestriction (principalOpen R r))
    e'.symm.functor :=
    CatCommSq.hInv e _ _ e' square
  have hinv : (finiteTypeSheavesRestriction (principalOpen R r)).kernel.isoModSerre.IsInvertedBy
      (finiteTypeSheavesRestriction (principalOpen R r)) := by
    rw [Abelian.isoModSerre_kernel_eq_inverseImage_isomorphisms]
    intro M N f hf
    exact hf
  apply Functor.IsLocalization.of_equivalences L P.isoModSerre
    (finiteTypeSheavesRestriction (principalOpen R r))
    (finiteTypeSheavesRestriction (principalOpen R r)).kernel.isoModSerre
    e.symm e'.symm ?_ hinv
  have hi : P.isoModSerre.IsInvertedBy
      (e.symm.functor ⋙ finiteTypeSheavesRestriction (principalOpen R r)) :=
    (MorphismProperty.IsInvertedBy.iff_of_iso _
      (CatCommSq.iso e.symm.functor L (finiteTypeSheavesRestriction (principalOpen R r))
        e'.symm.functor)).2
      (Localization.inverts (L ⋙ e'.symm.functor) P.isoModSerre)
  intro M N f hf
  apply MorphismProperty.le_isoClosure
  rw [Abelian.isoModSerre_kernel_eq_inverseImage_isomorphisms]
  exact hi f hf

/-- Equivalently, it is localization by actual coherent sheaves supported in
the closed complement of the principal open. -/
instance coherentPrincipalRestriction_isLocalization :
    (finiteTypeSheavesRestriction (principalOpen R r)).IsLocalization
      (finiteTypeSheavesSupportedAway (principalOpen R r)).isoModSerre := by
  have h : (finiteTypeSheavesRestriction (principalOpen R r)).kernel.isoModSerre =
      (finiteTypeSheavesSupportedAway (principalOpen R r)).isoModSerre := by
    funext M N f
    apply propext
    change ((finiteTypeSheavesRestriction (principalOpen R r)).kernel (kernel f) ∧
      (finiteTypeSheavesRestriction (principalOpen R r)).kernel (cokernel f)) ↔ _
    rw [finiteTypeSheavesRestriction_kernel_eq_support]
    rfl
  rw [← h]
  infer_instance

end AlgebraicGeometry.Scheme.Modules.Coherent
