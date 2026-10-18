/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Principal
public import Aglib.Algebra.Homology.Koszul.Ext.ScalarExtensionClass

/-!
# The original principal quotient source in the two native class comparisons

The actual geometric localization model and the original exact
scalar-extension class theorem use two quotient source comparisons.
The literal quotient/localization equivalence identifies their actual
maps, as checked on the original unit pure tensors.
-/

@[expose] public section
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct ChangeOfRings

universe u
namespace AlgebraicGeometry.Scheme.Modules

variable {A : CommRingCat.{u}} (s : List A) (r : A)

/-- The original localized quotient map, with its original target quotient localization. -/
abbrev regularListPrincipalClosedMap :
    Localization.Away r →+* Localization.Away (Ideal.Quotient.mk (Ideal.ofList s) r) :=
  IsLocalization.Away.map (Localization.Away r)
    (Localization.Away (Ideal.Quotient.mk (Ideal.ofList s) r))
    (Ideal.Quotient.mk (Ideal.ofList s)) r

/-- The actual quotient/localization ring equivalence retains the original ambient action. -/
def regularListPrincipalModuleIso :
    ModuleCat.of (Localization.Away r)
      (Localization.Away r ⧸ Ideal.ofList (regularListPrincipalList s r)) ≅
    (ModuleCat.restrictScalars (regularListPrincipalClosedMap s r)).obj
      (ModuleCat.of (Localization.Away (Ideal.Quotient.mk (Ideal.ofList s) r))
        (Localization.Away (Ideal.Quotient.mk (Ideal.ofList s) r))) := by
  refine ModuleCat.isoMk (regularListPrincipalQuotientEquiv s r).toAddEquiv.toAddCommGrpIso ?_
  intro a
  ext x
  change regularListPrincipalClosedMap s r a * regularListPrincipalQuotientEquiv s r x =
    regularListPrincipalQuotientEquiv s r
      (Ideal.Quotient.mk (Ideal.ofList (regularListPrincipalList s r)) a * x)
  rw [map_mul, regularListPrincipalQuotientEquiv_mk]

/-- The two actual quotient-source maps agree through the same quotient/localization map. -/
theorem regularListPrincipalSourceIso_hom :
    (closedImmersionQuotientLocalizationSourceIso (Ideal.ofList s) r).hom =
      (ChainComplex.Koszul.scalarExtensionQuotientIso (S := Localization.Away r) s).hom ≫
        (regularListPrincipalModuleIso s r).hom := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  change (closedImmersionQuotientLocalizationSourceIso (Ideal.ofList s) r).hom
      ((1 : Localization.Away r) ⊗ₜ[A,algebraMap A (Localization.Away r)]
        Ideal.Quotient.mk (Ideal.ofList s) a) =
    (regularListPrincipalModuleIso s r).hom
      ((ChainComplex.Koszul.scalarExtensionQuotientIso (S := Localization.Away r) s).hom
        ((1 : Localization.Away r) ⊗ₜ[A,algebraMap A (Localization.Away r)]
          Ideal.Quotient.mk (Ideal.ofList s) a))
  rw [closedImmersionQuotientLocalizationSourceIso_one_tmul,
    ChainComplex.Koszul.scalarExtensionQuotientIso_one_tmul]
  change algebraMap (A ⧸ Ideal.ofList s)
      (Localization.Away (Ideal.Quotient.mk (Ideal.ofList s) r))
      (Ideal.Quotient.mk (Ideal.ofList s) a) =
    regularListPrincipalQuotientEquiv s r
      (Ideal.Quotient.mk (Ideal.ofList (regularListPrincipalList s r))
        (algebraMap A (Localization.Away r) a))
  rw [regularListPrincipalQuotientEquiv_mk]
  simp only [IsLocalization.Away.map, IsLocalization.map_eq]
end AlgebraicGeometry.Scheme.Modules
