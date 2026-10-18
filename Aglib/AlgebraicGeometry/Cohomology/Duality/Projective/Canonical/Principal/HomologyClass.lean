/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Principal.Class

/-!
# Original top classes under the actual geometric principal homology map

The installed geometric localization map on the original injective model
is compared with the original exact scalar-extension class, using the same
quotient/localization source and the same localized coefficient frame.
This is the class computation before transporting native sheaf homology.
-/

@[expose] public section
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u w z
namespace AlgebraicGeometry.Scheme.Modules

variable {A : CommRingCat.{u}} (s : List A)
  (hs : RingTheory.Sequence.IsWeaklyRegular A s) (r : A)
  {L : (Spec A).Modules} [L.IsQuasicoherent]
  (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of A A) (J : InjectiveResolution L)
  [HasExt.{w} (ModuleCat.{u} A)]
  [HasExt.{z} (ModuleCat.{u} (Localization.Away r))]

local instance : (moduleSpecΓFunctor (R := regularListQuotientRing s)).Additive :=
  moduleSpecΓFunctor_additive _

local instance : (moduleSpecΓFunctor (R := CommRingCat.of
    (Localization.Away (Ideal.Quotient.mk (Ideal.ofList s) r)))).Additive :=
  moduleSpecΓFunctor_additive _

local instance : IsClosedImmersion (Spec.map (CommRingCat.ofHom
    (regularListPrincipalClosedMap s r))) :=
  IsClosedImmersion.spec_of_surjective _
    (IsLocalization.map_surjective_of_surjective (Submonoid.powers r) (Localization.Away r)
      (Localization.Away (Ideal.Quotient.mk (Ideal.ofList s) r)) Ideal.Quotient.mk_surjective)

/-- The original geometric model homology map sends the original top class to the literal
same-list localized class with the original source and coefficient normalizations. -/
theorem regularListPrincipalHomologyMap_topClass (x : A) :
    let S := Localization.Away r
    let T := Localization.Away (Ideal.Quotient.mk (Ideal.ofList s) r)
    let σ : A ⟶ CommRingCat.of S := CommRingCat.ofHom (algebraMap A S)
    let q' : CommRingCat.of S ⟶ CommRingCat.of T :=
      CommRingCat.ofHom (regularListPrincipalClosedMap s r)
    let J' := affineOpenRestrictedInjectiveResolution σ J
    let θ := affineRestrictGlobalSectionsIso σ L
    let e' := regularListPrincipalCoefficientFrame r e θ
    let : Module.Flat A S := IsLocalization.flat S (Submonoid.powers r)
    let ξ := (closedImmersionRightAdjointRegularListResolutionSectionsExtAddEquiv s J
      s.length).symm ((ChainComplex.Koszul.topExtClass s hs (ModuleCat.of A A) x).comp
        (Ext.mk₀ e.inv) (add_zero s.length))
    let τ := cast (congrArg (fun k => Ext.{z}
      (ModuleCat.of S (S ⧸ Ideal.ofList (s.map (algebraMap A S)))) (ModuleCat.of S S) k)
      (List.length_map (as := s) (algebraMap A S)))
      (ChainComplex.Koszul.topExtClass (s.map (algebraMap A S)) (hs.of_flat (S := S))
        (ModuleCat.of S S) (algebraMap A S x))
    affineClosedRightAdjointResolutionExtAddEquiv q' J' s.length
      (closedImmersionQuotientLocalizationHomologyMap (Ideal.ofList s) r J (s.length : ℤ) ξ) =
      (Ext.mk₀ (regularListPrincipalModuleIso s r).inv).comp
        (τ.comp (Ext.mk₀ e'.inv) (add_zero s.length)) (zero_add s.length) := by
  intro S T σ q' J' θ e' hflat ξ τ
  let F : ModuleCat.{u} A ⥤ ModuleCat.{u} S := ModuleCat.extendScalars (algebraMap A S)
  let : PreservesFiniteLimits F := ModuleCat.extendScalars_preservesFiniteLimits_of_flat _
    (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat S (Submonoid.powers r)))
  let : PreservesFiniteColimits F := ModuleCat.extendScalars_preservesFiniteColimits_of_flat _
    (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat S (Submonoid.powers r)))
  let β := ((ChainComplex.Koszul.topExtClass s hs (ModuleCat.of A A) x).comp
    (Ext.mk₀ e.inv) (add_zero s.length)).mapExactFunctor F
  let μ := ChainComplex.Koszul.scalarExtensionQuotientIso (S := S) s
  let ν := regularListPrincipalModuleIso s r
  let η := closedImmersionQuotientLocalizationSourceIso (Ideal.ofList s) r
  have hg := closedImmersionQuotientLocalizationHomologyMap_ext
    (Ideal.ofList s) r J s.length ξ
  have hξ : closedImmersionRightAdjointRegularListResolutionSectionsExtAddEquiv s J s.length ξ =
      (ChainComplex.Koszul.topExtClass s hs (ModuleCat.of A A) x).comp
        (Ext.mk₀ e.inv) (add_zero s.length) :=
    (closedImmersionRightAdjointRegularListResolutionSectionsExtAddEquiv s J
      s.length).apply_symm_apply _
  rw [closedImmersionRightAdjointRegularListResolutionSectionsExtAddEquiv_eq_affine] at hξ
  replace hg := hg.trans (congrArg (fun ζ : Ext.{w}
    (ModuleCat.of A (A ⧸ Ideal.ofList s)) (moduleSpecΓFunctor.obj L) s.length =>
      ((Ext.mk₀ η.inv).comp (ζ.mapExactFunctor F) (zero_add s.length)).comp
        (Ext.mk₀ θ.hom) (add_zero s.length)) hξ)
  change _ = ((Ext.mk₀ η.inv).comp β (zero_add s.length)).comp
    (Ext.mk₀ θ.hom) (add_zero s.length) at hg
  have hi : η = μ ≪≫ ν := by
    apply Iso.ext
    exact regularListPrincipalSourceIso_hom s r
  have hinv : η.inv = ν.inv ≫ μ.inv := congrArg Iso.inv hi
  have hf : (Ext.mk₀ ν.inv).comp ((Ext.mk₀ μ.inv).comp β (zero_add s.length))
      (zero_add s.length) = (Ext.mk₀ η.inv).comp β (zero_add s.length) :=
    (Ext.mk₀_comp_mk₀_assoc ν.inv μ.inv β).trans
      (congrArg (fun f => (Ext.mk₀ f).comp β (zero_add s.length)) hinv.symm)
  have hc := regularListPrincipalTopExtClass_coefficients r s hs x e θ
  change ((Ext.mk₀ μ.inv).comp β (zero_add s.length)).comp (Ext.mk₀ θ.hom)
    (add_zero s.length) = τ.comp (Ext.mk₀ e'.inv) (add_zero s.length) at hc
  exact hg.trans
    ((congrArg (fun γ => γ.comp (Ext.mk₀ θ.hom) (add_zero s.length)) hf.symm).trans
      ((Ext.comp_assoc_of_third_deg_zero (Ext.mk₀ ν.inv)
        ((Ext.mk₀ μ.inv).comp β (zero_add s.length)) (Ext.mk₀ θ.hom)
        (zero_add s.length)).trans
          (congrArg (fun γ => (Ext.mk₀ ν.inv).comp γ (zero_add s.length)) hc)))

end AlgebraicGeometry.Scheme.Modules
