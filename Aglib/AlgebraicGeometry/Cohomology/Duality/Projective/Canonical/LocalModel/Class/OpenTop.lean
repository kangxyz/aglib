/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalModel.OpenTopClass
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalModel.Class.Degree

/-!
# Actual open transport of the original model class in its common degree

The original ambient and two-stage principal maps carry the original model
class to the original target model class. Its only degree change is the
genuine length equality already carried by the native Ext-class formula.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry Opposite

universe u w z
namespace AlgebraicGeometry.Scheme.Modules

local instance {A : CommRingCat.{u}} (s : List A) :
    IsClosedImmersion (Spec.map (regularListQuotientMap s)) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

section Ambient
variable {A A' : CommRingCat.{u}} (a : A ≃+* A') (s : List A)
  (hs : RingTheory.Sequence.IsWeaklyRegular A s)
  {L : (Spec A).Modules} [L.IsQuasicoherent]
  (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of A A) (J : InjectiveResolution L)
  [HasExt.{w} (ModuleCat.{u} A)] [HasExt.{z} (ModuleCat.{u} A')]

local instance : ((restrictFunctor (Spec.map a.toCommRingCatIso.hom)).obj L).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (Spec A').ringCatSheaf).prop_of_iso
    ((restrictFunctorIsoPullback (Spec.map a.toCommRingCatIso.hom)).symm.app L)
    (isQuasicoherent_pullback a.toCommRingCatIso.hom L)

/-- The actual ambient map preserves the original class with its genuine target degree. -/
theorem regularListAmbientSheafHomologyMap_modelTopClass (x : A)
    (V : (Spec (regularListQuotientRing (s.map a.toRingHom))).Opens) :
    letI := a.toRingHom.toAlgebra
    letI : Module.Flat A A' :=
      RingHom.flat_algebraMap_iff.mp (RingHom.Flat.of_bijective a.bijective)
    let φ := a.toCommRingCatIso.hom
    let ψ := (regularListAmbientQuotientEquiv a s).toCommRingCatIso.hom
    let J' := affineOpenRestrictedInjectiveResolution φ J
    let θ := affineRestrictGlobalSectionsIso φ L
    let e' := regularListAmbientCoefficientFrame a e θ
    (canonicalAmbientSheafHomologyMap φ (regularListQuotientMap s)
        (regularListQuotientMap (s.map a.toRingHom)) ψ (regularListAmbientSquare a s) J
          (s.length : ℤ)).val.app (op V)
      (regularListModelTopClass s hs J e x ((Spec.map ψ) ''ᵁ V)) =
      regularListModelTopClassInDegree (s.map a.toRingHom) (hs.of_flat (S := A'))
        J' e' s.length (List.length_map (as := s) a.toRingHom) (a x) V := by
  let := a.toRingHom.toAlgebra
  let : Module.Flat A A' :=
    RingHom.flat_algebraMap_iff.mp (RingHom.Flat.of_bijective a.bijective)
  intro φ ψ J' θ e'
  have ht := regularListModelTopClassInDegree_native (s.map a.toRingHom)
    (hs.of_flat (S := A')) J' e' s.length (List.length_map (as := s) a.toRingHom) (a x) V
  dsimp only at ht
  rw [closedImmersionRightAdjointRegularListResolutionSectionsExtAddEquiv_eq_affine] at ht
  exact (regularListAmbientSheafHomologyMap_topClass a s hs e J x V).trans ht.symm

end Ambient

section Principal
variable {A : CommRingCat.{u}} (s : List A)
  (hs : RingTheory.Sequence.IsWeaklyRegular A s) (r : A)
  {L : (Spec A).Modules} [L.IsQuasicoherent]
  (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of A A) (J : InjectiveResolution L)
  [HasExt.{w} (ModuleCat.{u} A)] [HasExt.{z} (ModuleCat.{u} (Localization.Away r))]

local instance : ((restrictFunctor (Spec.map
    (CommRingCat.ofHom (algebraMap A (Localization.Away r))))).obj L).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent
    (Spec (CommRingCat.of (Localization.Away r))).ringCatSheaf).prop_of_iso
    ((restrictFunctorIsoPullback
      (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away r))))).symm.app L)
    (isQuasicoherent_pullback (CommRingCat.ofHom (algebraMap A (Localization.Away r))) L)

/-- The original two-stage principal map preserves the original localized model class. -/
theorem regularListPrincipalSheafHomologyMap_modelTopClass (x : A)
    (V : (Spec (regularListQuotientRing (A := CommRingCat.of (Localization.Away r))
      (regularListPrincipalList s r))).Opens) :
    let S := Localization.Away r
    let φ : A ⟶ CommRingCat.of S := CommRingCat.ofHom (algebraMap A S)
    let ψ : regularListQuotientRing s ⟶
        CommRingCat.of (Localization.Away (Ideal.Quotient.mk (Ideal.ofList s) r)) :=
      CommRingCat.ofHom (algebraMap (A ⧸ Ideal.ofList s)
        (Localization.Away (Ideal.Quotient.mk (Ideal.ofList s) r)))
    let ε := (regularListPrincipalQuotientEquiv s r).toCommRingCatIso.inv
    let J' := affineOpenRestrictedInjectiveResolution φ J
    let θ := affineRestrictGlobalSectionsIso φ L
    let e' := regularListPrincipalCoefficientFrame r e θ
    letI : Module.Flat A S := IsLocalization.flat S (Submonoid.powers r)
    (regularListPrincipalSheafHomologyMap s r J (s.length : ℤ)).val.app (op V)
      (regularListModelTopClass s hs J e x
        ((Spec.map ψ) ''ᵁ ((Spec.map ε) ''ᵁ V))) =
      regularListModelTopClassInDegree (regularListPrincipalList s r) (hs.of_flat (S := S))
        J' e' s.length (List.length_map (as := s) (algebraMap A S)) (algebraMap A S x) V := by
  intro S φ ψ ε J' θ e'
  let : Module.Flat A S := IsLocalization.flat S (Submonoid.powers r)
  have ht := regularListModelTopClassInDegree_native (regularListPrincipalList s r)
    (hs.of_flat (S := S)) J' e' s.length
      (List.length_map (as := s) (algebraMap A S)) (algebraMap A S x) V
  dsimp only at ht
  rw [closedImmersionRightAdjointRegularListResolutionSectionsExtAddEquiv_eq_affine] at ht
  exact (regularListPrincipalSheafHomologyMap_topClass s hs r e J x V).trans ht.symm

end Principal
end AlgebraicGeometry.Scheme.Modules
