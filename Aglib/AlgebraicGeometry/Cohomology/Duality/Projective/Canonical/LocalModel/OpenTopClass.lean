/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalModel.OpenCounit
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalModel.Class
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Principal.AmbientIsomorphism.Classes
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Principal.NormalizedClass
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Principal.Derived
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalModel.OpenTopClass.Source

/-!
# Original top classes on the actual open sheaf model

The native module-class transport is applied through the original affine
counit. The resulting formula concerns the actual sheaf-model homology
map on every open. The original class, coefficient frame and list-length
cast remain explicit.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Abelian HomologicalComplex AlgebraicGeometry Opposite

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

/-- The actual ambient-isomorphism sheaf homology map takes the original
top class to the original image-list class, with its genuine degree cast
and the original induced coefficient frame. -/
theorem regularListAmbientSheafHomologyMap_topClass (x : A)
    (V : (Spec (regularListQuotientRing (s.map a.toRingHom))).Opens) :
    letI := a.toRingHom.toAlgebra
    letI : Module.Flat A A' :=
      RingHom.flat_algebraMap_iff.mp (RingHom.Flat.of_bijective a.bijective)
    let φ := a.toCommRingCatIso.hom
    let σ := regularListQuotientMap s
    let τ := regularListQuotientMap (s.map a.toRingHom)
    let ψ := (regularListAmbientQuotientEquiv a s).toCommRingCatIso.hom
    let J' := affineOpenRestrictedInjectiveResolution φ J
    let θ := affineRestrictGlobalSectionsIso φ L
    let e' := regularListAmbientCoefficientFrame a e θ
    let η := (cast (congrArg (fun k => Ext.{z}
      (ModuleCat.of A' (A' ⧸ Ideal.ofList (s.map a.toRingHom))) (ModuleCat.of A' A') k)
      (List.length_map (as := s) a.toRingHom))
      (ChainComplex.Koszul.topExtClass (s.map a.toRingHom) (hs.of_flat (S := A'))
        (ModuleCat.of A' A') (a x))).comp (Ext.mk₀ e'.inv) (add_zero s.length)
    (canonicalAmbientSheafHomologyMap φ σ τ ψ (regularListAmbientSquare a s) J
        (s.length : ℤ)).val.app (op V)
      (regularListModelTopClass s hs J e x ((Spec.map ψ) ''ᵁ V)) =
    (canonicalTildeHomologyCounitMap (canonicalAmbientTargetSheafComplex φ τ J)
      (s.length : ℤ)).val.app (op V)
      (tilde.toOpen ((closedImmersionSourceResolutionComplex J' τ).homology (s.length : ℤ)) V
        ((affineClosedRightAdjointResolutionExtAddEquiv τ J' s.length).symm η)) := by
  let := a.toRingHom.toAlgebra
  let : Module.Flat A A' :=
    RingHom.flat_algebraMap_iff.mp (RingHom.Flat.of_bijective a.bijective)
  intro φ σ τ ψ J' θ e' η
  let ξ := (closedImmersionRightAdjointRegularListResolutionSectionsExtAddEquiv s J
    s.length).symm ((ChainComplex.Koszul.topExtClass s hs (ModuleCat.of A A) x).comp
      (Ext.mk₀ e.inv) (add_zero s.length))
  have hm := regularListAmbientHomologyMap_topClass a s hs e J x
  change affineClosedRightAdjointResolutionExtAddEquiv τ J' s.length
      (canonicalAmbientHomologyMap φ σ τ ψ (regularListAmbientSquare a s) J
        (s.length : ℤ) ξ) = η at hm
  have hv : canonicalAmbientHomologyMap φ σ τ ψ (regularListAmbientSquare a s) J
      (s.length : ℤ) ξ = (affineClosedRightAdjointResolutionExtAddEquiv τ J' s.length).symm η := by
    apply (affineClosedRightAdjointResolutionExtAddEquiv τ J' s.length).injective
    exact hm.trans
      ((affineClosedRightAdjointResolutionExtAddEquiv τ J' s.length).apply_symm_apply η).symm
  have ht := canonicalAmbientSheafHomologyMap_counit_section φ σ τ ψ
    (regularListAmbientSquare a s) J (s.length : ℤ) ξ V
  rw [hv] at ht
  exact ht

end Ambient

local instance {A : CommRingCat.{u}} (s : List A) (r : A) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (regularListPrincipalClosedMap s r))) :=
  IsClosedImmersion.spec_of_surjective _
    (IsLocalization.map_surjective_of_surjective (Submonoid.powers r) (Localization.Away r)
      (Localization.Away (Ideal.Quotient.mk (Ideal.ofList s) r)) Ideal.Quotient.mk_surjective)

section PrincipalGeometry
variable {A : CommRingCat.{u}} (s : List A) (r : A)
  {L : (Spec A).Modules} (J : InjectiveResolution L)

/-- The raw ambient resolution arrow is the frozen original quotient-localization arrow. -/
theorem regularListPrincipalRawResolutionMap_eq :
    let S := CommRingCat.of (Localization.Away r)
    let T := CommRingCat.of (Localization.Away (Ideal.Quotient.mk (Ideal.ofList s) r))
    let φ : A ⟶ S := CommRingCat.ofHom (algebraMap A (Localization.Away r))
    let q := regularListQuotientMap s
    let q' : S ⟶ T := CommRingCat.ofHom (regularListPrincipalClosedMap s r)
    let ψ : regularListQuotientRing s ⟶ T := CommRingCat.ofHom
      (algebraMap (A ⧸ Ideal.ofList s) (Localization.Away (Ideal.Quotient.mk (Ideal.ofList s) r)))
    canonicalAmbientResolutionMap φ q q' ψ (regularListPrincipalRawSquare s r) J =
      closedImmersionQuotientLocalizationResolutionMap (Ideal.ofList s) r J := by
  intro S T φ q q' ψ
  ext n : 1
  rw [canonicalAmbientResolutionMap_model_f, regularListPrincipalResolutionMap_model_f,
    canonicalAmbientModelOpenIso_hom_f, regularListPrincipalModelOpenIso_hom_f]

/-- The raw ambient homology arrow is the frozen original quotient-localization map. -/
theorem regularListPrincipalRawHomologyMap_eq (n : ℤ) :
    let S := CommRingCat.of (Localization.Away r)
    let T := CommRingCat.of (Localization.Away (Ideal.Quotient.mk (Ideal.ofList s) r))
    let φ : A ⟶ S := CommRingCat.ofHom (algebraMap A (Localization.Away r))
    let q := regularListQuotientMap s
    let q' : S ⟶ T := CommRingCat.ofHom (regularListPrincipalClosedMap s r)
    let ψ : regularListQuotientRing s ⟶ T := CommRingCat.ofHom
      (algebraMap (A ⧸ Ideal.ofList s) (Localization.Away (Ideal.Quotient.mk (Ideal.ofList s) r)))
    canonicalAmbientHomologyMap φ q q' ψ (regularListPrincipalRawSquare s r) J n =
      closedImmersionQuotientLocalizationHomologyMap (Ideal.ofList s) r J n := by
  intro S T φ q q' ψ
  have hr : canonicalAmbientResolutionMap φ q q' ψ (regularListPrincipalRawSquare s r) J =
      closedImmersionQuotientLocalizationResolutionMap (Ideal.ofList s) r J :=
    regularListPrincipalRawResolutionMap_eq s r J
  rw [canonicalAmbientHomologyMap, hr]
  exact (closedImmersionQuotientLocalizationHomologyMap_eq (Ideal.ofList s) r J n).symm

/-- The actual principal sheaf map is raw open restriction followed by the original
source-isomorphism normalization. Its source retains the two original restrictions. -/
def regularListPrincipalSheafHomologyMap (n : ℤ) :
    let S := CommRingCat.of (Localization.Away r)
    let T := CommRingCat.of (Localization.Away (Ideal.Quotient.mk (Ideal.ofList s) r))
    let φ : A ⟶ S := CommRingCat.ofHom (algebraMap A (Localization.Away r))
    let q := regularListQuotientMap s
    let _q' : S ⟶ T := CommRingCat.ofHom (regularListPrincipalClosedMap s r)
    let τ := regularListQuotientMap (A := S) (regularListPrincipalList s r)
    let : IsClosedImmersion (Spec.map τ) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    let ψ : regularListQuotientRing s ⟶ T := CommRingCat.ofHom
      (algebraMap (A ⧸ Ideal.ofList s) (Localization.Away (Ideal.Quotient.mk (Ideal.ofList s) r)))
    let ε := (regularListPrincipalQuotientEquiv s r).toCommRingCatIso.inv
    let J' := affineOpenRestrictedInjectiveResolution φ J
    (((canonicalAmbientSourceSheafComplex q J).homology n).restrict (Spec.map ψ)).restrict
        (Spec.map ε) ⟶ (canonicalSourceSheafComplex τ J').homology n := by
  intro S T φ q q' τ hτ ψ ε J'
  let : IsClosedImmersion (Spec.map τ) := hτ
  exact (restrictFunctor (Spec.map ε)).map
      (canonicalAmbientSheafHomologyMap φ q q' ψ (regularListPrincipalRawSquare s r) J n) ≫
    canonicalSourceSheafHomologyMap q' τ (regularListPrincipalQuotientEquiv s r)
      (regularListPrincipalSourceOnlySquare s r) J' n

/-- On every open the actual normalized map is the successive application of its
two original sheaf homology maps. -/
theorem regularListPrincipalSheafHomologyMap_app (n : ℤ)
    (V : (Spec (regularListQuotientRing (A := CommRingCat.of (Localization.Away r))
      (regularListPrincipalList s r))).Opens) :
    let S := CommRingCat.of (Localization.Away r)
    let T := CommRingCat.of (Localization.Away (Ideal.Quotient.mk (Ideal.ofList s) r))
    let φ : A ⟶ S := CommRingCat.ofHom (algebraMap A (Localization.Away r))
    let q := regularListQuotientMap s
    let q' : S ⟶ T := CommRingCat.ofHom (regularListPrincipalClosedMap s r)
    let τ := regularListQuotientMap (A := S) (regularListPrincipalList s r)
    let : IsClosedImmersion (Spec.map τ) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    let ψ : regularListQuotientRing s ⟶ T := CommRingCat.ofHom
      (algebraMap (A ⧸ Ideal.ofList s) (Localization.Away (Ideal.Quotient.mk (Ideal.ofList s) r)))
    let ε := (regularListPrincipalQuotientEquiv s r).toCommRingCatIso.inv
    let J' := affineOpenRestrictedInjectiveResolution φ J
    ∀ x : ((canonicalAmbientSourceSheafComplex q J).homology n).val.obj
        (op ((Spec.map ψ) ''ᵁ ((Spec.map ε) ''ᵁ V))),
      (regularListPrincipalSheafHomologyMap s r J n).val.app (op V) x =
        (canonicalSourceSheafHomologyMap q' τ (regularListPrincipalQuotientEquiv s r)
          (regularListPrincipalSourceOnlySquare s r) J' n).val.app (op V)
          ((canonicalAmbientSheafHomologyMap φ q q' ψ
            (regularListPrincipalRawSquare s r) J n).val.app (op ((Spec.map ε) ''ᵁ V)) x) := by
  intro S T φ q q' τ hτ ψ ε J' x
  let : IsClosedImmersion (Spec.map τ) := hτ
  rfl

/-- The original two-stage principal map acts on every native module-homology
class through the two original affine counit maps. -/
theorem regularListPrincipalSheafHomologyMap_counit_section (n : ℤ)
    (x : (closedImmersionSourceResolutionComplex J (regularListQuotientMap s)).homology n)
    (V : (Spec (regularListQuotientRing (A := CommRingCat.of (Localization.Away r))
      (regularListPrincipalList s r))).Opens) :
    let S := CommRingCat.of (Localization.Away r)
    let T := CommRingCat.of (Localization.Away (Ideal.Quotient.mk (Ideal.ofList s) r))
    let φ : A ⟶ S := CommRingCat.ofHom (algebraMap A (Localization.Away r))
    let q := regularListQuotientMap s
    let q' : S ⟶ T := CommRingCat.ofHom (regularListPrincipalClosedMap s r)
    let τ := regularListQuotientMap (A := S) (regularListPrincipalList s r)
    let : IsClosedImmersion (Spec.map τ) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    let ψ : regularListQuotientRing s ⟶ T := CommRingCat.ofHom
      (algebraMap (A ⧸ Ideal.ofList s) (Localization.Away (Ideal.Quotient.mk (Ideal.ofList s) r)))
    let ε := (regularListPrincipalQuotientEquiv s r).toCommRingCatIso.inv
    let J' := affineOpenRestrictedInjectiveResolution φ J
    let B' := regularListQuotientRing (A := S) (regularListPrincipalList s r)
    let K' : CochainComplex (Spec B').Modules ℤ :=
      ((closedImmersionRightAdjoint (Spec.map τ)).mapHomologicalComplex (.up ℤ)).obj
        J'.cochainComplex
    letI : (moduleSpecΓFunctor (R := B')).Additive := moduleSpecΓFunctor_additive B'
    let C' : CochainComplex (ModuleCat.{u} B') ℤ :=
      ((moduleSpecΓFunctor (R := B')).mapHomologicalComplex (.up ℤ)).obj K'
    (regularListPrincipalSheafHomologyMap s r J n).val.app (op V)
      ((canonicalTildeHomologyCounitMap (canonicalAmbientSourceSheafComplex q J) n).val.app
        (op ((Spec.map ψ) ''ᵁ ((Spec.map ε) ''ᵁ V)))
        (tilde.toOpen ((closedImmersionSourceResolutionComplex J q).homology n)
          ((Spec.map ψ) ''ᵁ ((Spec.map ε) ''ᵁ V)) x)) =
      (canonicalTildeHomologyCounitMap K' n).val.app (op V)
        (tilde.toOpen (C'.homology n) V
          (closedImmersionSourceHomologyMap q' τ (regularListPrincipalQuotientEquiv s r)
            (regularListPrincipalSourceOnlySquare s r) J' n
            (closedImmersionQuotientLocalizationHomologyMap (Ideal.ofList s) r J n x))) := by
  intro S T φ q q' τ hτ ψ ε J' B' K' C'
  let : IsClosedImmersion (Spec.map τ) := hτ
  rw [regularListPrincipalSheafHomologyMap_app]
  have ht := canonicalAmbientSheafHomologyMap_counit_section φ q q' ψ
    (regularListPrincipalRawSquare s r) J n x ((Spec.map ε) ''ᵁ V)
  rw [regularListPrincipalRawHomologyMap_eq] at ht
  have hc := congrArg
    ((canonicalSourceSheafHomologyMap q' τ (regularListPrincipalQuotientEquiv s r)
      (regularListPrincipalSourceOnlySquare s r) J' n).val.app (op V)) ht
  have ht' := canonicalSourceSheafHomologyMap_counit_section q' τ
    (regularListPrincipalQuotientEquiv s r) (regularListPrincipalSourceOnlySquare s r)
    J' n (closedImmersionQuotientLocalizationHomologyMap (Ideal.ofList s) r J n x) V
  exact hc.trans ht'

end PrincipalGeometry

section PrincipalClass
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

/-- The actual two-stage principal sheaf map takes the original top class to the
normalized original localized class, retaining its degree cast and coefficient frame. -/
theorem regularListPrincipalSheafHomologyMap_topClass (x : A)
    (V : (Spec (regularListQuotientRing (A := CommRingCat.of (Localization.Away r))
      (regularListPrincipalList s r))).Opens) :
    let S := Localization.Away r
    let φ : A ⟶ CommRingCat.of S := CommRingCat.ofHom (algebraMap A S)
    let _q := regularListQuotientMap s
    let _q' := CommRingCat.ofHom (regularListPrincipalClosedMap s r)
    let t := regularListPrincipalList s r
    let τ := regularListQuotientMap (A := CommRingCat.of S) t
    let : IsClosedImmersion (Spec.map τ) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    let ψ : regularListQuotientRing s ⟶
        CommRingCat.of (Localization.Away (Ideal.Quotient.mk (Ideal.ofList s) r)) :=
      CommRingCat.ofHom (algebraMap (A ⧸ Ideal.ofList s)
        (Localization.Away (Ideal.Quotient.mk (Ideal.ofList s) r)))
    let ε := (regularListPrincipalQuotientEquiv s r).toCommRingCatIso.inv
    let J' := affineOpenRestrictedInjectiveResolution φ J
    let B' := regularListQuotientRing (A := CommRingCat.of S) t
    let K' : CochainComplex (Spec B').Modules ℤ :=
      ((closedImmersionRightAdjoint (Spec.map τ)).mapHomologicalComplex (.up ℤ)).obj
        J'.cochainComplex
    letI : (moduleSpecΓFunctor (R := B')).Additive := moduleSpecΓFunctor_additive B'
    let C' : CochainComplex (ModuleCat.{u} B') ℤ :=
      ((moduleSpecΓFunctor (R := B')).mapHomologicalComplex (.up ℤ)).obj K'
    let θ := affineRestrictGlobalSectionsIso φ L
    let e' := regularListPrincipalCoefficientFrame r e θ
    let : Module.Flat A S := IsLocalization.flat S (Submonoid.powers r)
    let η := (cast (congrArg (fun k => Ext.{z}
      (ModuleCat.of S (S ⧸ Ideal.ofList t)) (ModuleCat.of S S) k)
      (List.length_map (as := s) (algebraMap A S)))
      (ChainComplex.Koszul.topExtClass t (hs.of_flat (S := S))
        (ModuleCat.of S S) (algebraMap A S x))).comp (Ext.mk₀ e'.inv)
          (add_zero s.length)
    (regularListPrincipalSheafHomologyMap s r J (s.length : ℤ)).val.app (op V)
      (regularListModelTopClass s hs J e x
        ((Spec.map ψ) ''ᵁ ((Spec.map ε) ''ᵁ V))) =
      (canonicalTildeHomologyCounitMap K' (s.length : ℤ)).val.app (op V)
        (tilde.toOpen (C'.homology (s.length : ℤ)) V
          ((affineClosedRightAdjointResolutionExtAddEquiv τ J' s.length).symm η)) := by
  intro S φ q q' t τ hτ ψ ε J' B' K' C' θ e' hflat η
  let : IsClosedImmersion (Spec.map τ) := hτ
  let : Module.Flat A S := hflat
  let ξ := (closedImmersionRightAdjointRegularListResolutionSectionsExtAddEquiv s J
    s.length).symm ((ChainComplex.Koszul.topExtClass s hs (ModuleCat.of A A) x).comp
      (Ext.mk₀ e.inv) (add_zero s.length))
  have hm := regularListPrincipalNormalizedHomologyMap_topClass s r hs e J x
  change affineClosedRightAdjointResolutionExtAddEquiv τ J' s.length
      (closedImmersionSourceHomologyMap q' τ (regularListPrincipalQuotientEquiv s r)
        (regularListPrincipalSourceOnlySquare s r) J' (s.length : ℤ)
        (closedImmersionQuotientLocalizationHomologyMap (Ideal.ofList s) r J
          (s.length : ℤ) ξ)) = η at hm
  have hv : closedImmersionSourceHomologyMap q' τ (regularListPrincipalQuotientEquiv s r)
      (regularListPrincipalSourceOnlySquare s r) J' (s.length : ℤ)
      (closedImmersionQuotientLocalizationHomologyMap (Ideal.ofList s) r J
        (s.length : ℤ) ξ) =
      (affineClosedRightAdjointResolutionExtAddEquiv τ J' s.length).symm η := by
    apply (affineClosedRightAdjointResolutionExtAddEquiv τ J' s.length).injective
    exact hm.trans
      ((affineClosedRightAdjointResolutionExtAddEquiv τ J' s.length).apply_symm_apply η).symm
  have ht := regularListPrincipalSheafHomologyMap_counit_section s r J (s.length : ℤ) ξ V
  dsimp only at ht
  rw [hv] at ht
  exact ht

end PrincipalClass
end AlgebraicGeometry.Scheme.Modules
