/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Principal.HomologyClass

/-!
# Original principal restriction on the sheaf injective model

The same original principal quotient map is used for the native closed-adjoint
open comparison. Mapping that comparison termwise and retaining the original
restriction/extension comparison gives the actual sheaf-complex isomorphism.
Its affine sections are the original geometric localization map, before
native derived units identify the installed right-adjoint object.
-/

@[expose] public section
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u
namespace AlgebraicGeometry.Scheme.Modules

variable {A : CommRingCat.{u}} (s : List A) (r : A)

/-- The unnormalized quotient localization is the same actual Cartesian open square. -/
theorem regularListPrincipalRawSquare :
    IsPullback
      (Spec.map (CommRingCat.ofHom (algebraMap (A ⧸ Ideal.ofList s)
        (Localization.Away (Ideal.Quotient.mk (Ideal.ofList s) r)))))
      (Spec.map (CommRingCat.ofHom (regularListPrincipalClosedMap s r)))
      (Spec.map (regularListQuotientMap s))
      (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away r)))) := by
  apply IsPullback.flip
  apply IsOpenImmersion.isPullback
  · rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    change algebraMap (A ⧸ Ideal.ofList s)
        (Localization.Away (Ideal.Quotient.mk (Ideal.ofList s) r))
        (Ideal.Quotient.mk (Ideal.ofList s) a) =
      regularListPrincipalClosedMap s r (algebraMap A (Localization.Away r) a)
    simp only [regularListPrincipalClosedMap, IsLocalization.Away.map, IsLocalization.map_eq]
  · have hA := Scheme.Hom.opensRange_localizationAway (R := A) r
    have hB := Scheme.Hom.opensRange_localizationAway (R := regularListQuotientRing s)
      (Ideal.Quotient.mk (Ideal.ofList s) r)
    exact (congrArg (fun U => (Spec.map (regularListQuotientMap s)) ⁻¹ᵁ U) hA).trans
      ((SpecMap_preimage_basicOpen (regularListQuotientMap s) r).trans
        ((congrArg PrimeSpectrum.basicOpen
          (show (regularListQuotientMap s) r = Ideal.Quotient.mk (Ideal.ofList s) r from rfl)).trans
            hB.symm))

local instance : IsClosedImmersion (Spec.map (CommRingCat.ofHom
    (regularListPrincipalClosedMap s r))) :=
  IsClosedImmersion.spec_of_surjective _
    (IsLocalization.map_surjective_of_surjective (Submonoid.powers r) (Localization.Away r)
      (Localization.Away (Ideal.Quotient.mk (Ideal.ofList s) r)) Ideal.Quotient.mk_surjective)

variable {L : (Spec A).Modules} (J : InjectiveResolution L)

/-- Actual principal restriction on the original sheaf resolution, with its original ordinary
closed-adjoint open comparison and original mapExtend comparison. -/
@[no_expose] def regularListPrincipalModelOpenIso :
    let S := CommRingCat.of (Localization.Away r)
    let T := CommRingCat.of (Localization.Away (Ideal.Quotient.mk (Ideal.ofList s) r))
    let σ : A ⟶ S := CommRingCat.ofHom (algebraMap A (Localization.Away r))
    let ψ : regularListQuotientRing s ⟶ T := CommRingCat.ofHom
      (algebraMap (A ⧸ Ideal.ofList s) (Localization.Away (Ideal.Quotient.mk (Ideal.ofList s) r)))
    let q' : S ⟶ T := CommRingCat.ofHom (regularListPrincipalClosedMap s r)
    ((restrictFunctor (Spec.map ψ)).mapHomologicalComplex (.up ℤ)).obj
      (closedImmersionRightAdjointRegularListResolutionComplex s J) ≅
    ((closedImmersionRightAdjoint (Spec.map q')).mapHomologicalComplex (.up ℤ)).obj
      (affineOpenRestrictedInjectiveResolution σ J).cochainComplex := by
  intro S T σ ψ q'
  let e := closedImmersionRightAdjointOpenIso (Spec.map ψ) (Spec.map q')
    (Spec.map (regularListQuotientMap s)) (Spec.map σ) (regularListPrincipalRawSquare s r)
  exact (Functor.mapHomologicalComplexCompIso e (.up ℤ)).app J.cochainComplex ≪≫
    ((Functor.mapHomologicalComplexCompIso
      (Iso.refl (restrictFunctor (Spec.map σ) ⋙ closedImmersionRightAdjoint (Spec.map q')))
      (.up ℤ)).symm.app J.cochainComplex) ≪≫
    ((closedImmersionRightAdjoint (Spec.map q')).mapHomologicalComplex (.up ℤ)).mapIso
      (J.cocomplex.mapExtendIso (restrictFunctor (Spec.map σ)) ComplexShape.embeddingUpNat)

/-- Every component of the sheaf model comparison uses the same two original arrows. -/
theorem regularListPrincipalModelOpenIso_hom_f (n : ℤ) :
    let S := CommRingCat.of (Localization.Away r)
    let T := CommRingCat.of (Localization.Away (Ideal.Quotient.mk (Ideal.ofList s) r))
    let σ : A ⟶ S := CommRingCat.ofHom (algebraMap A (Localization.Away r))
    let ψ : regularListQuotientRing s ⟶ T := CommRingCat.ofHom
      (algebraMap (A ⧸ Ideal.ofList s) (Localization.Away (Ideal.Quotient.mk (Ideal.ofList s) r)))
    let q' : S ⟶ T := CommRingCat.ofHom (regularListPrincipalClosedMap s r)
    (regularListPrincipalModelOpenIso s r J).hom.f n =
      (closedImmersionRightAdjointOpenIso (Spec.map ψ) (Spec.map q')
        (Spec.map (regularListQuotientMap s)) (Spec.map σ)
        (regularListPrincipalRawSquare s r)).hom.app (J.cochainComplex.X n) ≫
      (closedImmersionRightAdjoint (Spec.map q')).map
        ((J.cocomplex.mapExtendIso (restrictFunctor (Spec.map σ))
          ComplexShape.embeddingUpNat).hom.f n) := by
  rfl

/-- The actual affine geometric localization map is the original restriction of sections
followed by the same sheaf-model open isomorphism. -/
theorem regularListPrincipalResolutionMap_model_f (n : ℤ) :
    let T := CommRingCat.of (Localization.Away (Ideal.Quotient.mk (Ideal.ofList s) r))
    let ψ : regularListQuotientRing s ⟶ T := CommRingCat.ofHom
      (algebraMap (A ⧸ Ideal.ofList s) (Localization.Away (Ideal.Quotient.mk (Ideal.ofList s) r)))
    (closedImmersionQuotientLocalizationResolutionMap (Ideal.ofList s) r J).f n =
      affineOpenRestrictionSectionsMap ψ
        ((closedImmersionRightAdjoint (Spec.map (regularListQuotientMap s))).obj
          (J.cochainComplex.X n)) ≫
      (ModuleCat.restrictScalars ψ.hom).map
        ((moduleSpecΓFunctor (R := T)).map
          ((regularListPrincipalModelOpenIso s r J).hom.f n)) := by
  intro T ψ
  have hm := regularListPrincipalModelOpenIso_hom_f s r J n
  have hmap := congrArg (fun f => affineOpenRestrictionSectionsMap ψ
      ((closedImmersionRightAdjoint (Spec.map (regularListQuotientMap s))).obj
        (J.cochainComplex.X n)) ≫
    (ModuleCat.restrictScalars ψ.hom).map ((moduleSpecΓFunctor (R := T)).map f)) hm
  have h := closedImmersionQuotientLocalizationResolutionMap_f (Ideal.ofList s) r J n
  have hs : (closedImmersionQuotientLocalizationResolutionMap (Ideal.ofList s) r J).f n =
      affineOpenRestrictionSectionsMap ψ
        ((closedImmersionRightAdjoint (Spec.map (regularListQuotientMap s))).obj
          (J.cochainComplex.X n)) ≫
      (ModuleCat.restrictScalars ψ.hom).map ((moduleSpecΓFunctor (R := T)).map
        ((closedImmersionRightAdjointOpenIso (Spec.map ψ)
          (Spec.map (CommRingCat.ofHom (regularListPrincipalClosedMap s r)))
          (Spec.map (regularListQuotientMap s))
          (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away r))))
          (regularListPrincipalRawSquare s r)).hom.app (J.cochainComplex.X n) ≫
        (closedImmersionRightAdjoint
          (Spec.map (CommRingCat.ofHom (regularListPrincipalClosedMap s r)))).map
          ((J.cocomplex.mapExtendIso
            (restrictFunctor (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away r)))))
            ComplexShape.embeddingUpNat).hom.f n))) := by
    simpa only [Functor.map_comp, Category.assoc] using h
  exact hs.trans hmap.symm

end AlgebraicGeometry.Scheme.Modules
