/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.Dimension
public import Aglib.AlgebraicGeometry.Morphisms.Etale.StalkBaseChange
public import Aglib.AlgebraicGeometry.Properties.Regular.Basic
public import Aglib.AlgebraicGeometry.Stalk.CodimensionOne
public import Aglib.RingTheory.Etale.ZariskiNagataPurity
public import Mathlib.RingTheory.Etale.Pi

/-!
# Generic finite-etale normalization over a regular base

The actual relative normalization is etale if its pullbacks to the actual
codimension-one target stalks are etale. Its affine integral closures split
along the finite separable field factors of the given generic algebra. Purity
applies to those factors, and finite products recover the original chart.

The generic cover can be disconnected or empty. Normality of the base stalks,
the normalization stalk dimensions and the stalk-localization transport are
derived; no pointwise quasi-finite branch-purity family is used.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization

universe u

private theorem isUnramifiedAt_of_spec_stalkMap
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
    (q : PrimeSpectrum B)
    (h : ((Spec.map (CommRingCat.ofHom (algebraMap R B))).stalkMap q).hom.FormallyUnramified) :
    Algebra.IsUnramifiedAt R q.asIdeal := by
  let p := q.asIdeal.comap (algebraMap R B)
  let : p.IsPrime := q.2.comap (algebraMap R B)
  let : q.asIdeal.IsPrime := q.2
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime q.asIdeal) :=
    (Localization.localRingHom p q.asIdeal (algebraMap R B) rfl).toAlgebra
  let : IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime q.asIdeal) :=
    .of_algebraMap_eq fun r =>
      (Localization.localRingHom_to_map p q.asIdeal (algebraMap R B) rfl r).symm
  have hl := (RingHom.FormallyUnramified.respectsIso.arrow_mk_iso_iff
    (Scheme.arrowStalkMapSpecIso (CommRingCat.ofHom (algebraMap R B)) q)).mp h
  let : Algebra.FormallyUnramified (Localization.AtPrime p)
      (Localization.AtPrime q.asIdeal) := hl
  let : Algebra.FormallyUnramified R (Localization.AtPrime p) :=
    Algebra.FormallyUnramified.of_isLocalization p.primeCompl
  exact Algebra.FormallyUnramified.comp R (Localization.AtPrime p)
    (Localization.AtPrime q.asIdeal)

private theorem integralClosure_etale_of_unramified_stalk_dimension_one
    (R K A : Type u) [CommRing R] [IsDomain R] [IsRegularRing R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A] [Algebra.Etale K A]
    (hunram : ∀ q : PrimeSpectrum (integralClosure R A),
      ringKrullDim ((Spec (.of (integralClosure R A))).presheaf.stalk q) = 1 →
      RingHom.FormallyUnramified
        ((Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R A)))).stalkMap q).hom) :
    Algebra.Etale R (integralClosure R A) := by
  classical
  obtain ⟨ι, hι, L, hL, hKL, e, hfin⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod K A).mp inferInstance
  let := hι
  let := hL
  let := hKL
  let (i : ι) : Algebra R (L i) :=
    ((algebraMap K (L i)).comp (algebraMap R K)).toAlgebra
  let (i : ι) : IsScalarTower R K (L i) := IsScalarTower.of_algebraMap_eq' rfl
  let (i : ι) : Module.Finite K (L i) := (hfin i).1
  let (i : ι) : Algebra.IsSeparable K (L i) := (hfin i).2
  let (i : ι) : Module.Finite R (integralClosure R (L i)) :=
    IsIntegralClosure.finite R K (L i) _
  let (i : ι) : IsIntegrallyClosed (integralClosure R (L i)) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension (K := K)
  let (i : ι) : IsFractionRing (integralClosure R (L i)) (L i) :=
    integralClosure.isFractionRing_of_finite_extension K (L i)
  let eB := integralClosure.equivPi R A L (e.restrictScalars R)
  let φ : Spec (.of (∀ i, integralClosure R (L i))) ⟶ Spec (.of (integralClosure R A)) :=
    Spec.map (CommRingCat.ofHom eB.toRingHom)
  let : IsIso φ := isIso_SpecMap_iff.mpr eB.bijective
  have hfactor (i : ι) : Algebra.Etale R (integralClosure R (L i)) := by
    let : Algebra (FractionRing R) (L i) :=
      ((algebraMap K (L i)).comp (FractionRing.algEquiv R K).toRingHom).toAlgebra
    let : IsScalarTower R (FractionRing R) (L i) :=
      IsScalarTower.of_algebraMap_eq fun r =>
        congrArg (algebraMap K (L i)) ((FractionRing.algEquiv R K).commutes r).symm
    let : Algebra.IsSeparable (FractionRing R) (L i) := by
      apply Algebra.IsSeparable.of_equiv_equiv
        (FractionRing.algEquiv R K).symm.toRingEquiv (RingEquiv.refl (L i))
      ext k
      exact congrArg (algebraMap K (L i)) ((FractionRing.algEquiv R K).apply_symm_apply k)
    apply Algebra.etale_of_unramified_height_one_of_isRegularRing
      R (integralClosure R (L i)) (L i)
    intro q hq
    let : q.asIdeal.IsPrime := q.2
    let ψ : Spec (.of (integralClosure R (L i))) ⟶ Spec (.of (integralClosure R A)) :=
      Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun i => integralClosure R (L i)) i)) ≫ φ
    let : IsOpenImmersion ψ := by dsimp [ψ]; infer_instance
    have hψ : ψ ≫ Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R A))) =
        Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R (L i)))) := by
      dsimp [ψ, φ]
      rw [Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext r
      exact congrArg Subtype.val (congrFun (eB.commutes r) i)
    have hd : ringKrullDim
        ((Spec (.of (integralClosure R A))).presheaf.stalk (ψ q)) = 1 := by
      rw [(asIso (ψ.stalkMap q)).commRingCatIsoToRingEquiv.ringKrullDim]
      rw [(Spec.stalkIso (.of (integralClosure R (L i))) q).commRingCatIsoToRingEquiv.ringKrullDim,
        IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal, hq]
      rfl
    have hcomp : RingHom.FormallyUnramified
        ((ψ ≫ Spec.map (CommRingCat.ofHom
          (algebraMap R (integralClosure R A)))).stalkMap q).hom := by
      rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp]
      exact (hunram (ψ q) hd).comp (FormallyUnramified.stalkMap ψ q)
    rw [hψ] at hcomp
    exact isUnramifiedAt_of_spec_stalkMap R (integralClosure R (L i)) q hcomp
  let (i : ι) : Algebra.Etale R (integralClosure R (L i)) := hfactor i
  exact Algebra.Etale.of_equiv eB.symm

/-- On the actual normalization, purity of its affine field factors removes
the three former theorem-family inputs. The displayed local condition is on
the original morphism after pullback to each actual target divisor stalk. -/
theorem etale_of_regularStalks
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    [∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)]
    (C : Scheme.FiniteEtale (Spec X.functionField))
    (hlocal : ∀ x : Scheme.CodimensionOnePoint X,
      Etale (pullback.snd (C.obj.hom ≫ X.fromSpecStalk (genericPoint X)).fromNormalization
        (X.fromSpecStalk x.1))) :
    Etale (C.obj.hom ≫ X.fromSpecStalk (genericPoint X)).fromNormalization := by
  let (x : X) : IsIntegrallyClosed (X.presheaf.stalk x) :=
    IsRegularLocalRing.isIntegrallyClosed_of_regularLocal (X.presheaf.stalk x)
  let f := (C.obj.hom ≫ X.fromSpecStalk (genericPoint X)).fromNormalization
  have hunram (z : (C.obj.hom ≫ X.fromSpecStalk (genericPoint X)).normalization)
      (hz : ringKrullDim
        ((C.obj.hom ≫ X.fromSpecStalk (genericPoint X)).normalization.presheaf.stalk z) = 1) :
      (f.stalkMap z).hom.FormallyUnramified := by
    have hx : ringKrullDim (X.presheaf.stalk (f z)) = 1 :=
      (stalk_ringKrullDim X C z).symm.trans hz
    exact (RingHom.FormallyEtale.iff_formallyUnramified_and_formallySmooth _).mp
      (Scheme.LocalRing.Etale.stalkMap_formallyEtale_of_etale_stalkBaseChange f z
        (hlocal ⟨f z, hx⟩)) |>.1
  apply IsZariskiLocalAtTarget.of_iSup_eq_top
    (fun U : X.affineOpens => U.1) (iSup_affineOpens_eq_top X)
  intro U
  by_cases hne : Nonempty U.1
  · let := hne
    let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    let : IsRegularRing Γ(X, U.1) :=
      Scheme.RegularStalks.isRegularRing_sections (fun x => inferInstance) U.2
    let : IsIntegrallyClosed Γ(X, U.1) :=
      Scheme.isIntegrallyClosed_sections_of_isAffineOpen X U.1 U.2
    let : IsFractionRing Γ(X, U.1) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X U.1 U.2
    let B := integralClosure Γ(X, U.1)
      Γ(C.obj.left, (C.obj.hom ≫ X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U.1)
    let b := Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) B))
    let g := (C.obj.hom ≫ X.fromSpecStalk (genericPoint X)).normalizationOpenCover.f U
    let : IsOpenImmersion g := by dsimp [g]; infer_instance
    have hB : Algebra.Etale Γ(X, U.1) B := by
      apply integralClosure_etale_of_unramified_stalk_dimension_one
        Γ(X, U.1) X.functionField
      intro q hq
      have hd : ringKrullDim
          ((C.obj.hom ≫ X.fromSpecStalk (genericPoint X)).normalization.presheaf.stalk (g q))
            = 1 :=
        (asIso (g.stalkMap q)).commRingCatIsoToRingEquiv.ringKrullDim.trans hq
      have hcomp : ((g ≫ f).stalkMap q).hom.FormallyUnramified := by
        rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp]
        exact (hunram (g q) hd).comp (FormallyUnramified.stalkMap g q)
      have hw : g ≫ f = b ≫ U.2.fromSpec := (isPullback_chart X C U.1 U.2).w
      rw [hw, Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp] at hcomp
      exact RingHom.FormallyUnramified.of_comp hcomp
    have happ : (f.app U.1).hom.Etale := by
      dsimp [f]
      rw [Scheme.Hom.fromNormalization_app _ U.2]
      exact RingHom.Etale.stableUnderComposition _ _
        (RingHom.etale_algebraMap.mpr hB)
        (RingHom.Etale.of_bijective (ConcreteCategory.bijective_of_isIso
          ((C.obj.hom ≫ X.fromSpecStalk (genericPoint X)).normalizationObjIso U.2).inv))
    let : IsAffine U.1 := U.2
    let : IsAffine (f ⁻¹ᵁ U.1) := U.2.preimage f
    rw [← f.resLE_eq_morphismRestrict (U := U.1)]
    apply HasRingHomProperty.iff_of_isAffine.mpr
    apply (RingHom.Etale.respectsIso.arrow_mk_iso_iff
      (arrowResLEAppIso f U.1 (f ⁻¹ᵁ U.1) le_rfl)).mpr
    simpa only [Scheme.Hom.appLE_eq_app] using happ
  · let : IsEmpty U.1 := not_nonempty_iff.mp hne
    infer_instance

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization
