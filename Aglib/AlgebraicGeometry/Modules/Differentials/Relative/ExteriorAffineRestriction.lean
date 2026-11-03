/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorAffine
public import Aglib.AlgebraicGeometry.Modules.ExteriorPower.AffineMaps
public import Aglib.AlgebraicGeometry.Modules.ExteriorPower.Pushforward
public import Aglib.AlgebraicGeometry.Modules.Locality.AffineChartRestrictionMap
public import Aglib.RingTheory.Kaehler.Exterior.Map


/-!
# Original raw affine forms under restriction
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open scoped ModuleCat.Algebra

universe u


open AlgebraicGeometry.Scheme.Modules
open KaehlerDifferential

namespace AlgebraicGeometry.Scheme.Modules.Differentials

variable {X : Scheme.{u}} {Λ R D : CommRingCat.{u}}

/-- The actual smaller chart retains its original coefficient map. -/
theorem affineRestrictionCoefficient_eq (a : X ⟶ Spec Λ) (φ : R ⟶ D)
    (j : Spec R ⟶ X) (j' : Spec D ⟶ X) (hc : Spec.map φ ≫ j = j') :
    Spec.preimage (j' ≫ a) = Spec.preimage (j ≫ a) ≫ φ := by
  rw [← hc, Category.assoc, Spec.preimage_comp, Spec.preimage_map]

/-- Original commuting chart coefficients give their original scalar tower. -/
theorem affineRestrictionCoefficientTower (a : X ⟶ Spec Λ)
    (φ : R ⟶ D) (j : Spec R ⟶ X) (j' : Spec D ⟶ X)
    (hc : Spec.map φ ≫ j = j') :
    letI := φ.hom.toAlgebra
    letI := (Spec.preimage (j ≫ a)).hom.toAlgebra
    letI := (Spec.preimage (j' ≫ a)).hom.toAlgebra
    letI : SMul Λ D := Algebra.toSMul
    letI : SMul R D := Algebra.toSMul
    IsScalarTower Λ R D := by
  let := φ.hom.toAlgebra
  let := (Spec.preimage (j ≫ a)).hom.toAlgebra
  let := (Spec.preimage (j' ≫ a)).hom.toAlgebra
  let : SMul Λ D := Algebra.toSMul
  let : SMul R D := Algebra.toSMul
  apply IsScalarTower.of_algebraMap_eq'
  exact congrArg CommRingCat.Hom.hom (affineRestrictionCoefficient_eq a φ j j' hc)

private def differentialSectionsEquiv (a : X ⟶ Spec Λ)
    (j : Spec R ⟶ X) [IsOpenImmersion j] :
    letI := (Spec.preimage (j ≫ a)).hom.toAlgebra
    moduleSpecΓFunctor.obj ((relativeDifferentialSheaf a).restrict j) ≃ₗ[R]
      KaehlerDifferential Λ R := by
  let := (Spec.preimage (j ≫ a)).hom.toAlgebra
  exact ((moduleSpecΓFunctor.mapIso (relativeDifferentialAffineChartIso a j)) ≪≫
    (tilde.toTildeΓNatIso.app
      (CommRingCat.KaehlerDifferential (Spec.preimage (j ≫ a)))).symm).toLinearEquiv

private theorem differentialSectionsEquiv_symm_d (a : X ⟶ Spec Λ)
    (j : Spec R ⟶ X) [IsOpenImmersion j] (r : R) :
    letI := (Spec.preimage (j ≫ a)).hom.toAlgebra
    (differentialSectionsEquiv a j).symm (KaehlerDifferential.D Λ R r) =
      (relativeDifferentialDerivation a).d
        ((affineRestrictionUnitSectionsEquiv j).symm r) := by
  let := (Spec.preimage (j ≫ a)).hom.toAlgebra
  let e := differentialSectionsEquiv a j
  have hd := relativeDifferentialAffineChartIso_hom_d a j 1 r
  rw [PrimeSpectrum.basicOpen_one] at hd
  have he : e ((relativeDifferentialDerivation a).d
      ((j.appIso ⊤).inv ((Scheme.ΓSpecIso R).inv r))) = KaehlerDifferential.D Λ R r :=
    (congrArg (tilde.toTildeΓNatIso.app
      (CommRingCat.KaehlerDifferential (Spec.preimage (j ≫ a)))).inv hd).trans
        ((tilde.toTildeΓNatIso.app
          (CommRingCat.KaehlerDifferential (Spec.preimage (j ≫ a)))).hom_inv_id_apply _)
  apply e.injective
  exact (e.apply_symm_apply _).trans
    ((congrArg (fun z : Γ(X, j ''ᵁ ⊤) => e ((relativeDifferentialDerivation a).d z))
      (affineChartUnitSections_symm_apply j r)).trans he).symm

private theorem linearMap_eq_comp_of_kaehler_generators
    {A B S P Q N : Type*} [CommRing A] [CommRing B] [Algebra A B] [Semiring S]
    [AddCommMonoid P] [Module B P]
    [AddCommMonoid Q] [Module B Q] [Module S Q]
    [AddCommMonoid N] [Module B N] [Module S N]
    [LinearMap.CompatibleSMul Q N B S]
    (e : P ≃ₗ[B] KaehlerDifferential A B) (e' : Q ≃ₗ[S] N)
    (f : P →ₗ[B] Q) (g : KaehlerDifferential A B →ₗ[B] N)
    (hgen : ∀ r : B, f (e.symm (KaehlerDifferential.D A B r)) =
      e'.symm (g (KaehlerDifferential.D A B r))) :
    (e'.toLinearMap.restrictScalars B).comp f = g.comp e.toLinearMap := by
  apply (e.comp_toLinearMap_symm_eq g _).mp
  apply LinearMap.ext_on_range (KaehlerDifferential.span_range_derivation A B)
  intro r
  change e' (f (e.symm (KaehlerDifferential.D A B r))) =
    g (KaehlerDifferential.D A B r)
  exact (congrArg e' (hgen r)).trans (e'.apply_symm_apply _)

private theorem differentialSections_affineRestriction (a : X ⟶ Spec Λ)
    (φ : R ⟶ D) (j : Spec R ⟶ X) (j' : Spec D ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] [IsOpenImmersion (Spec.map φ)]
    (hc : Spec.map φ ≫ j = j') :
    letI := φ.hom.toAlgebra
    letI := (Spec.preimage (j ≫ a)).hom.toAlgebra
    letI := (Spec.preimage (j' ≫ a)).hom.toAlgebra
    letI : SMul Λ D := Algebra.toSMul
    letI : SMul R D := Algebra.toSMul
    letI := affineRestrictionCoefficientTower a φ j j' hc
    letI : IsScalarTower Λ Λ D :=
      IsScalarTower.of_algebraMap_eq' (by ext x; rfl)
    ((differentialSectionsEquiv a j').toLinearMap.restrictScalars R).comp
      (affineChartRestrictionLinearMap φ j j' hc (relativeDifferentialSheaf a)) =
    (KaehlerDifferential.map Λ Λ R D).comp
      (differentialSectionsEquiv a j).toLinearMap := by
  let := φ.hom.toAlgebra
  let := (Spec.preimage (j ≫ a)).hom.toAlgebra
  let := (Spec.preimage (j' ≫ a)).hom.toAlgebra
  let : SMul Λ D := Algebra.toSMul
  let : SMul R D := Algebra.toSMul
  let := affineRestrictionCoefficientTower a φ j j' hc
  let : IsScalarTower Λ Λ D :=
    IsScalarTower.of_algebraMap_eq' (by ext x; rfl)
  let e := differentialSectionsEquiv a j
  let e' := differentialSectionsEquiv a j'
  have hgen (r : R) :
      affineChartRestrictionLinearMap φ j j' hc (relativeDifferentialSheaf a)
        (e.symm (KaehlerDifferential.D Λ R r)) =
      e'.symm (KaehlerDifferential.map Λ Λ R D (KaehlerDifferential.D Λ R r)) := by
    have hu' : X.presheaf.map (homOfLE (affineChart_image_le φ j j' hc)).op
        ((affineRestrictionUnitSectionsEquiv j).symm r) =
        (affineRestrictionUnitSectionsEquiv j').symm
          (algebraMap R D r) := by
      apply (affineRestrictionUnitSectionsEquiv j').injective
      exact ((congrArg (affineRestrictionUnitSectionsEquiv j')
        (affineChartRestrictionLinearMap_apply φ j j' hc (SheafOfModules.unit X.ringCatSheaf)
          ((affineRestrictionUnitSectionsEquiv j).symm r))).symm.trans
            (affineChartUnitSections_restriction φ j j' hc
              ((affineRestrictionUnitSectionsEquiv j).symm r))).trans
        ((congrArg (algebraMap R D)
          ((affineRestrictionUnitSectionsEquiv j).apply_symm_apply r)).trans
            ((affineRestrictionUnitSectionsEquiv j').apply_symm_apply _).symm)
    have hsource := congrArg
      (affineChartRestrictionLinearMap φ j j' hc (relativeDifferentialSheaf a))
      (differentialSectionsEquiv_symm_d a j r)
    have hrestrict :=
      (affineChartRestrictionLinearMap_apply φ j j' hc (relativeDifferentialSheaf a)
        ((relativeDifferentialDerivation a).d
          ((affineRestrictionUnitSectionsEquiv j).symm r))).trans
        (relativeDifferentialDerivation_restrict a
          (homOfLE (affineChart_image_le φ j j' hc)).op
          ((affineRestrictionUnitSectionsEquiv j).symm r)).symm
    have hunit := congrArg
      (fun z : Γ(X, j' ''ᵁ ⊤) => (relativeDifferentialDerivation a).d z) hu'
    have htarget := (differentialSectionsEquiv_symm_d a j' (algebraMap R D r)).symm
    have hmap := congrArg e'.symm (KaehlerDifferential.map_D Λ Λ R D r).symm
    have hfinal := hsource.trans (hrestrict.trans (hunit.trans (htarget.trans hmap)))
    exact hfinal
  exact linearMap_eq_comp_of_kaehler_generators e e'
    (affineChartRestrictionLinearMap φ j j' hc (relativeDifferentialSheaf a))
    (KaehlerDifferential.map Λ Λ R D) hgen

private theorem rawSectionsEquiv_symm_wedge (a : X ⟶ Spec Λ)
    (j : Spec R ⟶ X) [IsOpenImmersion j] (n : ℕ)
    (v : Fin n → CommRingCat.KaehlerDifferential (Spec.preimage (j ≫ a))) :
    (rawFormsAffineSectionsEquiv a j n).symm (exteriorPower.ιMulti R n v) =
      wedgeAt X (relativeDifferentialSheaf a) n (j ''ᵁ ⊤)
        (fun i => (differentialSectionsEquiv a j).symm (v i)) := by
  let P := CommRingCat.KaehlerDifferential (Spec.preimage (j ≫ a))
  change (moduleExteriorPowerRestrictionIso j (relativeDifferentialSheaf a) n).hom.val.app
    (op ⊤)
    (((moduleExteriorPowerFunctor (Spec R) n).map
      (relativeDifferentialAffineChartIso a j).inv).val.app (op ⊤)
        ((exteriorTildeIso P n).inv.val.app (op ⊤)
          (tilde.toOpen (ModuleCat.of R (⋀[R]^n P)) ⊤
            (exteriorPower.ιMulti R n v)))) = _
  rw [exteriorTildeIso_inv_mk_top]
  refine (congrArg
    ((moduleExteriorPowerRestrictionIso j (relativeDifferentialSheaf a) n).hom.val.app (op ⊤))
    (SheafOfModulesOfCommRing.exteriorPowerFunctor_map_mk (Spec R).sheaf
      (relativeDifferentialAffineChartIso a j).inv n (op ⊤)
      (fun i => tilde.toOpen P ⊤ (v i)))).trans ?_
  exact moduleExteriorPowerRestrictionIso_hom_mk j (relativeDifferentialSheaf a) n ⊤ _

private theorem coordinate_apply_of_comp_symm
    {K : Type*} [Semiring K]
    {A : Type*} {B : Type*} {P : Type*} {Q : Type*}
    [AddCommMonoid A] [Module K A]
    [AddCommMonoid B] [Module K B]
    [AddCommMonoid P] [Module K P]
    [AddCommMonoid Q] [Module K Q]
    (e : A ≃ₗ[K] P) (f : A →ₗ[K] B) (q : P →ₗ[K] Q)
    {l : B →ₗ[K] Q}
    (h : (l.comp f).comp e.symm.toLinearMap = q)
    (m : A) : l (f m) = q (e m) := by
  exact (congrArg (fun z => l (f z)) (e.symm_apply_apply m)).symm.trans
    (LinearMap.congr_fun h (e m))

/-- Evaluation of the original raw coordinate restriction square. -/
theorem rawFormsAffineSectionsEquiv_affineRestriction_apply
    (a : X ⟶ Spec Λ) (φ : R ⟶ D)
    (j : Spec R ⟶ X) (j' : Spec D ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] [IsOpenImmersion (Spec.map φ)]
    (hc : Spec.map φ ≫ j = j') (n : ℕ)
    (m : moduleSpecΓFunctor.obj
      ((moduleExteriorPower X (relativeDifferentialSheaf a) n).restrict j)) :
    letI := φ.hom.toAlgebra
    letI := (Spec.preimage (j ≫ a)).hom.toAlgebra
    letI := (Spec.preimage (j' ≫ a)).hom.toAlgebra
    letI : SMul Λ D := Algebra.toSMul
    letI : SMul R D := Algebra.toSMul
    letI : IsScalarTower Λ R D :=
      IsScalarTower.of_algebraMap_eq'
        (congrArg CommRingCat.Hom.hom (affineRestrictionCoefficient_eq a φ j j' hc))
    rawFormsAffineSectionsEquiv a j' n
      (affineChartRestrictionLinearMap φ j j' hc
        (moduleExteriorPower X (relativeDifferentialSheaf a) n) m) =
      KaehlerDifferential.mapExterior Λ R D n (rawFormsAffineSectionsEquiv a j n m) := by
  let := φ.hom.toAlgebra
  let := (Spec.preimage (j ≫ a)).hom.toAlgebra
  let := (Spec.preimage (j' ≫ a)).hom.toAlgebra
  let : SMul Λ D := Algebra.toSMul
  let : SMul R D := Algebra.toSMul
  let := affineRestrictionCoefficientTower a φ j j' hc
  let : IsScalarTower Λ Λ D :=
    IsScalarTower.of_algebraMap_eq' (by ext x; rfl)
  let M := moduleExteriorPower X (relativeDifferentialSheaf a) n
  let e := rawFormsAffineSectionsEquiv a j n
  let e' := rawFormsAffineSectionsEquiv a j' n
  have he : ((e'.toLinearMap.restrictScalars R).comp
      (affineChartRestrictionLinearMap φ j j' hc M)).comp e.symm.toLinearMap =
      KaehlerDifferential.mapExterior Λ R D n := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change e' (affineChartRestrictionLinearMap φ j j' hc M
      (e.symm (exteriorPower.ιMulti R n v))) = _
    refine (congrArg (fun z => e' (affineChartRestrictionLinearMap φ j j' hc M z))
      (rawSectionsEquiv_symm_wedge a j n v)).trans ?_
    refine (congrArg e'
      ((affineChartRestrictionLinearMap_apply φ j j' hc M _).trans
        (wedgeAt_naturality X (relativeDifferentialSheaf a) n
          (homOfLE (affineChart_image_le φ j j' hc))
          (fun i => (differentialSectionsEquiv a j).symm (v i))))).trans ?_
    have hv (i : Fin n) : (relativeDifferentialSheaf a).presheaf.map
        (homOfLE (affineChart_image_le φ j j' hc)).op ((differentialSectionsEquiv a j).symm (v i)) =
        (differentialSectionsEquiv a j').symm
          (KaehlerDifferential.map Λ Λ R D (v i)) := by
      apply (differentialSectionsEquiv a j').injective
      have h : differentialSectionsEquiv a j'
          (affineChartRestrictionLinearMap φ j j' hc (relativeDifferentialSheaf a)
            ((differentialSectionsEquiv a j).symm (v i))) =
          KaehlerDifferential.map Λ Λ R D
            (differentialSectionsEquiv a j ((differentialSectionsEquiv a j).symm (v i))) :=
        LinearMap.congr_fun (differentialSections_affineRestriction a φ j j' hc)
          ((differentialSectionsEquiv a j).symm (v i))
      exact ((congrArg (differentialSectionsEquiv a j')
        (affineChartRestrictionLinearMap_apply φ j j' hc (relativeDifferentialSheaf a)
          ((differentialSectionsEquiv a j).symm (v i)))).symm.trans h).trans
        ((congrArg (KaehlerDifferential.map Λ Λ R D)
          ((differentialSectionsEquiv a j).apply_symm_apply (v i))).trans
            ((differentialSectionsEquiv a j').apply_symm_apply _).symm)
    rw [show (fun i => (relativeDifferentialSheaf a).presheaf.map
      (homOfLE (affineChart_image_le φ j j' hc)).op ((differentialSectionsEquiv a j).symm (v i))) =
      (fun i => (differentialSectionsEquiv a j').symm
        (KaehlerDifferential.map Λ Λ R D (v i))) from funext hv]
    refine (congrArg e' (rawSectionsEquiv_symm_wedge a j' n
      (fun i => KaehlerDifferential.map Λ Λ R D (v i))).symm).trans ?_
    exact (e'.apply_symm_apply _).trans
      (KaehlerDifferential.mapExterior_ιMulti Λ R D n v).symm
  have hm := coordinate_apply_of_comp_symm e
    (affineChartRestrictionLinearMap φ j j' hc M) (KaehlerDifferential.mapExterior Λ R D n) he m
  exact hm

/-- Actual raw affine coordinates preserve restriction between the specified charts.
No Noetherianity, finite type, nonempty-open or nonzero-element premise is needed. -/
theorem rawFormsAffineSectionsEquiv_affineRestriction (a : X ⟶ Spec Λ)
    (φ : R ⟶ D) (j : Spec R ⟶ X) (j' : Spec D ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] [IsOpenImmersion (Spec.map φ)]
    (hc : Spec.map φ ≫ j = j') (n : ℕ) :
    letI := φ.hom.toAlgebra
    letI := (Spec.preimage (j ≫ a)).hom.toAlgebra
    letI := (Spec.preimage (j' ≫ a)).hom.toAlgebra
    letI : SMul Λ D := Algebra.toSMul
    letI : SMul R D := Algebra.toSMul
    letI : IsScalarTower Λ R D :=
      IsScalarTower.of_algebraMap_eq'
        (congrArg CommRingCat.Hom.hom (affineRestrictionCoefficient_eq a φ j j' hc))
    let M := moduleExteriorPower X (relativeDifferentialSheaf a) n
    (((rawFormsAffineSectionsEquiv a j' n).toLinearMap).restrictScalars R).comp
      (((moduleSpecΓFunctor.map
        (affineChartRestrictionIso φ j j' hc M).hom).hom.restrictScalars R).comp
          (moduleSpecΓFunctor.map ((restrictAdjunction (Spec.map φ)).unit.app (M.restrict j)) ≫
            (pushforwardGlobalSectionsIso φ).hom.app
              ((M.restrict j).restrict (Spec.map φ))).hom) =
      (KaehlerDifferential.mapExterior Λ R D n).comp
        (rawFormsAffineSectionsEquiv a j n).toLinearMap := by
  let := φ.hom.toAlgebra
  let := (Spec.preimage (j ≫ a)).hom.toAlgebra
  let := (Spec.preimage (j' ≫ a)).hom.toAlgebra
  let : SMul Λ D := Algebra.toSMul
  let : SMul R D := Algebra.toSMul
  let := affineRestrictionCoefficientTower a φ j j' hc
  apply LinearMap.ext
  intro m
  exact rawFormsAffineSectionsEquiv_affineRestriction_apply a φ j j' hc n m

private theorem mapExterior_algebra_congr
    (K A B : Type*) [CommRing K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B]
    (a b : Algebra A B) (hab : a = b) (n : ℕ) :
    letI : SMul K B := Algebra.toSMul
    letI := a
    letI : SMul A B := Algebra.toSMul
    ∀ [_towerA : IsScalarTower K A B],
    let qa : (⋀[A]^n (KaehlerDifferential K A)) →
      (⋀[B]^n (KaehlerDifferential K B)) := KaehlerDifferential.mapExterior K A B n
    letI := b
    letI : SMul A B := Algebra.toSMul
    ∀ [_towerB : IsScalarTower K A B],
    qa = (KaehlerDifferential.mapExterior K A B n :
      (⋀[A]^n (KaehlerDifferential K A)) → (⋀[B]^n (KaehlerDifferential K B))) := by
  cases hab
  dsimp only
  intro hA hB
  rfl

/-- The smaller chart retains the original coefficient map, not a selected algebra. -/
theorem affinePrincipalCoefficient_eq (a : X ⟶ Spec Λ)
    (j : Spec R ⟶ X) (t : R) :
    Spec.preimage ((principalOpen R t ≫ j) ≫ a) =
      Spec.preimage (j ≫ a) ≫
        CommRingCat.ofHom (algebraMap R (Localization.Away t)) :=
  affineRestrictionCoefficient_eq a
    (CommRingCat.ofHom (algebraMap R (Localization.Away t)))
    j (principalOpen R t ≫ j) rfl

/-- Actual raw affine coordinates preserve the whole original principal restriction.
No Noetherianity, finite type, nonempty-open or nonzero-element premise is needed. -/
theorem rawFormsAffineSectionsEquiv_principal (a : X ⟶ Spec Λ)
    (j : Spec R ⟶ X) [IsOpenImmersion j] (t : R) (n : ℕ) :
    letI := (Spec.preimage (j ≫ a)).hom.toAlgebra
    letI := (Spec.preimage ((principalOpen R t ≫ j) ≫ a)).hom.toAlgebra
    letI : SMul Λ (Localization.Away t) := Algebra.toSMul
    letI : SMul R (Localization.Away t) := Algebra.toSMul
    letI : IsScalarTower Λ R (Localization.Away t) :=
      IsScalarTower.of_algebraMap_eq'
        (congrArg CommRingCat.Hom.hom (affinePrincipalCoefficient_eq a j t))
    let M := moduleExteriorPower X (relativeDifferentialSheaf a) n
    (((rawFormsAffineSectionsEquiv a (principalOpen R t ≫ j) n).toLinearMap).restrictScalars R).comp
      (((moduleSpecΓFunctor.map
        ((restrictFunctorComp (principalOpen R t) j).inv.app M)).hom.restrictScalars R).comp
          (toPrincipalGlobalSections R t (M.restrict j))) =
      (KaehlerDifferential.mapExterior Λ R (Localization.Away t) n).comp
        (rawFormsAffineSectionsEquiv a j n).toLinearMap := by
  let := (Spec.preimage (j ≫ a)).hom.toAlgebra
  let := (Spec.preimage ((principalOpen R t ≫ j) ≫ a)).hom.toAlgebra
  let : SMul Λ (Localization.Away t) := Algebra.toSMul
  let : SMul R (Localization.Away t) := Algebra.toSMul
  let : IsScalarTower Λ R (Localization.Away t) :=
    IsScalarTower.of_algebraMap_eq'
      (congrArg CommRingCat.Hom.hom (affinePrincipalCoefficient_eq a j t))
  let M := moduleExteriorPower X (relativeDifferentialSheaf a) n
  let aRD : @Algebra R (Localization.Away t) CommRing.toCommSemiring
      (@CommRing.toCommSemiring (Localization.Away t)
        (inferInstance : CommRing (Localization.Away t))).toSemiring := inferInstance
  have hA : (CommRingCat.ofHom (algebraMap R (Localization.Away t))).hom.toAlgebra =
      aRD := toAlgebra_algebraMap
  have hMap := mapExterior_algebra_congr Λ R (CommRingCat.of (Localization.Away t))
    (CommRingCat.ofHom (algebraMap R (Localization.Away t))).hom.toAlgebra aRD hA n
    (_towerA := affineRestrictionCoefficientTower a
      (CommRingCat.ofHom (algebraMap R (Localization.Away t)))
      j (principalOpen R t ≫ j) rfl)
    (_towerB := inferInstance)
  have h := rawFormsAffineSectionsEquiv_affineRestriction a
    (CommRingCat.ofHom (algebraMap R (Localization.Away t)))
    j (principalOpen R t ≫ j) rfl n
  have hfun := congrArg DFunLike.coe h
  have hfun' := hfun.trans
    (congrArg (fun f => f ∘ (rawFormsAffineSectionsEquiv a j n)) hMap)
  apply LinearMap.ext
  intro m
  have hm := congrFun hfun' m
  change rawFormsAffineSectionsEquiv a (principalOpen R t ≫ j) n
      (affineChartRestrictionLinearMap (CommRingCat.ofHom (algebraMap R (Localization.Away t)))
        j (principalOpen R t ≫ j) rfl M m) = _ at hm
  rw [affineChartRestrictionLinearMap_principal_apply] at hm
  exact hm

/-- Existing raw coordinates on actual affine opens preserve the whole original
section restriction. No localization, Noetherianity, or finite type is assumed. -/
theorem rawFormsAffineSectionsEquiv_restrict (a : X ⟶ Spec Λ)
    (U V : X.affineOpens) (i : V.val ⟶ U.val) (n : ℕ) :
    letI : IsOpenImmersion U.property.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.property
    letI : IsOpenImmersion V.property.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec V.property
    letI := (X.presheaf.map i.op).hom.toAlgebra
    letI := (Spec.preimage (U.property.fromSpec ≫ a)).hom.toAlgebra
    letI := (Spec.preimage (V.property.fromSpec ≫ a)).hom.toAlgebra
    letI : SMul Λ Γ(X, V) := Algebra.toSMul
    letI : SMul Γ(X, U) Γ(X, V) := Algebra.toSMul
    letI : IsScalarTower Λ Γ(X, U) Γ(X, V) :=
      IsScalarTower.of_algebraMap_eq'
        (congrArg CommRingCat.Hom.hom
          (affineRestrictionCoefficient_eq a (X.presheaf.map i.op)
            U.property.fromSpec V.property.fromSpec (U.property.map_fromSpec V.property i.op)))
    let M := moduleExteriorPower X (relativeDifferentialSheaf a) n
    (fun m : Γ(M, U) => rawFormsAffineSectionsEquiv a V.property.fromSpec n
      ((affineChartΓIso V M).inv (M.val.map i.op m))) =
      (fun m => KaehlerDifferential.mapExterior Λ Γ(X, U) Γ(X, V) n
        (rawFormsAffineSectionsEquiv a U.property.fromSpec n ((affineChartΓIso U M).inv m))) := by
  let : IsOpenImmersion U.property.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.property
  let : IsOpenImmersion V.property.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec V.property
  let := (X.presheaf.map i.op).hom.toAlgebra
  let := (Spec.preimage (U.property.fromSpec ≫ a)).hom.toAlgebra
  let := (Spec.preimage (V.property.fromSpec ≫ a)).hom.toAlgebra
  let : SMul Λ Γ(X, V) := Algebra.toSMul
  let : SMul Γ(X, U) Γ(X, V) := Algebra.toSMul
  let : IsOpenImmersion (Spec.map (X.presheaf.map i.op)) :=
    affineOpenRestriction_isOpenImmersion U V i
  let := affineRestrictionCoefficientTower a (X.presheaf.map i.op)
    U.property.fromSpec V.property.fromSpec (U.property.map_fromSpec V.property i.op)
  let M := moduleExteriorPower X (relativeDifferentialSheaf a) n
  funext m
  have h := LinearMap.congr_fun
    (rawFormsAffineSectionsEquiv_affineRestriction a (X.presheaf.map i.op)
      U.property.fromSpec V.property.fromSpec (U.property.map_fromSpec V.property i.op) n)
    ((affineChartΓIso U M).inv m)
  change rawFormsAffineSectionsEquiv a V.property.fromSpec n
    (affineChartRestrictionLinearMap (X.presheaf.map i.op) U.property.fromSpec V.property.fromSpec
      (U.property.map_fromSpec V.property i.op) M ((affineChartΓIso U M).inv m)) = _ at h
  rw [affineChartRestrictionLinearMap_affineOpens] at h
  exact h


end AlgebraicGeometry.Scheme.Modules.Differentials
