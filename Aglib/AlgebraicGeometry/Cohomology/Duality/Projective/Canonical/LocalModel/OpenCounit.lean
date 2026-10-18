/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Principal.AmbientIsomorphism.Model
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalModel.OpenCounit.Sections
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalModel.OpenCounit.Homology
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalModel.OpenCounit.Transport
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Refinements.OpenCoefficient.Units
public import Aglib.AlgebraicGeometry.Modules.Complex.Tilde.HomologyMap
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# The original open model and the actual affine counit

The scalar adjoint of the original sections-resolution map acts through
the original affine counit, degree by degree and on homology. The counit
is used as a map on arbitrary sheaf complexes. No quasicoherence of
resolution terms or general invertibility of that counit is assumed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex AlgebraicGeometry Opposite
open scoped TensorProduct ChangeOfRings

universe u
namespace AlgebraicGeometry.Scheme.Modules

section General
variable {R S : CommRingCat.{u}} (ψ : R ⟶ S) [IsOpenImmersion (Spec.map ψ)]

/-- The original affine pullback comparison followed by the original open
restriction comparison, in the direction of scalar extension. -/
def canonicalOpenTildeIso :
    ModuleCat.extendScalars ψ.hom ⋙ tilde.functor S ≅
      tilde.functor R ⋙ restrictFunctor (Spec.map ψ) :=
  (tildePullbackIso ψ).symm ≪≫
    Functor.isoWhiskerLeft (tilde.functor R) (restrictFunctorIsoPullback (Spec.map ψ)).symm

/-- The native open comparison retains the original unit-section morphism. -/
theorem canonicalOpenTildeIso_unitSection (E : ModuleCat.{u} R) (x : E) :
    canonicalAffineUnitSection ((ModuleCat.extendScalars ψ.hom).obj E)
        ((1 : S) ⊗ₜ[R,ψ.hom] x) ≫ (canonicalOpenTildeIso ψ).hom.app E =
      (restrictUnitIso (Spec.map ψ)).inv ≫
        (restrictFunctor (Spec.map ψ)).map (canonicalAffineUnitSection E x) := by
  have hu : (pullbackUnitIso (Spec.map ψ)).inv ≫
      (restrictFunctorIsoPullback (Spec.map ψ)).inv.app
        (SheafOfModules.unit (Spec R).ringCatSheaf) =
    (restrictUnitIso (Spec.map ψ)).inv := by
    apply (cancel_mono (restrictUnitIso (Spec.map ψ)).hom).mp
    rw [Category.assoc, restrictFunctorIsoPullback_inv_unit]
    change (pullbackUnitIso (Spec.map ψ)).inv ≫ (pullbackUnitIso (Spec.map ψ)).hom = _
    rw [Iso.inv_hom_id, Iso.inv_hom_id]
  have hn := (restrictFunctorIsoPullback (Spec.map ψ)).inv.naturality
    (canonicalAffineUnitSection E x)
  change (pullback (Spec.map ψ)).map (canonicalAffineUnitSection E x) ≫
      (restrictFunctorIsoPullback (Spec.map ψ)).inv.app (tilde E) =
    (restrictFunctorIsoPullback (Spec.map ψ)).inv.app
      (SheafOfModules.unit (Spec R).ringCatSheaf) ≫
      (restrictFunctor (Spec.map ψ)).map (canonicalAffineUnitSection E x) at hn
  rw [← canonicalAffineUnitSection_pullback ψ E x]
  change ((pullbackUnitIso (Spec.map ψ)).inv ≫
      (pullback (Spec.map ψ)).map (canonicalAffineUnitSection E x) ≫
      (tildePullbackIso ψ).hom.app E) ≫
    (tildePullbackIso ψ).inv.app E ≫
      (restrictFunctorIsoPullback (Spec.map ψ)).inv.app (tilde E) = _
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [hn, ← Category.assoc, hu]

/-- A native unit tensor represents the same original section after open restriction. -/
theorem canonicalOpenTildeIso_one_tmul (E : ModuleCat.{u} R) (x : E)
    (U : (Spec S).Opens) :
    ((canonicalOpenTildeIso ψ).hom.app E).val.app (op U)
        (tilde.toOpen ((ModuleCat.extendScalars ψ.hom).obj E) U
          ((1 : S) ⊗ₜ[R,ψ.hom] x)) =
      tilde.toOpen E ((Spec.map ψ) ''ᵁ U) x := by
  have ht := congrArg (fun k => k.val.app (op U) (1 : Γ(Spec S, U)))
    (canonicalOpenTildeIso_unitSection ψ E x)
  change ((canonicalOpenTildeIso ψ).hom.app E).val.app (op U)
      ((canonicalAffineUnitSection ((ModuleCat.extendScalars ψ.hom).obj E)
        ((1 : S) ⊗ₜ[R,ψ.hom] x)).val.app (op U) (1 : Γ(Spec S, U))) =
    (canonicalAffineUnitSection E x).val.app (op ((Spec.map ψ) ''ᵁ U))
      (((Spec.map ψ).appIso U).inv (1 : Γ(Spec S, U))) at ht
  rw [canonicalAffineUnitSection_app, ((Spec.map ψ).appIso U).inv.hom.map_one,
    canonicalAffineUnitSection_app] at ht
  exact ht

/-- The same native comparison on the actual module complex. -/
def canonicalOpenTildeComplexIso (C : CochainComplex (ModuleCat.{u} R) ℤ) :
    ((tilde.functor S).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.extendScalars ψ.hom).mapHomologicalComplex (.up ℤ)).obj C) ≅
      ((restrictFunctor (Spec.map ψ)).mapHomologicalComplex (.up ℤ)).obj
        (((tilde.functor R).mapHomologicalComplex (.up ℤ)).obj C) :=
  (Functor.mapHomologicalComplexCompIso (canonicalOpenTildeIso ψ) (.up ℤ)).app C ≪≫
    ((Functor.mapHomologicalComplexCompIso
      (Iso.refl (tilde.functor R ⋙ restrictFunctor (Spec.map ψ))) (.up ℤ)).app C).symm

/-- Every component is the same original pullback/restriction comparison. -/
theorem canonicalOpenTildeComplexIso_hom_f
    (C : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    (canonicalOpenTildeComplexIso ψ C).hom.f n =
      (tildePullbackIso ψ).inv.app (C.X n) ≫
        (restrictFunctorIsoPullback (Spec.map ψ)).inv.app (tilde (C.X n)) := by
  rfl

/-- Exact tilde followed by homology of the original affine counit. This
is the forward map of the existing native isomorphism when its particular
counit is a quasi-isomorphism. -/
def canonicalTildeHomologyCounitMap (K : CochainComplex (Spec R).Modules ℤ) (n : ℤ) :
    tilde (((moduleSpecΓFunctor (R := R)).mapHomologicalComplex (.up ℤ)).obj K |>.homology n) ⟶
      K.homology n :=
  (((((moduleSpecΓFunctor (R := R)).mapHomologicalComplex (.up ℤ)).obj K).sc n).mapHomologyIso
      (tilde.functor R)).inv ≫
    homologyMap (Complex.tildeGlobalSectionsCounit R (.up ℤ) K) n

/-- The special native homology isomorphism has precisely this original
counit map; no new invertibility assertion is used. -/
theorem canonicalTildeHomologyCounitMap_eq
    (K : CochainComplex (Spec R).Modules ℤ)
    [QuasiIso (Complex.tildeGlobalSectionsCounit R (.up ℤ) K)] (n : ℤ) :
    canonicalTildeHomologyCounitMap (R := R) K n =
      (Complex.tildeGlobalSectionsHomologyIso R (.up ℤ) K n).hom := rfl

private theorem tildeHomologyCounitMap_naturality
    (C : CochainComplex (ModuleCat.{u} R) ℤ) (K : CochainComplex (Spec R).Modules ℤ)
    (q : C ⟶ ((moduleSpecΓFunctor (R := R)).mapHomologicalComplex (.up ℤ)).obj K) (n : ℤ) :
    (tilde.functor R).map (homologyMap q n) ≫ canonicalTildeHomologyCounitMap K n =
      ((C.sc n).mapHomologyIso (tilde.functor R)).inv ≫
        homologyMap (((tilde.functor R).mapHomologicalComplex (.up ℤ)).map q ≫
          Complex.tildeGlobalSectionsCounit R (.up ℤ) K) n := by
  have hn := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (.up ℤ) n).map q)
    (tilde.functor R)
  change (tilde.functor R).map (homologyMap q n) ≫
      (((((moduleSpecΓFunctor (R := R)).mapHomologicalComplex (.up ℤ)).obj K).sc n).mapHomologyIso
        (tilde.functor R)).inv =
    ((C.sc n).mapHomologyIso (tilde.functor R)).inv ≫
      homologyMap (((tilde.functor R).mapHomologicalComplex (.up ℤ)).map q) n at hn
  simp only [canonicalTildeHomologyCounitMap, homologyMap_comp]
  rw [← Category.assoc, hn]
  exact Category.assoc _ _ _

end General

section Geometry
variable {A A' B B' : CommRingCat.{u}}
  (φ : A ⟶ A') (σ : A ⟶ B) (τ : A' ⟶ B') (ψ : B ⟶ B')
  [IsOpenImmersion (Spec.map φ)] [IsOpenImmersion (Spec.map ψ)]
  [IsClosedImmersion (Spec.map σ)] [IsClosedImmersion (Spec.map τ)]
  (h : IsPullback (Spec.map ψ) (Spec.map τ) (Spec.map σ) (Spec.map φ))
  {L : (Spec A).Modules} (J : InjectiveResolution L)

/-- The actual source sheaf model on the supplied resolution. -/
abbrev canonicalAmbientSourceSheafComplex :=
  ((closedImmersionRightAdjoint (Spec.map σ)).mapHomologicalComplex (.up ℤ)).obj J.cochainComplex

/-- The actual target sheaf model on the same restricted resolution. -/
abbrev canonicalAmbientTargetSheafComplex :=
  ((closedImmersionRightAdjoint (Spec.map τ)).mapHomologicalComplex (.up ℤ)).obj
    (affineOpenRestrictedInjectiveResolution φ J).cochainComplex

/-- The native scalar adjoint of the original geometric sections map. -/
def canonicalAmbientScalarResolutionMap :
    ((ModuleCat.extendScalars ψ.hom).mapHomologicalComplex (.up ℤ)).obj
        (closedImmersionSourceResolutionComplex J σ) ⟶
      closedImmersionSourceResolutionComplex (affineOpenRestrictedInjectiveResolution φ J) τ :=
  (((ModuleCat.extendRestrictScalarsAdj ψ.hom).mapHomologicalComplex (.up ℤ)).homEquiv _ _).symm
    (canonicalAmbientResolutionMap φ σ τ ψ h J)

/-- The ordinary scalar adjoint of the original module-homology map. -/
def canonicalAmbientHomologyScalarMap (n : ℤ) :
    (ModuleCat.extendScalars ψ.hom).obj
        ((closedImmersionSourceResolutionComplex J σ).homology n) ⟶
      (closedImmersionSourceResolutionComplex
        (affineOpenRestrictedInjectiveResolution φ J) τ).homology n :=
  ((ModuleCat.extendRestrictScalarsAdj ψ.hom).homEquiv _ _).symm
    (canonicalAmbientHomologyMap φ σ τ ψ h J n)

/-- Its unit tensors retain the actual original module-homology map. -/
theorem canonicalAmbientHomologyScalarMap_one_tmul (n : ℤ)
    (x : (closedImmersionSourceResolutionComplex J σ).homology n) :
    canonicalAmbientHomologyScalarMap φ σ τ ψ h J n ((1 : B') ⊗ₜ[B,ψ.hom] x) =
      canonicalAmbientHomologyMap φ σ τ ψ h J n x := by
  have hmap := ((ModuleCat.extendRestrictScalarsAdj ψ.hom).homEquiv _ _).apply_symm_apply
    (canonicalAmbientHomologyMap φ σ τ ψ h J n)
  have he := ModuleCat.extendRestrictScalarsAdj_homEquiv_apply
    (canonicalAmbientHomologyScalarMap φ σ τ ψ h J n) x
  exact he.symm.trans (ConcreteCategory.congr_hom hmap x)

/-- Its component is the original ordinary scalar adjoint. -/
theorem canonicalAmbientScalarResolutionMap_f (n : ℤ) :
    (canonicalAmbientScalarResolutionMap φ σ τ ψ h J).f n =
      ((ModuleCat.extendRestrictScalarsAdj ψ.hom).homEquiv _ _).symm
        ((canonicalAmbientResolutionMap φ σ τ ψ h J).f n) := rfl

/-- The native scalar adjoint of the actual resolution map commutes with
the original affine counit and original geometric open model map. -/
theorem canonicalAmbientScalarResolutionMap_counit :
    ((tilde.functor B').mapHomologicalComplex (.up ℤ)).map
        (canonicalAmbientScalarResolutionMap φ σ τ ψ h J) ≫
        Complex.tildeGlobalSectionsCounit B' (.up ℤ)
          (canonicalAmbientTargetSheafComplex φ τ J) =
      (canonicalOpenTildeComplexIso ψ (closedImmersionSourceResolutionComplex J σ)).hom ≫
        ((restrictFunctor (Spec.map ψ)).mapHomologicalComplex (.up ℤ)).map
          (Complex.tildeGlobalSectionsCounit B (.up ℤ)
            (canonicalAmbientSourceSheafComplex σ J)) ≫
        (canonicalAmbientModelOpenIso φ σ τ ψ h J).hom := by
  ext n : 1
  change (tilde.functor B').map
      (((ModuleCat.extendRestrictScalarsAdj ψ.hom).homEquiv _ _).symm
        ((canonicalAmbientResolutionMap φ σ τ ψ h J).f n)) ≫
      ((canonicalAmbientTargetSheafComplex φ τ J).X n).fromTildeΓ =
    (tildePullbackIso ψ).inv.app
        (moduleSpecΓFunctor.obj ((canonicalAmbientSourceSheafComplex σ J).X n)) ≫
      (restrictFunctorIsoPullback (Spec.map ψ)).inv.app
        (tilde (moduleSpecΓFunctor.obj ((canonicalAmbientSourceSheafComplex σ J).X n))) ≫
      (restrictFunctor (Spec.map ψ)).map
        ((canonicalAmbientSourceSheafComplex σ J).X n).fromTildeΓ ≫
      (canonicalAmbientModelOpenIso φ σ τ ψ h J).hom.f n
  rw [canonicalAmbientResolutionMap_model_f]
  exact affineOpenRestrictionSectionsMap_counit ψ _ _ _

/-- Homology of this same original counit square. It uses the counit
as a map on both complexes, with no assumption on its invertibility. -/
theorem canonicalAmbientScalarResolutionMap_homology_counit (n : ℤ) :
    (tilde.functor B').map
        (homologyMap (canonicalAmbientScalarResolutionMap φ σ τ ψ h J) n) ≫
        canonicalTildeHomologyCounitMap (canonicalAmbientTargetSheafComplex φ τ J) n =
      (((((ModuleCat.extendScalars ψ.hom).mapHomologicalComplex (.up ℤ)).obj
        (closedImmersionSourceResolutionComplex J σ)).sc n).mapHomologyIso
          (tilde.functor B')).inv ≫
        homologyMap (canonicalOpenTildeComplexIso ψ
          (closedImmersionSourceResolutionComplex J σ)).hom n ≫
        homologyMap (((restrictFunctor (Spec.map ψ)).mapHomologicalComplex (.up ℤ)).map
          (Complex.tildeGlobalSectionsCounit B (.up ℤ)
            (canonicalAmbientSourceSheafComplex σ J))) n ≫
        homologyMap (canonicalAmbientModelOpenIso φ σ τ ψ h J).hom n := by
  rw [tildeHomologyCounitMap_naturality,
    canonicalAmbientScalarResolutionMap_counit]
  simp only [homologyMap_comp]

/-- The actual open map on sheaf homology, with the original restriction
comparison in its source. -/
def canonicalAmbientSheafHomologyMap (n : ℤ) :
    ((canonicalAmbientSourceSheafComplex σ J).homology n).restrict (Spec.map ψ) ⟶
      (canonicalAmbientTargetSheafComplex φ τ J).homology n :=
  (((canonicalAmbientSourceSheafComplex σ J).sc n).mapHomologyIso
    (restrictFunctor (Spec.map ψ))).inv ≫
      homologyMap (canonicalAmbientModelOpenIso φ σ τ ψ h J).hom n

/-- The actual sheaf homology map is induced by the ordinary scalar adjoint
of the original module-homology map, under the same original counits. -/
theorem canonicalAmbientHomologyScalarMap_counit (n : ℤ) :
    (tilde.functor B').map (canonicalAmbientHomologyScalarMap φ σ τ ψ h J n) ≫
        canonicalTildeHomologyCounitMap (canonicalAmbientTargetSheafComplex φ τ J) n =
      (canonicalOpenTildeIso ψ).hom.app
          ((closedImmersionSourceResolutionComplex J σ).homology n) ≫
        (restrictFunctor (Spec.map ψ)).map
          (canonicalTildeHomologyCounitMap (canonicalAmbientSourceSheafComplex σ J) n) ≫
        canonicalAmbientSheafHomologyMap φ σ τ ψ h J n := by
  let F := ModuleCat.extendScalars ψ.hom
  let T := tilde.functor B'
  let T₀ := tilde.functor B
  let U := restrictFunctor (Spec.map ψ)
  let C := closedImmersionSourceResolutionComplex J σ
  let K := canonicalAmbientSourceSheafComplex σ J
  let K' := canonicalAmbientTargetSheafComplex φ τ J
  let D := canonicalAmbientScalarResolutionMap φ σ τ ψ h J
  let κ := Complex.tildeGlobalSectionsCounit B (.up ℤ) K
  let Φ := canonicalAmbientModelOpenIso φ σ τ ψ h J
  let B₀ := canonicalOpenTildeComplexIso ψ C
  let : PreservesFiniteLimits F :=
    ModuleCat.extendScalars_preservesFiniteLimits_of_flat ψ.hom
      (AlgebraicGeometry.Flat.SpecMap_iff.mp inferInstance)
  let e :
      (((U.mapHomologicalComplex (.up ℤ)).obj
        ((T₀.mapHomologicalComplex (.up ℤ)).obj C)).homology n) ≅
      U.obj (T₀.obj (C.homology n)) :=
    ((((T₀.mapHomologicalComplex (.up ℤ)).obj C).sc n).mapHomologyIso U) ≪≫
      U.mapIso ((C.sc n).mapHomologyIso T₀)
  let a : T.obj (F.obj (C.homology n)) ⟶
      ((T.mapHomologicalComplex (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj C)).homology n :=
    T.map ((C.sc n).mapHomologyIso F).inv ≫
      ((((F.mapHomologicalComplex (.up ℤ)).obj C).sc n).mapHomologyIso T).inv
  have hD := CategoryTheory.Adjunction.mapHomologicalComplex_homology_homEquiv_symm
    (ModuleCat.extendRestrictScalarsAdj ψ.hom) (.up ℤ)
    (canonicalAmbientResolutionMap φ σ τ ψ h J) n
  change ((C.sc n).mapHomologyIso F).inv ≫ homologyMap D n =
    canonicalAmbientHomologyScalarMap φ σ τ ψ h J n at hD
  have hB := HomologicalComplex.homologyMap_twoStage_exactIso F T T₀ U
    (canonicalOpenTildeIso ψ) (.up ℤ) C n
  have hB' : (a ≫ homologyMap B₀.hom n) ≫ e.hom =
      (canonicalOpenTildeIso ψ).hom.app (C.homology n) := by
    simpa only [a, e, B₀, canonicalOpenTildeComplexIso, Iso.trans_hom,
      Functor.mapIso_hom, Category.assoc] using hB
  have hb : a ≫ homologyMap B₀.hom n =
      (canonicalOpenTildeIso ψ).hom.app (C.homology n) ≫ e.inv := by
    have hc := congrArg (fun z => z ≫ e.inv) hB'
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hc
  have hκ := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor (Spec B).Modules (.up ℤ) n).map κ) U
  change U.map (homologyMap κ n) ≫ ((K.sc n).mapHomologyIso U).inv =
    ((((T₀.mapHomologicalComplex (.up ℤ)).obj C).sc n).mapHomologyIso U).inv ≫
      homologyMap ((U.mapHomologicalComplex (.up ℤ)).map κ) n at hκ
  have hc : e.inv ≫ homologyMap ((U.mapHomologicalComplex (.up ℤ)).map κ) n =
      U.map (canonicalTildeHomologyCounitMap K n) ≫ ((K.sc n).mapHomologyIso U).inv := by
    simp only [e, Iso.trans_inv, Functor.mapIso_inv, Category.assoc]
    rw [← hκ, ← CategoryTheory.Functor.map_comp_assoc]
    rfl
  calc
    _ = a ≫ homologyMap B₀.hom n ≫
        homologyMap ((U.mapHomologicalComplex (.up ℤ)).map κ) n ≫
        homologyMap Φ.hom n := by
      rw [← hD, CategoryTheory.Functor.map_comp, Category.assoc,
        canonicalAmbientScalarResolutionMap_homology_counit]
      simp only [a, T, F, B₀, U, κ, Φ, K, C, Category.assoc]
    _ = (canonicalOpenTildeIso ψ).hom.app (C.homology n) ≫ e.inv ≫
        homologyMap ((U.mapHomologicalComplex (.up ℤ)).map κ) n ≫
        homologyMap Φ.hom n := by
      simpa only [Category.assoc] using congrArg
        (fun z => z ≫ homologyMap ((U.mapHomologicalComplex (.up ℤ)).map κ) n ≫
          homologyMap Φ.hom n) hb
    _ = _ := by
      simpa only [canonicalAmbientSheafHomologyMap, Φ, K, U, Category.assoc] using
        congrArg (fun z => (canonicalOpenTildeIso ψ).hom.app (C.homology n) ≫ z ≫
          homologyMap Φ.hom n) hc

/-- Every original module-homology class has the same image under the
actual sheaf-model open map. The formula retains the original affine
counit maps and is valid on every open. -/
theorem canonicalAmbientSheafHomologyMap_counit_section (n : ℤ)
    (x : (closedImmersionSourceResolutionComplex J σ).homology n)
    (V : (Spec B').Opens) :
    (canonicalAmbientSheafHomologyMap φ σ τ ψ h J n).val.app (op V)
        ((canonicalTildeHomologyCounitMap (canonicalAmbientSourceSheafComplex σ J) n).val.app
          (op ((Spec.map ψ) ''ᵁ V))
          (tilde.toOpen ((closedImmersionSourceResolutionComplex J σ).homology n)
            ((Spec.map ψ) ''ᵁ V) x)) =
      (canonicalTildeHomologyCounitMap (canonicalAmbientTargetSheafComplex φ τ J) n).val.app
        (op V)
        (tilde.toOpen ((closedImmersionSourceResolutionComplex
          (affineOpenRestrictedInjectiveResolution φ J) τ).homology n) V
          (canonicalAmbientHomologyMap φ σ τ ψ h J n x)) := by
  let C := closedImmersionSourceResolutionComplex J σ
  let C' := closedImmersionSourceResolutionComplex (affineOpenRestrictedInjectiveResolution φ J) τ
  let v := tilde.toOpen ((ModuleCat.extendScalars ψ.hom).obj (C.homology n)) V
    ((1 : B') ⊗ₜ[B,ψ.hom] x)
  have ht := congrArg (fun z => z.val.app (op V) v)
    (canonicalAmbientHomologyScalarMap_counit φ σ τ ψ h J n)
  have hm := ConcreteCategory.congr_hom
    (tilde.toOpen_map_app (canonicalAmbientHomologyScalarMap φ σ τ ψ h J n) V)
    ((1 : B') ⊗ₜ[B,ψ.hom] x)
  change (((tilde.functor B').map (canonicalAmbientHomologyScalarMap φ σ τ ψ h J n)).val.app
      (op V)) v = tilde.toOpen (C'.homology n) V
        (canonicalAmbientHomologyScalarMap φ σ τ ψ h J n ((1 : B') ⊗ₜ[B,ψ.hom] x)) at hm
  rw [canonicalAmbientHomologyScalarMap_one_tmul] at hm
  have hv := canonicalOpenTildeIso_one_tmul ψ (C.homology n) x V
  change ((canonicalOpenTildeIso ψ).hom.app (C.homology n)).val.app (op V) v =
    tilde.toOpen (C.homology n) ((Spec.map ψ) ''ᵁ V) x at hv
  change (canonicalTildeHomologyCounitMap (canonicalAmbientTargetSheafComplex φ τ J) n).val.app
      (op V)
      ((((tilde.functor B').map (canonicalAmbientHomologyScalarMap φ σ τ ψ h J n)).val.app
        (op V)) v) =
    (canonicalAmbientSheafHomologyMap φ σ τ ψ h J n).val.app (op V)
      ((canonicalTildeHomologyCounitMap (canonicalAmbientSourceSheafComplex σ J) n).val.app
        (op ((Spec.map ψ) ''ᵁ V))
        (((canonicalOpenTildeIso ψ).hom.app (C.homology n)).val.app (op V) v)) at ht
  rw [hm, hv] at ht
  exact ht.symm

end Geometry
end AlgebraicGeometry.Scheme.Modules
