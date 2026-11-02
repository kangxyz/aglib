/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalModel.OpenCounit
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalModel.SourceIsomorphism

/-!
# The original source-isomorphism model and its affine counit

The ordinary closed-adjoint open comparison over the identity ambient chart
acts on the original coefficient resolution. Its homology map retains the
original affine counit and the original normalized source-sections map on
every open, without exactness of global sections on arbitrary sheaves.
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

section CounitPasting
variable {R S : CommRingCat.{u}} (ψ : R ⟶ S) [IsOpenImmersion (Spec.map ψ)]

private theorem openComplexHomologyCounit
    (K : CochainComplex (Spec R).Modules ℤ) (K' : CochainComplex (Spec S).Modules ℤ)
    (q : ((moduleSpecΓFunctor (R := R)).mapHomologicalComplex (.up ℤ)).obj K ⟶
      ((ModuleCat.restrictScalars ψ.hom).mapHomologicalComplex (.up ℤ)).obj
        (((moduleSpecΓFunctor (R := S)).mapHomologicalComplex (.up ℤ)).obj K'))
    (Φ : ((restrictFunctor (Spec.map ψ)).mapHomologicalComplex (.up ℤ)).obj K ⟶ K')
    (hq : ∀ n, q.f n = affineOpenRestrictionSectionsMap ψ (K.X n) ≫
      (ModuleCat.restrictScalars ψ.hom).map (moduleSpecΓFunctor.map (Φ.f n))) (n : ℤ) :
    let C := ((moduleSpecΓFunctor (R := R)).mapHomologicalComplex (.up ℤ)).obj K
    let C' := ((moduleSpecΓFunctor (R := S)).mapHomologicalComplex (.up ℤ)).obj K'
    let m := homologyMap q n ≫ ((C'.sc n).mapHomologyIso
      (ModuleCat.restrictScalars ψ.hom)).hom
    (tilde.functor S).map (((ModuleCat.extendRestrictScalarsAdj ψ.hom).homEquiv _ _).symm m) ≫
        canonicalTildeHomologyCounitMap K' n =
      (canonicalOpenTildeIso ψ).hom.app (C.homology n) ≫
        (restrictFunctor (Spec.map ψ)).map (canonicalTildeHomologyCounitMap K n) ≫
        ((K.sc n).mapHomologyIso (restrictFunctor (Spec.map ψ))).inv ≫ homologyMap Φ n := by
  intro C C' m
  let F := ModuleCat.extendScalars ψ.hom
  let T := tilde.functor S
  let T₀ := tilde.functor R
  let U := restrictFunctor (Spec.map ψ)
  let d := (((ModuleCat.extendRestrictScalarsAdj ψ.hom).mapHomologicalComplex (.up ℤ)).homEquiv
    C C').symm q
  let κ := Complex.tildeGlobalSectionsCounit R (.up ℤ) K
  let B₀ := canonicalOpenTildeComplexIso ψ C
  let : PreservesFiniteLimits F :=
    ModuleCat.extendScalars_preservesFiniteLimits_of_flat ψ.hom
      (AlgebraicGeometry.Flat.SpecMap_iff.mp inferInstance)
  have hd : ((T.mapHomologicalComplex (.up ℤ)).map d) ≫
      Complex.tildeGlobalSectionsCounit S (.up ℤ) K' =
    B₀.hom ≫ (U.mapHomologicalComplex (.up ℤ)).map κ ≫ Φ := by
    ext i : 1
    change (tilde.functor S).map
        (((ModuleCat.extendRestrictScalarsAdj ψ.hom).homEquiv _ _).symm (q.f i)) ≫
        (K'.X i).fromTildeΓ =
      (tildePullbackIso ψ).inv.app (moduleSpecΓFunctor.obj (K.X i)) ≫
        (restrictFunctorIsoPullback (Spec.map ψ)).inv.app
          (tilde (moduleSpecΓFunctor.obj (K.X i))) ≫
        U.map (K.X i).fromTildeΓ ≫ Φ.f i
    rw [hq]
    exact affineOpenRestrictionSectionsMap_counit ψ _ _ _
  have hD := CategoryTheory.Adjunction.mapHomologicalComplex_homology_homEquiv_symm
    (ModuleCat.extendRestrictScalarsAdj ψ.hom) (.up ℤ) q n
  change ((C.sc n).mapHomologyIso F).inv ≫ homologyMap d n =
    ((ModuleCat.extendRestrictScalarsAdj ψ.hom).homEquiv _ _).symm m at hD
  have hs := HomologicalComplex.homologyMap_twoStage_square F T T₀ U
    (canonicalOpenTildeIso ψ) (.up ℤ) C C' K K' d κ
    (Complex.tildeGlobalSectionsCounit S (.up ℤ) K') Φ hd n
  have hh := congrArg
    (fun z => T.map z ≫ canonicalTildeHomologyCounitMap K' n) hD
  apply hh.symm.trans
  simpa only [canonicalTildeHomologyCounitMap, HomologicalComplex.homologyCounitMap,
    F, T, T₀, U, κ, C, C', Category.assoc] using hs

private theorem openComplexHomologyCounit_section
    (K : CochainComplex (Spec R).Modules ℤ) (K' : CochainComplex (Spec S).Modules ℤ)
    (q : ((moduleSpecΓFunctor (R := R)).mapHomologicalComplex (.up ℤ)).obj K ⟶
      ((ModuleCat.restrictScalars ψ.hom).mapHomologicalComplex (.up ℤ)).obj
        (((moduleSpecΓFunctor (R := S)).mapHomologicalComplex (.up ℤ)).obj K'))
    (Φ : ((restrictFunctor (Spec.map ψ)).mapHomologicalComplex (.up ℤ)).obj K ⟶ K')
    (hq : ∀ n, q.f n = affineOpenRestrictionSectionsMap ψ (K.X n) ≫
      (ModuleCat.restrictScalars ψ.hom).map (moduleSpecΓFunctor.map (Φ.f n))) (n : ℤ)
    (x : (((moduleSpecΓFunctor (R := R)).mapHomologicalComplex (.up ℤ)).obj K).homology n)
    (V : (Spec S).Opens) :
    (((K.sc n).mapHomologyIso (restrictFunctor (Spec.map ψ))).inv ≫
        homologyMap Φ n).val.app (op V)
      ((canonicalTildeHomologyCounitMap K n).val.app (op ((Spec.map ψ) ''ᵁ V))
        (tilde.toOpen
          ((((moduleSpecΓFunctor (R := R)).mapHomologicalComplex (.up ℤ)).obj K).homology n)
          ((Spec.map ψ) ''ᵁ V) x)) =
      (canonicalTildeHomologyCounitMap K' n).val.app (op V)
        (tilde.toOpen
          ((((moduleSpecΓFunctor (R := S)).mapHomologicalComplex (.up ℤ)).obj K').homology n) V
          ((homologyMap q n ≫
            (((((moduleSpecΓFunctor (R := S)).mapHomologicalComplex
              (.up ℤ)).obj K').sc n).mapHomologyIso
              (ModuleCat.restrictScalars ψ.hom)).hom) x)) := by
  let M := ((moduleSpecΓFunctor (R := R)).mapHomologicalComplex (.up ℤ)).obj K
  let M' := ((moduleSpecΓFunctor (R := S)).mapHomologicalComplex (.up ℤ)).obj K'
  let m := homologyMap q n ≫ ((M'.sc n).mapHomologyIso
    (ModuleCat.restrictScalars ψ.hom)).hom
  let d := ((ModuleCat.extendRestrictScalarsAdj ψ.hom).homEquiv _ _).symm m
  let a := ((K.sc n).mapHomologyIso (restrictFunctor (Spec.map ψ))).inv ≫ homologyMap Φ n
  let v := tilde.toOpen ((ModuleCat.extendScalars ψ.hom).obj (M.homology n)) V
    ((1 : S) ⊗ₜ[R,ψ.hom] x)
  have ht := congrArg (fun z => z.val.app (op V) v)
    (openComplexHomologyCounit ψ K K' q Φ hq n)
  have hm := ConcreteCategory.congr_hom (tilde.toOpen_map_app d V)
    ((1 : S) ⊗ₜ[R,ψ.hom] x)
  change (((tilde.functor S).map d).val.app (op V)) v =
    tilde.toOpen (M'.homology n) V (d ((1 : S) ⊗ₜ[R,ψ.hom] x)) at hm
  have hmap := ((ModuleCat.extendRestrictScalarsAdj ψ.hom).homEquiv _ _).apply_symm_apply m
  have he := ModuleCat.extendRestrictScalarsAdj_homEquiv_apply d x
  have hdm : d ((1 : S) ⊗ₜ[R,ψ.hom] x) = m x :=
    he.symm.trans (ConcreteCategory.congr_hom hmap x)
  rw [hdm] at hm
  have hv := canonicalOpenTildeIso_one_tmul ψ (M.homology n) x V
  change ((canonicalOpenTildeIso ψ).hom.app (M.homology n)).val.app (op V) v =
    tilde.toOpen (M.homology n) ((Spec.map ψ) ''ᵁ V) x at hv
  change (canonicalTildeHomologyCounitMap K' n).val.app (op V)
      ((((tilde.functor S).map d).val.app (op V)) v) =
    a.val.app (op V)
      ((canonicalTildeHomologyCounitMap K n).val.app (op ((Spec.map ψ) ''ᵁ V))
        (((canonicalOpenTildeIso ψ).hom.app (M.homology n)).val.app (op V) v)) at ht
  rw [hm, hv] at ht
  exact ht.symm

end CounitPasting

section Source
variable {A B C : CommRingCat.{u}} (σ : A ⟶ B) (τ : A ⟶ C) (e : C ≃+* B)
  [IsClosedImmersion (Spec.map σ)] [IsClosedImmersion (Spec.map τ)]
  (h : IsPullback (Spec.map e.toCommRingCatIso.inv) (Spec.map τ)
    (Spec.map σ) (𝟙 (Spec A)))
  {L : (Spec A).Modules} (J : InjectiveResolution L)

/-- The actual ordinary closed-adjoint model on the supplied resolution. -/
abbrev canonicalSourceSheafComplex :=
  ((closedImmersionRightAdjoint (Spec.map σ)).mapHomologicalComplex (.up ℤ)).obj J.cochainComplex

/-- The original source open comparison followed by the original identity
restriction isomorphism, with no identity-restricted coefficient in the target. -/
@[no_expose] def canonicalSourceModelOpenIso :
    ((restrictFunctor (Spec.map e.toCommRingCatIso.inv)).mapHomologicalComplex (.up ℤ)).obj
        (canonicalSourceSheafComplex σ J) ≅ canonicalSourceSheafComplex τ J :=
  (Functor.mapHomologicalComplexCompIso
      (closedImmersionRightAdjointOpenIso (Spec.map e.toCommRingCatIso.inv)
        (Spec.map τ) (Spec.map σ) (𝟙 (Spec A)) h) (.up ℤ)).app J.cochainComplex ≪≫
    (NatIso.mapHomologicalComplex
      (Functor.isoWhiskerRight restrictFunctorId (closedImmersionRightAdjoint (Spec.map τ)) ≪≫
        Functor.leftUnitor (closedImmersionRightAdjoint (Spec.map τ)))
      (.up ℤ)).app J.cochainComplex

/-- Every term is the same original normalized ordinary source comparison. -/
theorem canonicalSourceModelOpenIso_hom_f (n : ℤ) :
    (canonicalSourceModelOpenIso σ τ e h J).hom.f n =
      (closedImmersionRightAdjointOpenIso (Spec.map e.toCommRingCatIso.inv)
        (Spec.map τ) (Spec.map σ) (𝟙 (Spec A)) h).hom.app (J.cochainComplex.X n) ≫
        (closedImmersionRightAdjoint (Spec.map τ)).map
          (restrictFunctorId.hom.app (J.cochainComplex.X n)) := by
  simp only [canonicalSourceModelOpenIso, Iso.trans_hom, HomologicalComplex.comp_f,
    NatIso.mapHomologicalComplex, NatTrans.mapHomologicalComplex,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app]
  rfl

/-- The frozen original sections-resolution map is induced by precisely this
sheaf-model isomorphism, including its original identity normalization. -/
theorem closedImmersionSourceResolutionMap_model_f (n : ℤ) :
    (closedImmersionSourceResolutionMap σ τ e h J).f n =
      affineOpenRestrictionSectionsMap e.toCommRingCatIso.inv
        ((canonicalSourceSheafComplex σ J).X n) ≫
      (ModuleCat.restrictScalars e.toCommRingCatIso.inv.hom).map
        (moduleSpecΓFunctor.map ((canonicalSourceModelOpenIso σ τ e h J).hom.f n)) := by
  rw [canonicalSourceModelOpenIso_hom_f]
  rfl

/-- The actual normalized source comparison on sheaf homology. -/
def canonicalSourceSheafHomologyMap (n : ℤ) :
    ((canonicalSourceSheafComplex σ J).homology n).restrict
        (Spec.map e.toCommRingCatIso.inv) ⟶ (canonicalSourceSheafComplex τ J).homology n :=
  (((canonicalSourceSheafComplex σ J).sc n).mapHomologyIso
    (restrictFunctor (Spec.map e.toCommRingCatIso.inv))).inv ≫
      homologyMap (canonicalSourceModelOpenIso σ τ e h J).hom n

/-- Every original module-homology class has the same image under the actual
source-isomorphism map on every open, through the original affine counits. -/
theorem canonicalSourceSheafHomologyMap_counit_section (n : ℤ)
    (x : (closedImmersionSourceResolutionComplex J σ).homology n)
    (V : (Spec C).Opens) :
    (canonicalSourceSheafHomologyMap σ τ e h J n).val.app (op V)
        ((canonicalTildeHomologyCounitMap (canonicalSourceSheafComplex σ J) n).val.app
          (op ((Spec.map e.toCommRingCatIso.inv) ''ᵁ V))
          (tilde.toOpen ((closedImmersionSourceResolutionComplex J σ).homology n)
            ((Spec.map e.toCommRingCatIso.inv) ''ᵁ V) x)) =
      (canonicalTildeHomologyCounitMap (canonicalSourceSheafComplex τ J) n).val.app
        (op V)
        (tilde.toOpen ((closedImmersionSourceResolutionComplex J τ).homology n) V
          (closedImmersionSourceHomologyMap σ τ e h J n x)) := by
  have hh := openComplexHomologyCounit_section (R := B) (S := C) e.toCommRingCatIso.inv
    (canonicalSourceSheafComplex σ J) (canonicalSourceSheafComplex τ J)
    (closedImmersionSourceResolutionMap σ τ e h J)
    (canonicalSourceModelOpenIso σ τ e h J).hom
    (closedImmersionSourceResolutionMap_model_f σ τ e h J) n x V
  unfold canonicalSourceSheafHomologyMap closedImmersionSourceHomologyMap
  dsimp only [closedImmersionSourceResolutionComplex, canonicalSourceSheafComplex] at hh ⊢
  exact hh

end Source
end AlgebraicGeometry.Scheme.Modules
