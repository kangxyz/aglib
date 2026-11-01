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

private theorem tildeHomologyCounit_naturality
    (C : CochainComplex (ModuleCat.{u} S) ℤ) (K : CochainComplex (Spec S).Modules ℤ)
    (q : C ⟶ ((moduleSpecΓFunctor (R := S)).mapHomologicalComplex (.up ℤ)).obj K) (n : ℤ) :
    (tilde.functor S).map (homologyMap q n) ≫ canonicalTildeHomologyCounitMap K n =
      ((C.sc n).mapHomologyIso (tilde.functor S)).inv ≫
        homologyMap (((tilde.functor S).mapHomologicalComplex (.up ℤ)).map q ≫
          Complex.tildeGlobalSectionsCounit S (.up ℤ) K) n := by
  have hn := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} S) (.up ℤ) n).map q)
    (tilde.functor S)
  change (tilde.functor S).map (homologyMap q n) ≫
      (((((moduleSpecΓFunctor (R := S)).mapHomologicalComplex (.up ℤ)).obj K).sc n).mapHomologyIso
        (tilde.functor S)).inv =
    ((C.sc n).mapHomologyIso (tilde.functor S)).inv ≫
      homologyMap (((tilde.functor S).mapHomologicalComplex (.up ℤ)).map q) n at hn
  simp only [canonicalTildeHomologyCounitMap, homologyMap_comp]
  rw [← Category.assoc, hn]
  exact Category.assoc _ _ _

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
  have hdH : T.map (homologyMap d n) ≫ canonicalTildeHomologyCounitMap K' n =
      ((((F.mapHomologicalComplex (.up ℤ)).obj C).sc n).mapHomologyIso T).inv ≫
        homologyMap B₀.hom n ≫ homologyMap ((U.mapHomologicalComplex (.up ℤ)).map κ) n ≫
        homologyMap Φ n := by
    rw [tildeHomologyCounit_naturality, hd]
    simp only [F, T, homologyMap_comp]
  let E : (((U.mapHomologicalComplex (.up ℤ)).obj
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
    (ModuleCat.extendRestrictScalarsAdj ψ.hom) (.up ℤ) q n
  change ((C.sc n).mapHomologyIso F).inv ≫ homologyMap d n =
    ((ModuleCat.extendRestrictScalarsAdj ψ.hom).homEquiv _ _).symm m at hD
  have hB := HomologicalComplex.homologyMap_twoStage_exactIso F T T₀ U
    (canonicalOpenTildeIso ψ) (.up ℤ) C n
  have hB' : (a ≫ homologyMap B₀.hom n) ≫ E.hom =
      (canonicalOpenTildeIso ψ).hom.app (C.homology n) := by
    simpa only [a, E, B₀, canonicalOpenTildeComplexIso, Iso.trans_hom,
      Functor.mapIso_hom, Category.assoc] using hB
  have hb : a ≫ homologyMap B₀.hom n =
      (canonicalOpenTildeIso ψ).hom.app (C.homology n) ≫ E.inv := by
    have hc := congrArg (fun z => z ≫ E.inv) hB'
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hc
  have hκ := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor (Spec R).Modules (.up ℤ) n).map κ) U
  change U.map (homologyMap κ n) ≫ ((K.sc n).mapHomologyIso U).inv =
    ((((T₀.mapHomologicalComplex (.up ℤ)).obj C).sc n).mapHomologyIso U).inv ≫
      homologyMap ((U.mapHomologicalComplex (.up ℤ)).map κ) n at hκ
  have hc : E.inv ≫ homologyMap ((U.mapHomologicalComplex (.up ℤ)).map κ) n =
      U.map (canonicalTildeHomologyCounitMap K n) ≫ ((K.sc n).mapHomologyIso U).inv := by
    simp only [E, Iso.trans_inv, Functor.mapIso_inv, Category.assoc]
    rw [← hκ, ← CategoryTheory.Functor.map_comp_assoc]
    rfl
  calc
    _ = a ≫ homologyMap B₀.hom n ≫
        homologyMap ((U.mapHomologicalComplex (.up ℤ)).map κ) n ≫ homologyMap Φ n := by
      rw [← hD, CategoryTheory.Functor.map_comp, Category.assoc, hdH]
      simp only [a, T, F, B₀, U, κ, C, Category.assoc]
    _ = (canonicalOpenTildeIso ψ).hom.app (C.homology n) ≫ E.inv ≫
        homologyMap ((U.mapHomologicalComplex (.up ℤ)).map κ) n ≫ homologyMap Φ n := by
      simpa only [Category.assoc] using congrArg
        (fun z => z ≫ homologyMap ((U.mapHomologicalComplex (.up ℤ)).map κ) n ≫
          homologyMap Φ n) hb
    _ = _ := by
      simpa only [Category.assoc] using congrArg
        (fun z => (canonicalOpenTildeIso ψ).hom.app (C.homology n) ≫ z ≫ homologyMap Φ n) hc

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
  have hh := openComplexHomologyCounit_section e.toCommRingCatIso.inv
    (canonicalSourceSheafComplex σ J) (canonicalSourceSheafComplex τ J)
    (closedImmersionSourceResolutionMap σ τ e h J)
    (canonicalSourceModelOpenIso σ τ e h J).hom
    (closedImmersionSourceResolutionMap_model_f σ τ e h J) n x V
  unfold canonicalSourceSheafHomologyMap closedImmersionSourceHomologyMap
  dsimp only [closedImmersionSourceResolutionComplex, canonicalSourceSheafComplex] at hh ⊢
  exact hh

end Source
end AlgebraicGeometry.Scheme.Modules
