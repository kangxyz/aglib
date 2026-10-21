/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Normalization.InertiaTorsor.SheafClass
public import Aglib.AlgebraicGeometry.FundamentalGroup.Field.ArbitraryGalois
public import Aglib.AlgebraicGeometry.Cohomology.EtaleH1.Naturality
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.GenericRestriction

/-!
# Actual generic pullback and coefficient restriction

The literal h1Pullback of the same normalization Ext class is identified
through the represented-sheaf base-change map with the actual pulled-back
torsor class. The Galois factorization uses native GenericRestriction maps.
The final coefficient specialization reuses generic_represented_h1Pullback_injective;
its lower connectedness and fibre-surjectivity proofs are not duplicated.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj CategoryTheory.PreGaloisCategory FintypeCatDiscrete
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (Fiber baseChange fiberToFinite)
open _root_.AlgebraicGeometry.Scheme.EtaleFundamentalGroups
open _root_.AlgebraicGeometry.Scheme.FiniteEtale.FiberTorsorActions
open _root_.AlgebraicGeometry.Scheme.FiniteEtale.GroupBaseChange
open _root_.GroupCohomology.ContinuousH1
open _root_.AlgebraicGeometry.Scheme.EtaleH1 _root_.CategoryTheory.Abelian
open _root_.CategoryTheory.Functor.LargePresheaf
open AlgebraicGeometry.Scheme.FiniteEtale
open AlgebraicGeometry.Scheme.FiniteEtale.InertiaTorsor
open AlgebraicGeometry.Scheme.FiniteEtale.FieldGalois.OverRing Algebra.FiniteEtale.TorsorExtension
open integralClosure Algebra.FiniteEtale.TorsorCoordinates
open AlgebraicGeometry.Scheme.FiniteEtale.InertiaTorsor.SheafClass

open _root_.AlgebraicGeometry.Scheme.FiniteEtale.GenericRestriction
  (genericInclusion genericPoint_compat genericFibreMap)

namespace AlgebraicGeometry.Scheme.FiniteEtale.InertiaTorsor.GenericPullback
universe u v w w'

/-- Pointed base change preserves literal precomposition when its source and
base endomorphisms have the same underlying map of geometric-point schemes. -/
private theorem pointedMap_precomposition {F : Type u} [Field F]
    {S X : PointedScheme F} (fp : S ⟶ X)
    (a : FiberAutGroup S.hom) (b : FiberAutGroup X.hom)
    (eS : Over.mk S.hom ⟶ Over.mk S.hom)
    (eX : Over.mk X.hom ⟶ Over.mk X.hom)
    (he : eS.left = eX.left)
    (ha : ∀ (Y : Scheme.FiniteEtale S.right) (p : Fiber S.hom Y), a.hom.app Y p = eS ≫ p)
    (hb : ∀ (Y : Scheme.FiniteEtale X.right) (p : Fiber X.hom Y), b.hom.app Y p = eX ≫ p) :
    pointedMap fp a = b := by
  apply Aut.ext
  apply NatTrans.ext
  funext Y
  apply FintypeCat.hom_ext
  intro p
  rw [pointedMap_apply, ha, hb]
  apply Over.OverMorphism.ext
  simp only [pointedFiberEquiv_symm_left, Over.comp_left,
    pointedFiberEquiv_left, Category.assoc, pullback.lift_fst, he]

/-- Identity coefficients for a continuous group pullback between the supplied actions.
The equivariance equation is explicit, and the underlying coefficient function is `id`. -/
def identityCoefficientPullback {G J M : Type*}
    [Group G] [TopologicalSpace G] [Group J] [TopologicalSpace J]
    [AddCommGroup M] [TopologicalSpace M]
    [DistribMulAction G M] [DistribMulAction J M]
    (φ : J →ₜ* G) (hφ : ∀ (j : J) (a : M), φ j • a = j • a) :
    PullbackMap (A := M) (B := M) φ where
  toFun := id
  map_zero' := rfl
  map_add' _ _ := rfl
  continuous_toFun := continuous_id
  map_smul' := hφ

/-- Literal cohomology pullback followed by the canonical coefficient comparison.
The actual group homomorphism is retained with its equation to the pointed group map,
so the coefficient action uses that same map. Both Ext universes remain independent. -/
def pointedH1PullbackHom
    {X S : Scheme.{u}} {F : Type u} [Field F]
    (f : S ⟶ X) (s : Spec (.of F) ⟶ S) (x : Spec (.of F) ⟶ X) (hx : s ≫ f = x)
    (φ : FiberAutGroup s →ₜ* FiberAutGroup x)
    (hφ : φ = Naturality.pointedGroupHom f s x hx)
    (G : Grp (Over X)) [IsCommMonObj G.X] [IsFinite G.X.hom] [Etale G.X.hom]
    (M : Type v) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M] [Finite M]
    [DistribMulAction (FiberAutGroup x) M] [ContinuousSMul (FiberAutGroup x) M]
    [GaloisCategory (Scheme.FiniteEtale X)]
    [PreGaloisCategory.FiberFunctor (fiberToFinite x)]
    [GaloisCategory (Scheme.FiniteEtale S)]
    [PreGaloisCategory.FiberFunctor (fiberToFinite s)]
    [PreconnectedSpace X] [PreconnectedSpace S]
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)]
    (mark : (Over.mk x ⟶ G.X) ≃* Multiplicative M)
    (hmark : ∀ (γ : FiberAutGroup x) a,
      mark (γ.hom.app (coefficientCover G) a) = Multiplicative.ofAdd (γ • (mark a).toAdd))
    (hAS : Stacks03AJ.{u, w'} S) (hRS : Stacks03RV S)
    (hcoeff : FiniteCoefficient (representedSheaf G)) :
    letI := restrictedAction M φ
    letI := restrictedAction_continuous M φ
    H1Etale X (representedSheaf G) →+ H1 (FiberAutGroup s) M := by
  subst φ
  letI := restrictedAction M (Naturality.pointedGroupHom f s x hx)
  letI := restrictedAction_continuous M (Naturality.pointedGroupHom f s x hx)
  exact (Naturality.pointedInverseImageH1AddEquiv f s x hx G M mark hmark hAS hRS
    hcoeff).toAddMonoidHom.comp (h1Pullback f (representedSheaf G))

/-- The named homomorphism has exactly the original forward pullback/coefficient formula. -/
@[simp] theorem pointedH1PullbackHom_apply
    {X S : Scheme.{u}} {F : Type u} [Field F]
    (f : S ⟶ X) (s : Spec (.of F) ⟶ S) (x : Spec (.of F) ⟶ X) (hx : s ≫ f = x)
    (G : Grp (Over X)) [IsCommMonObj G.X] [IsFinite G.X.hom] [Etale G.X.hom]
    (M : Type v) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M] [Finite M]
    [DistribMulAction (FiberAutGroup x) M] [ContinuousSMul (FiberAutGroup x) M]
    [GaloisCategory (Scheme.FiniteEtale X)]
    [PreGaloisCategory.FiberFunctor (fiberToFinite x)]
    [GaloisCategory (Scheme.FiniteEtale S)]
    [PreGaloisCategory.FiberFunctor (fiberToFinite s)]
    [PreconnectedSpace X] [PreconnectedSpace S]
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)]
    (mark : (Over.mk x ⟶ G.X) ≃* Multiplicative M)
    (hmark : ∀ (γ : FiberAutGroup x) a,
      mark (γ.hom.app (coefficientCover G) a) = Multiplicative.ofAdd (γ • (mark a).toAdd))
    (hAS : Stacks03AJ.{u, w'} S) (hRS : Stacks03RV S)
    (hcoeff : FiniteCoefficient (representedSheaf G)) (a : H1Etale X (representedSheaf G)) :
    letI := restrictedAction M (Naturality.pointedGroupHom f s x hx)
    letI := restrictedAction_continuous M (Naturality.pointedGroupHom f s x hx)
    pointedH1PullbackHom f s x hx (Naturality.pointedGroupHom f s x hx) rfl
      G M mark hmark hAS hRS hcoeff a =
      Naturality.pointedInverseImageH1AddEquiv f s x hx G M mark hmark hAS hRS hcoeff
        (h1Pullback f (representedSheaf G) a) := rfl

/-- Injectivity of the actual pullback is retained through its coefficient equivalence. -/
theorem pointedH1PullbackHom_injective
    {X S : Scheme.{u}} {F : Type u} [Field F]
    (f : S ⟶ X) (s : Spec (.of F) ⟶ S) (x : Spec (.of F) ⟶ X) (hx : s ≫ f = x)
    (φ : FiberAutGroup s →ₜ* FiberAutGroup x)
    (hφ : φ = Naturality.pointedGroupHom f s x hx)
    (G : Grp (Over X)) [IsCommMonObj G.X] [IsFinite G.X.hom] [Etale G.X.hom]
    (M : Type v) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M] [Finite M]
    [DistribMulAction (FiberAutGroup x) M] [ContinuousSMul (FiberAutGroup x) M]
    [GaloisCategory (Scheme.FiniteEtale X)]
    [PreGaloisCategory.FiberFunctor (fiberToFinite x)]
    [GaloisCategory (Scheme.FiniteEtale S)]
    [PreGaloisCategory.FiberFunctor (fiberToFinite s)]
    [PreconnectedSpace X] [PreconnectedSpace S]
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)]
    (mark : (Over.mk x ⟶ G.X) ≃* Multiplicative M)
    (hmark : ∀ (γ : FiberAutGroup x) a,
      mark (γ.hom.app (coefficientCover G) a) = Multiplicative.ofAdd (γ • (mark a).toAdd))
    (hAS : Stacks03AJ.{u, w'} S) (hRS : Stacks03RV S)
    (hcoeff : FiniteCoefficient (representedSheaf G))
    (hinj : Function.Injective (h1Pullback f (representedSheaf G))) :
    letI := restrictedAction M φ
    letI := restrictedAction_continuous M φ
    Function.Injective (pointedH1PullbackHom f s x hx φ hφ G M mark hmark hAS hRS hcoeff) := by
  subst φ
  let := restrictedAction M (Naturality.pointedGroupHom f s x hx)
  let := restrictedAction_continuous M (Naturality.pointedGroupHom f s x hx)
  intro a b hab
  exact hinj ((Naturality.pointedInverseImageH1AddEquiv f s x hx G M mark hmark
    hAS hRS hcoeff).injective hab)

/-- Pointed naturality, with the same named forward map, before concrete spectra
or a normalization class are substituted. -/
private theorem pointedComparison_of_modelComparison
    {X S : Scheme.{u}} {F : Type u} [Field F]
    (f : S ⟶ X) (s : Spec (.of F) ⟶ S) (x : Spec (.of F) ⟶ X) (hx : s ≫ f = x)
    (φ : FiberAutGroup s →ₜ* FiberAutGroup x)
    (hφ : φ = Naturality.pointedGroupHom f s x hx)
    (G : Grp (Over X)) [IsCommMonObj G.X] [IsFinite G.X.hom] [Etale G.X.hom]
    (M : Type v) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M] [Finite M]
    [DistribMulAction (FiberAutGroup x) M] [ContinuousSMul (FiberAutGroup x) M]
    [GaloisCategory (Scheme.FiniteEtale X)]
    [PreGaloisCategory.FiberFunctor (fiberToFinite x)]
    [GaloisCategory (Scheme.FiniteEtale S)]
    [PreGaloisCategory.FiberFunctor (fiberToFinite s)]
    [PreconnectedSpace X] [PreconnectedSpace S]
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)]
    (mark : (Over.mk x ⟶ G.X) ≃* Multiplicative M)
    (hmark : ∀ (γ : FiberAutGroup x) a,
      mark (γ.hom.app (coefficientCover G) a) = Multiplicative.ofAdd (γ • (mark a).toAdd))
    (hAX : Stacks03AJ.{u, w} X) (hAS : Stacks03AJ.{u, w'} S)
    (hRX : Stacks03RV X) (hRS : Stacks03RV S)
    (hcoeff : FiniteCoefficient (representedSheaf G))
    (a : H1Etale X (representedSheaf G)) (b : H1 (FiberAutGroup x) M)
    (hab : FundamentalGroupComparison.representedH1AddEquiv x G hAX hRX M
      mark hmark hcoeff a = b) :
    letI := restrictedAction M φ
    letI := restrictedAction_continuous M φ
    pointedH1PullbackHom f s x hx φ hφ G M mark hmark hAS hRS hcoeff a =
      restriction M φ b := by
  subst φ
  let := restrictedAction M (Naturality.pointedGroupHom f s x hx)
  let := restrictedAction_continuous M (Naturality.pointedGroupHom f s x hx)
  exact (Naturality.pointedInverseImageH1AddEquiv_pullback f s x hx G M mark hmark
    hAX hAS hRX hRS hcoeff a).trans
      (congrArg (restriction M (Naturality.pointedGroupHom f s x hx)) hab)

/-- Carry three equalities through the specified coefficient map. -/
private theorem map_eq_of_three_equalities {S T : Type*}
    (f : S → T) (a b : S) (c d : T)
    (hab : a = b) (hbc : f b = c) (hcd : c = d) : f a = d :=
  (congrArg f hab).trans (hbc.trans hcd)

/-- Cocycles prove the compatibility of a genuine group restriction with
any two compatible coefficient pullbacks. -/
private theorem pullbackH1_after_restriction {G J L M N : Type*}
    [Group G] [TopologicalSpace G] [Group J] [TopologicalSpace J]
    [Group L] [TopologicalSpace L]
    [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
    [DistribMulAction G M] [ContinuousSMul G M]
    [DistribMulAction L N] [ContinuousSMul L N]
    (φ : J →ₜ* G) (ψ : L →ₜ* J) (χ : L →ₜ* G) (hcomp : φ.comp ψ = χ)
    (f : letI := restrictedAction M φ
      PullbackMap (A := M) (B := N) ψ)
    (g : PullbackMap (A := M) (B := N) χ)
    (hcoeff : ∀ m, f m = g m) :
    letI := restrictedAction M φ
    letI := restrictedAction_continuous M φ
    ∀ a : H1 G M, f.onH1 (restriction M φ a) = g.onH1 a := by
  let := restrictedAction M φ
  let := restrictedAction_continuous M φ
  intro a
  obtain ⟨c, rfl⟩ := classOf_surjective G M a
  rw [restriction_classOf, _root_.GroupCohomology.ContinuousH1.PullbackMap.onH1_classOf,
    _root_.GroupCohomology.ContinuousH1.PullbackMap.onH1_classOf]
  apply congrArg (classOf L N)
  apply _root_.GroupCohomology.ContinuousH1.Cocycle.ext
  intro l
  change f (c.val (φ (ψ l))) = g (c.val (χ l))
  rw [show φ (ψ l) = χ l from DFunLike.congr_fun hcomp l]
  exact hcoeff _

section GenericMap
variable (R K Ω : Type u) [CommRing R] [Field K] [Algebra R K]
  [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]


variable [Algebra.IsIntegral K Ω]

/-- Source K2-018#prop:k2018-arithmetic-characters, revision
e73d98b1b5c1e5abcdebf7d058e436d792b87982, local generic functoriality subset.
The literal Galois map factors through the ACTUAL generic pointed-scheme map,
using the same Omega and Spec precomposition at R=K. -/
theorem galoisToFibre_factorization :
    (genericFibreMap R K Ω).comp (galoisToFibre K K Ω) = galoisToFibre R K Ω := by
  apply ContinuousMonoidHom.ext
  intro sigma
  exact pointedMap_precomposition
    (Under.homMk (genericInclusion R K) (genericPoint_compat R K Ω) :
      Under.mk (basePoint K Ω) ⟶ Under.mk (basePoint R Ω))
    (galoisToFibre K K Ω sigma) (galoisToFibre R K Ω sigma)
    (pointEnd K K Ω sigma) (pointEnd R K Ω sigma) rfl
    (galoisToFibre_apply K K Ω sigma) (galoisToFibre_apply R K Ω sigma)

@[simp] theorem galoisToFibre_factorization_apply (sigma : Ω ≃ₐ[K] Ω) :
    genericFibreMap R K Ω (galoisToFibre K K Ω sigma) = galoisToFibre R K Ω sigma :=
  DFunLike.congr_fun (galoisToFibre_factorization R K Ω) sigma

end GenericMap

section Normalization
variable (R K Ω A H Lambda : Type u)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
  [IsGalois K Ω] [IsAlgClosed Ω]
  [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A] [Algebra.Etale K A]
  [CommRing H] [HopfAlgebra R H] [Coalgebra.IsCocomm R H]
  [Module.Finite R H] [Algebra.Etale R H]
  [AddCommGroup Lambda] [TopologicalSpace Lambda] [hLambdaDiscrete : DiscreteTopology Lambda]
  [IsTopologicalAddGroup Lambda] [DistribMulAction (Ω ≃ₐ[K] Ω) Lambda]
  [ContinuousSMul (Ω ≃ₐ[K] Ω) Lambda]

local instance : Module.Finite K A := Algebra.FormallyUnramified.finite_of_free K A

variable (tau : OriginalTorsorData R K A H (Bialgebra.counitAlgHom R H) (Bialgebra.comulAlgHom R H))
  (coords : CoefficientPointCoordinates R K Ω H Lambda
    (Bialgebra.counitAlgHom R H) (Bialgebra.comulAlgHom R H))
  (f : A →ₐ[K] Ω)
  (Q : Ideal (integralClosure R Ω)) [Q.IsPrime] [Q.LiesOver (IsLocalRing.maximalIdeal R)]
  (hvan : inertiaClass R K Ω A H Lambda tau coords f Q = 0)

/-- The generic full fibre group acts by actual generic pointed restriction
of the already constructed coefficient action over R. -/
abbrev genericCoefficientAction : DistribMulAction (FiberAutGroup (basePoint K Ω)) Lambda :=
  letI := modelCoefficientAction R K Ω H Lambda coords
  restrictedAction Lambda (genericFibreMap R K Ω)

theorem genericCoefficientAction_continuous :
    letI := genericCoefficientAction R K Ω H Lambda coords
    ContinuousSMul (FiberAutGroup (basePoint K Ω)) Lambda := by
  let := modelCoefficientAction R K Ω H Lambda coords
  let := modelCoefficientAction_continuous R K Ω H Lambda coords
  exact restrictedAction_continuous Lambda (genericFibreMap R K Ω)

include coords in
/-- Restriction of the generic action along the literal R=K Galois map is
the ORIGINAL Galois action, by the proved factorization. -/
theorem genericCoefficientAction_restrict (sigma : Ω ≃ₐ[K] Ω) (a : Lambda) :
    letI := genericCoefficientAction R K Ω H Lambda coords
    (galoisToFibre K K Ω sigma) • a = sigma • a := by
  let := modelCoefficientAction R K Ω H Lambda coords
  change (genericFibreMap R K Ω (galoisToFibre K K Ω sigma)) • a = sigma • a
  rw [galoisToFibre_factorization_apply]
  exact modelCoefficientAction_restrict R K Ω H Lambda coords sigma a

/-- Identity-coefficient Galois restriction of the ACTUAL generic fibre group,
with equivariance derived from generic functoriality and the original marking. -/
def genericCoefficientRestriction :
    letI := genericCoefficientAction R K Ω H Lambda coords
    PullbackMap (A := Lambda) (B := Lambda) (galoisToFibre K K Ω) := by
  letI := genericCoefficientAction R K Ω H Lambda coords
  exact identityCoefficientPullback (galoisToFibre K K Ω)
    (genericCoefficientAction_restrict R K Ω H Lambda coords)

/-- The two literal restriction routes agree on every native H¹ class; the
equality follows on cocycles from the actual generic Galois-map factorization. -/
theorem genericRestriction_onH1 :
    letI := modelCoefficientAction R K Ω H Lambda coords
    letI := modelCoefficientAction_continuous R K Ω H Lambda coords
    letI := genericCoefficientAction R K Ω H Lambda coords
    letI := genericCoefficientAction_continuous R K Ω H Lambda coords
    ∀ a : H1 (FiberAutGroup (basePoint R Ω)) Lambda,
      (genericCoefficientRestriction R K Ω H Lambda coords).onH1
        (restriction Lambda (genericFibreMap R K Ω) a) =
      (coefficientRestriction R K Ω H Lambda coords).onH1 a := by
  let := modelCoefficientAction R K Ω H Lambda coords
  let := modelCoefficientAction_continuous R K Ω H Lambda coords
  let := genericCoefficientAction R K Ω H Lambda coords
  let := genericCoefficientAction_continuous R K Ω H Lambda coords
  exact pullbackH1_after_restriction
    (genericFibreMap R K Ω) (galoisToFibre K K Ω) (galoisToFibre R K Ω)
    (galoisToFibre_factorization R K Ω)
    (genericCoefficientRestriction R K Ω H Lambda coords)
    (coefficientRestriction R K Ω H Lambda coords) (fun _ => rfl)

section Ext
variable [HasExt.{w} (AbelianSheaf.{u, u + 1} (Spec (.of R)))]
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} (Spec (.of K)))]

/-- The actual generic étale-cohomology class, after the canonical represented
coefficient isomorphism. This is the genuine h1Pullback of normalizationExtClass. -/
def genericExtClass :
    H1Etale (Spec (.of K))
      (representedSheaf (baseChangedGroup (genericInclusion R K) (coefficientGroup R H))) :=
  coefficientMap (representedSheafBaseChangeIso (genericInclusion R K) (coefficientGroup R H)).hom
    (h1Pullback (genericInclusion R K) (normalizationCoefficientSheaf R H)
      (normalizationExtClass R K Ω A H Lambda tau coords f Q hvan))

omit hLambdaDiscrete in
/-- The canonical coefficient comparison carries actual cohomological
pullback to the class of the ACTUAL pulled-back cover and scheme action.
This uses SchemeTorsorBaseChange.torsorExtClass_pullbackSchemeAction directly. -/
theorem genericExtClass_eq_torsor [_hLambdaDiscrete : DiscreteTopology Lambda] :
    genericExtClass R K Ω A H Lambda tau coords f Q hvan =
      (by
        letI : Surjective (normalizationCover R K Ω A H Lambda tau coords f Q hvan).obj.hom :=
          normalizationCover_surjective R K Ω A H Lambda tau coords f Q hvan
        exact torsorExtClass (torsorOfSchemeAction
          (baseChangedGroup (genericInclusion R K) (coefficientGroup R H))
          ((baseChange (genericInclusion R K)).obj (normalizationCover R K Ω A H Lambda tau coords f
            Q hvan))
          (SchemeTorsorBaseChange.pullbackSchemeAction (genericInclusion R K) (coefficientGroup R H)
            (normalizationCover R K Ω A H Lambda tau coords f Q hvan)
            (normalizationSchemeAction R K Ω A H Lambda tau coords f Q hvan)))) := by
  let : Surjective (normalizationCover R K Ω A H Lambda tau coords f Q hvan).obj.hom :=
    normalizationCover_surjective R K Ω A H Lambda tau coords f Q hvan
  unfold genericExtClass normalizationExtClass normalizationSheafTorsor
  exact SchemeTorsorBaseChange.torsorExtClass_pullbackSchemeAction
    (genericInclusion R K) (coefficientGroup R H)
    (normalizationCover R K Ω A H Lambda tau coords f Q hvan)
    (normalizationSchemeAction R K Ω A H Lambda tau coords f Q hvan)

section Comparison
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable [GaloisCategory (Scheme.FiniteEtale (Spec (.of R)))]
  [PreGaloisCategory.FiberFunctor (fiberToFinite (basePoint R Ω))]
  [GaloisCategory (Scheme.FiniteEtale (Spec (.of K)))]
  [PreGaloisCategory.FiberFunctor (fiberToFinite (basePoint K Ω))]
  (hAR : Stacks03AJ.{u, w} (Spec (.of R))) (hRR : Stacks03RV (Spec (.of R)))
  (hAK : Stacks03AJ.{u, w'} (Spec (.of K))) (hRK : Stacks03RV (Spec (.of K)))
  (n : ℕ) (hpos : 0 < n) (hkill : ∀ a : Lambda, n • a = 0)
  (hunit : LevelInvertible (Spec (.of R)) n)

/-- The actual generic pullback and canonical coefficient comparison, shared as a
single additive map. It is the same pointed map used by the general naturality theorem. -/
def genericH1PullbackComparison :
    letI := coefficientModule_finite R K Ω H Lambda coords
    letI := modelCoefficientAction R K Ω H Lambda coords
    letI := modelCoefficientAction_continuous R K Ω H Lambda coords
    letI := genericCoefficientAction R K Ω H Lambda coords
    letI := genericCoefficientAction_continuous R K Ω H Lambda coords
    H1Etale (Spec (.of R)) (normalizationCoefficientSheaf R H) →+
      H1 (FiberAutGroup (basePoint K Ω)) Lambda :=
  letI := coefficientModule_finite R K Ω H Lambda coords
  letI := modelCoefficientAction R K Ω H Lambda coords
  letI := modelCoefficientAction_continuous R K Ω H Lambda coords
  letI := genericCoefficientAction R K Ω H Lambda coords
  letI := genericCoefficientAction_continuous R K Ω H Lambda coords
  pointedH1PullbackHom (genericInclusion R K) (basePoint K Ω) (basePoint R Ω)
    (genericPoint_compat R K Ω) (genericFibreMap R K Ω) rfl
    (coefficientGroup R H) Lambda
    (coefficientSchemeMark R K Ω H Lambda coords)
    (coefficientFullAction_mark (basePoint R Ω) (coefficientGroup R H) Lambda
      (coefficientSchemeMark R K Ω H Lambda coords)) hAK hRK
    (normalizationFiniteCoefficient R K Ω H Lambda coords n hpos hkill hunit)

/-- The generic map is definitionally the actual pointed pullback homomorphism.
Together with `pointedH1PullbackHom_apply`, this identifies its literal old forward formula. -/
theorem genericH1PullbackComparison_eq_pointed :
    letI := coefficientModule_finite R K Ω H Lambda coords
    letI := modelCoefficientAction R K Ω H Lambda coords
    letI := modelCoefficientAction_continuous R K Ω H Lambda coords
    letI := genericCoefficientAction R K Ω H Lambda coords
    letI := genericCoefficientAction_continuous R K Ω H Lambda coords
    genericH1PullbackComparison R K Ω H Lambda coords hAK hRK n hpos hkill hunit =
      pointedH1PullbackHom (genericInclusion R K) (basePoint K Ω) (basePoint R Ω)
        (genericPoint_compat R K Ω) (genericFibreMap R K Ω) rfl
        (coefficientGroup R H) Lambda
        (coefficientSchemeMark R K Ω H Lambda coords)
        (coefficientFullAction_mark (basePoint R Ω) (coefficientGroup R H) Lambda
          (coefficientSchemeMark R K Ω H Lambda coords)) hAK hRK
        (normalizationFiniteCoefficient R K Ω H Lambda coords n hpos hkill hunit) := rfl

include hAR hRR in
/-- The same normalization Ext class compares under the actual generic pullback
map to restriction of the same full scheme-torsor class. The map's old literal formula
is `genericH1PullbackComparison_eq_pointed` followed by `pointedH1PullbackHom_apply`. -/
theorem normalizationExtClass_generic_comparison :
    letI := coefficientModule_finite R K Ω H Lambda coords
    letI := modelCoefficientAction R K Ω H Lambda coords
    letI := modelCoefficientAction_continuous R K Ω H Lambda coords
    letI := genericCoefficientAction R K Ω H Lambda coords
    letI := genericCoefficientAction_continuous R K Ω H Lambda coords
    genericH1PullbackComparison R K Ω H Lambda coords hAK hRK n hpos hkill hunit
      (normalizationExtClass R K Ω A H Lambda tau coords f Q hvan) =
      restriction Lambda (genericFibreMap R K Ω)
        (fullSchemeClass R K Ω A H Lambda tau coords f Q hvan) :=
  letI := coefficientModule_finite R K Ω H Lambda coords
  letI := modelCoefficientAction R K Ω H Lambda coords
  letI := modelCoefficientAction_continuous R K Ω H Lambda coords
  letI := genericCoefficientAction R K Ω H Lambda coords
  letI := genericCoefficientAction_continuous R K Ω H Lambda coords
  by
    exact pointedComparison_of_modelComparison
      (genericInclusion R K) (basePoint K Ω) (basePoint R Ω) (genericPoint_compat R K Ω)
      (genericFibreMap R K Ω) rfl (coefficientGroup R H) Lambda
      (coefficientSchemeMark R K Ω H Lambda coords)
      (coefficientFullAction_mark (basePoint R Ω) (coefficientGroup R H) Lambda
        (coefficientSchemeMark R K Ω H Lambda coords)) hAR hAK hRR hRK
      (normalizationFiniteCoefficient R K Ω H Lambda coords n hpos hkill hunit)
      (normalizationExtClass R K Ω A H Lambda tau coords f Q hvan)
      (fullSchemeClass R K Ω A H Lambda tau coords f Q hvan)
      (normalizationExtClass_comparison R K Ω A H Lambda tau coords f Q hvan
        hAR hRR n hpos hkill hunit)

include hAR hRR in
/-- Original identity-coefficient Galois restriction of the actual generic
pullback of the same normalization Ext class recovers the original algebraic torsor class. -/
theorem normalizationExtClass_generic_pullback :
    letI := coefficientModule_finite R K Ω H Lambda coords
    letI := modelCoefficientAction R K Ω H Lambda coords
    letI := modelCoefficientAction_continuous R K Ω H Lambda coords
    letI := genericCoefficientAction R K Ω H Lambda coords
    letI := genericCoefficientAction_continuous R K Ω H Lambda coords
    (genericCoefficientRestriction R K Ω H Lambda coords).onH1
      (genericH1PullbackComparison R K Ω H Lambda coords hAK hRK n hpos hkill hunit
        (normalizationExtClass R K Ω A H Lambda tau coords f Q hvan)) =
      genericClass R K Ω A H Lambda tau coords f :=
  letI := coefficientModule_finite R K Ω H Lambda coords
  letI := modelCoefficientAction R K Ω H Lambda coords
  letI := modelCoefficientAction_continuous R K Ω H Lambda coords
  letI := genericCoefficientAction R K Ω H Lambda coords
  letI := genericCoefficientAction_continuous R K Ω H Lambda coords
  by
    let restrictClass : H1 (FiberAutGroup (basePoint K Ω)) Lambda →
        H1 (Ω ≃ₐ[K] Ω) Lambda := (genericCoefficientRestriction R K Ω H Lambda coords).onH1
    exact map_eq_of_three_equalities restrictClass
      (genericH1PullbackComparison R K Ω H Lambda coords hAK hRK n hpos hkill hunit
        (normalizationExtClass R K Ω A H Lambda tau coords f Q hvan))
      (restriction Lambda (genericFibreMap R K Ω)
        (fullSchemeClass R K Ω A H Lambda tau coords f Q hvan))
      ((coefficientRestriction R K Ω H Lambda coords).onH1
        (fullSchemeClass R K Ω A H Lambda tau coords f Q hvan))
      (genericClass R K Ω A H Lambda tau coords f)
      (normalizationExtClass_generic_comparison R K Ω A H Lambda tau coords f Q hvan
        hAR hRR hAK hRK n hpos hkill hunit)
      (genericRestriction_onH1 R K Ω H Lambda coords
        (fullSchemeClass R K Ω A H Lambda tau coords f Q hvan))
      (fullSchemeClass_restriction_generic R K Ω A H Lambda tau coords f Q hvan)

end Comparison
end Ext
end Normalization

open _root_.AlgebraicGeometry.Scheme.FiniteEtale.GenericRestriction
  (generic_represented_h1Pullback_injective)

universe wR wK

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Generic pullback distinguishes actual model coefficient classes, retaining
both Ext universes and the supplied comparison families. -/
theorem normalizationCoefficient_generic_h1Pullback_injective (R K Ω H Lambda : Type u)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
    [IsGalois K Ω] [IsAlgClosed Ω]
    [CommRing H] [HopfAlgebra R H] [Coalgebra.IsCocomm R H]
    [Module.Finite R H] [Algebra.Etale R H]
    [AddCommGroup Lambda] [TopologicalSpace Lambda] [DiscreteTopology Lambda]
    [IsTopologicalAddGroup Lambda] [DistribMulAction (Ω ≃ₐ[K] Ω) Lambda]
    [ContinuousSMul (Ω ≃ₐ[K] Ω) Lambda]
    (coords : CoefficientPointCoordinates R K Ω H Lambda
      (Bialgebra.counitAlgHom R H) (Bialgebra.comulAlgHom R H))
    [GaloisCategory (Scheme.FiniteEtale (Spec (.of R)))]
    [PreGaloisCategory.FiberFunctor (fiberToFinite (basePoint R Ω))]
    [GaloisCategory (Scheme.FiniteEtale (Spec (.of K)))]
    [PreGaloisCategory.FiberFunctor (fiberToFinite (basePoint K Ω))]
    [HasExt.{wR} (AbelianSheaf.{u, u + 1} (Spec (.of R)))]
    [HasExt.{wK} (AbelianSheaf.{u, u + 1} (Spec (.of K)))]
    (hAR : Stacks03AJ.{u, wR} (Spec (.of R))) (hRR : Stacks03RV (Spec (.of R)))
    (hAK : Stacks03AJ.{u, wK} (Spec (.of K))) (hRK : Stacks03RV (Spec (.of K)))
    (n : ℕ) (hpos : 0 < n) (hkill : ∀ a : Lambda, n • a = 0)
    (hunit : LevelInvertible (Spec (.of R)) n) :
    Function.Injective
      (h1Pullback (genericInclusion R K) (normalizationCoefficientSheaf R H)) := by
  let := modelCoefficientAction R K Ω H Lambda coords
  let := modelCoefficientAction_continuous R K Ω H Lambda coords
  exact generic_represented_h1Pullback_injective R K Ω (coefficientGroup R H) Lambda
    (coefficientSchemeMark R K Ω H Lambda coords)
    (coefficientFullAction_mark (basePoint R Ω) (coefficientGroup R H) Lambda
      (coefficientSchemeMark R K Ω H Lambda coords)) hAR hRR hAK hRK
    (normalizationFiniteCoefficient R K Ω H Lambda coords n hpos hkill hunit)


/-- The actual generic comparison is injective under the original model/field
comparison families, because its literal pullback is injective and the coefficient map is an
additive equivalence. -/
theorem genericH1PullbackComparison_injective (R K Ω H Lambda : Type u)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
    [IsGalois K Ω] [IsAlgClosed Ω]
    [CommRing H] [HopfAlgebra R H] [Coalgebra.IsCocomm R H]
    [Module.Finite R H] [Algebra.Etale R H]
    [AddCommGroup Lambda] [TopologicalSpace Lambda] [DiscreteTopology Lambda]
    [IsTopologicalAddGroup Lambda] [DistribMulAction (Ω ≃ₐ[K] Ω) Lambda]
    [ContinuousSMul (Ω ≃ₐ[K] Ω) Lambda]
    (coords : CoefficientPointCoordinates R K Ω H Lambda
      (Bialgebra.counitAlgHom R H) (Bialgebra.comulAlgHom R H))
    [GaloisCategory (Scheme.FiniteEtale (Spec (.of R)))]
    [PreGaloisCategory.FiberFunctor (fiberToFinite (basePoint R Ω))]
    [GaloisCategory (Scheme.FiniteEtale (Spec (.of K)))]
    [PreGaloisCategory.FiberFunctor (fiberToFinite (basePoint K Ω))]
    [HasExt.{wR} (AbelianSheaf.{u, u + 1} (Spec (.of R)))]
    [HasExt.{wK} (AbelianSheaf.{u, u + 1} (Spec (.of K)))]
    (hAR : Stacks03AJ.{u, wR} (Spec (.of R))) (hRR : Stacks03RV (Spec (.of R)))
    (hAK : Stacks03AJ.{u, wK} (Spec (.of K))) (hRK : Stacks03RV (Spec (.of K)))
    (n : ℕ) (hpos : 0 < n) (hkill : ∀ a : Lambda, n • a = 0)
    (hunit : LevelInvertible (Spec (.of R)) n) :
    letI := coefficientModule_finite R K Ω H Lambda coords
    letI := modelCoefficientAction R K Ω H Lambda coords
    letI := modelCoefficientAction_continuous R K Ω H Lambda coords
    letI := genericCoefficientAction R K Ω H Lambda coords
    letI := genericCoefficientAction_continuous R K Ω H Lambda coords
    Function.Injective
      (genericH1PullbackComparison R K Ω H Lambda coords hAK hRK n hpos hkill hunit) :=
  letI := coefficientModule_finite R K Ω H Lambda coords
  letI := modelCoefficientAction R K Ω H Lambda coords
  letI := modelCoefficientAction_continuous R K Ω H Lambda coords
  letI := genericCoefficientAction R K Ω H Lambda coords
  letI := genericCoefficientAction_continuous R K Ω H Lambda coords
  by
    exact pointedH1PullbackHom_injective (genericInclusion R K)
      (basePoint K Ω) (basePoint R Ω) (genericPoint_compat R K Ω)
      (genericFibreMap R K Ω) rfl (coefficientGroup R H) Lambda
      (coefficientSchemeMark R K Ω H Lambda coords)
      (coefficientFullAction_mark (basePoint R Ω) (coefficientGroup R H) Lambda
        (coefficientSchemeMark R K Ω H Lambda coords)) hAK hRK
      (normalizationFiniteCoefficient R K Ω H Lambda coords n hpos hkill hunit)
      (normalizationCoefficient_generic_h1Pullback_injective R K Ω H Lambda coords
        hAR hRR hAK hRK n hpos hkill hunit)


/-- Source K2-018#prop:k2018-arithmetic-characters, revision
e73d98b1b5c1e5abcdebf7d058e436d792b87982, original-coefficient field matching.
The EXACT genericCoefficientRestriction used by normalizationExtClass_generic_pullback
is injective on arbitrary field fibre-group H1 classes, with the original
independently presented Galois action on Lambda and identity coefficients.
No external-class equality or restriction-injectivity dictionary is assumed. -/
theorem genericCoefficientRestriction_onH1_injective (R K Ω H Lambda : Type u)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
    [IsGalois K Ω] [IsAlgClosed Ω]
    [CommRing H] [HopfAlgebra R H] [Coalgebra.IsCocomm R H]
    [Module.Finite R H] [Algebra.Etale R H]
    [AddCommGroup Lambda] [TopologicalSpace Lambda] [DiscreteTopology Lambda]
    [IsTopologicalAddGroup Lambda] [DistribMulAction (Ω ≃ₐ[K] Ω) Lambda]
    [ContinuousSMul (Ω ≃ₐ[K] Ω) Lambda]
    (coords : CoefficientPointCoordinates R K Ω H Lambda
      (Bialgebra.counitAlgHom R H) (Bialgebra.comulAlgHom R H)) :
    letI := genericCoefficientAction R K Ω H Lambda coords
    letI := genericCoefficientAction_continuous R K Ω H Lambda coords
    Function.Injective (genericCoefficientRestriction R K Ω H Lambda coords).onH1 := by
  let := genericCoefficientAction R K Ω H Lambda coords
  let := genericCoefficientAction_continuous R K Ω H Lambda coords
  exact
    FieldGalois.Arbitrary.identityPullback_onH1_injective
    (galoisToFibre K K Ω)
    (FieldGalois.Arbitrary.galoisToFibre_surjective K Ω)
      (genericCoefficientRestriction R K Ω H Lambda coords)
    (fun _ => rfl)


end AlgebraicGeometry.Scheme.FiniteEtale.InertiaTorsor.GenericPullback
