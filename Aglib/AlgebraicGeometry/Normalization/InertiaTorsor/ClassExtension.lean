/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Normalization.InertiaTorsor.GenericPullback

/-!
# Uniqueness of the actual model class extending the same generic torsor

The model-to-Galois map is the literal generic cohomology pullback, canonical
coefficient comparison and identity-coefficient Galois restriction. Its actual
factors are injective under the displayed comparison conditions. The same
normalization Ext class is the unique preimage of the same generic torsor class.
Independent Ext universes and all level, descent and Stacks inputs remain explicit.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj CategoryTheory.PreGaloisCategory FintypeCatDiscrete
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (fiberToFinite)
open _root_.AlgebraicGeometry.Scheme.EtaleFundamentalGroups
open _root_.AlgebraicGeometry.Scheme.FiniteEtale.FiberTorsorActions
open _root_.GroupCohomology.ContinuousH1
open _root_.AlgebraicGeometry.Scheme.EtaleH1 _root_.CategoryTheory.Abelian
open _root_.CategoryTheory.Functor.LargePresheaf
open AlgebraicGeometry.Scheme.FiniteEtale
open _root_.AlgebraicGeometry.Scheme.FiniteEtale.GenericRestriction
  (genericInclusion genericPoint_compat genericFibreMap)
open AlgebraicGeometry.Scheme.FiniteEtale.InertiaTorsor Algebra.FiniteEtale.TorsorCoordinates
open AlgebraicGeometry.Scheme.FiniteEtale.FieldGalois.OverRing Algebra.FiniteEtale.TorsorExtension
open AlgebraicGeometry.Scheme.FiniteEtale.InertiaTorsor.SheafClass
open AlgebraicGeometry.Scheme.FiniteEtale.InertiaTorsor.GenericPullback
open AlgebraicGeometry.Scheme.FiniteEtale.FieldGalois.Arbitrary

namespace AlgebraicGeometry.Scheme.FiniteEtale.InertiaTorsor.ClassExtension

universe u wR wK

variable (R K Ω H Lambda : Type u)
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
  (hAK : Stacks03AJ.{u, wK} (Spec (.of K))) (hRK : Stacks03RV (Spec (.of K)))
  (n : ℕ) (hpos : 0 < n) (hkill : ∀ a : Lambda, n • a = 0)
  (hunit : LevelInvertible (Spec (.of R)) n)

/-- The canonical additive composite from actual model Ext-H1 to the ORIGINAL
native Galois H1, through literal generic h1Pullback and its actual coefficient
comparison. No final map or commuting square is provided as an input. -/
def modelToGaloisH1 :
    H1Etale (Spec (.of R)) (normalizationCoefficientSheaf R H) →+
      H1 (Ω ≃ₐ[K] Ω) Lambda := by
  letI := coefficientModule_finite R K Ω H Lambda coords
  letI := modelCoefficientAction R K Ω H Lambda coords
  letI := modelCoefficientAction_continuous R K Ω H Lambda coords
  letI := genericCoefficientAction R K Ω H Lambda coords
  letI := genericCoefficientAction_continuous R K Ω H Lambda coords
  exact (genericCoefficientRestriction R K Ω H Lambda coords).onH1.comp
    (genericH1PullbackComparison R K Ω H Lambda coords hAK hRK n hpos hkill hunit)

variable (hAR : Stacks03AJ.{u, wR} (Spec (.of R))) (hRR : Stacks03RV (Spec (.of R)))

include hAR hRR in
/-- Source K2-018#prop:k2018-arithmetic-characters, revision
e73d98b1b5c1e5abcdebf7d058e436d792b87982: conditional local arbitrary-class
injection. The three actual factors are injective. No A-torsor or inertia
premise is needed for injectivity on arbitrary model classes. -/
theorem modelToGaloisH1_injective :
    Function.Injective (modelToGaloisH1 R K Ω H Lambda coords hAK hRK n hpos hkill hunit) := by
  let := coefficientModule_finite R K Ω H Lambda coords
  let := modelCoefficientAction R K Ω H Lambda coords
  let := modelCoefficientAction_continuous R K Ω H Lambda coords
  let := genericCoefficientAction R K Ω H Lambda coords
  let := genericCoefficientAction_continuous R K Ω H Lambda coords
  intro a b hab
  apply genericH1PullbackComparison_injective R K Ω H Lambda coords
    hAR hRR hAK hRK n hpos hkill hunit
  apply genericCoefficientRestriction_onH1_injective R K Ω H Lambda coords
  exact hab

section OriginalTorsor
variable (A : Type u) [CommRing A] [Algebra K A] [Algebra R A]
  [IsScalarTower R K A] [Algebra.Etale K A]

local instance : Module.Finite K A := Algebra.FormallyUnramified.finite_of_free K A

variable (tau : OriginalTorsorData R K A H
    (Bialgebra.counitAlgHom R H) (Bialgebra.comulAlgHom R H))
  (f : A →ₐ[K] Ω)
  (Q : Ideal (integralClosure R Ω)) [Q.IsPrime] [Q.LiesOver (IsLocalRing.maximalIdeal R)]
  (hvan : inertiaClass R K Ω A H Lambda tau coords f Q = 0)

include hAR hRR in
/-- Source K2-018#prop:k2018-arithmetic-characters, revision
e73d98b1b5c1e5abcdebf7d058e436d792b87982: the SAME constructed normalization
Ext class maps to genericClass of the ORIGINAL algebraic A-torsor. This is the
accepted literal generic-pullback compatibility, applied to the constructed map. -/
theorem normalizationExtClass_image :
    modelToGaloisH1 R K Ω H Lambda coords hAK hRK n hpos hkill hunit
      (normalizationExtClass R K Ω A H Lambda tau coords f Q hvan) =
    genericClass R K Ω A H Lambda tau coords f := by
  exact normalizationExtClass_generic_pullback R K Ω A H Lambda tau coords f Q hvan
    hAR hRR hAK hRK n hpos hkill hunit

include hAR hRR in
/-- Source K2-018#prop:k2018-arithmetic-characters, revision
e73d98b1b5c1e5abcdebf7d058e436d792b87982: any model class with this ORIGINAL
generic torsor class equals the same constructed normalization Ext class. -/
theorem eq_normalizationExtClass_of_image
    (a : H1Etale (Spec (.of R)) (normalizationCoefficientSheaf R H))
    (ha : modelToGaloisH1 R K Ω H Lambda coords hAK hRK n hpos hkill hunit a =
      genericClass R K Ω A H Lambda tau coords f) :
    a = normalizationExtClass R K Ω A H Lambda tau coords f Q hvan := by
  apply modelToGaloisH1_injective R K Ω H Lambda coords hAK hRK n hpos hkill hunit hAR hRR
  exact ha.trans (normalizationExtClass_image R K Ω H Lambda coords hAK hRK
    n hpos hkill hunit hAR hRR A tau f Q hvan).symm

include hAR hRR hvan in
/-- Source K2-018#prop:k2018-arithmetic-characters, revision
e73d98b1b5c1e5abcdebf7d058e436d792b87982: conditional local existence and
uniqueness for the SAME original A-torsor. Existence uses tau/f/Q and vanishing
inertia; uniqueness uses injection on arbitrary model classes. No global gluing
or realization of an arbitrary Galois H1 class is asserted. -/
theorem existsUnique_modelClass :
    ∃! a : H1Etale (Spec (.of R)) (normalizationCoefficientSheaf R H),
      modelToGaloisH1 R K Ω H Lambda coords hAK hRK n hpos hkill hunit a =
        genericClass R K Ω A H Lambda tau coords f := by
  refine ⟨normalizationExtClass R K Ω A H Lambda tau coords f Q hvan,
    normalizationExtClass_image R K Ω H Lambda coords hAK hRK n hpos hkill hunit
      hAR hRR A tau f Q hvan, ?_⟩
  intro a ha
  exact eq_normalizationExtClass_of_image R K Ω H Lambda coords hAK hRK n hpos hkill hunit
    hAR hRR A tau f Q hvan a ha

end OriginalTorsor
end AlgebraicGeometry.Scheme.FiniteEtale.InertiaTorsor.ClassExtension
