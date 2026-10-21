/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.FundamentalGroup.Field.OverRing
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.MarkedComparisonTransport

/-!
# The sheaf Ext class of the same normalization torsor

The existing normalization cover and action define a represented sheaf torsor
and its Ext-H¹ class. Actual Hopf-point marking derives finiteness and local
constancy of the coefficients. The positive annihilator and its invertibility
remain explicit. Comparison and Galois restriction retain the supplied Ext,
Stacks03AJ/03RV and Galois-category/fibre-functor conditions.
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
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (fiberToFinite)
open _root_.AlgebraicGeometry.Scheme.EtaleFundamentalGroups
open _root_.AlgebraicGeometry.Scheme.FiniteEtale.FiberTorsorActions
open _root_.GroupCohomology.ContinuousH1
open _root_.AlgebraicGeometry.Scheme.EtaleCohomology _root_.CategoryTheory.Abelian
open _root_.CategoryTheory.Functor.LargePresheaf
open AlgebraicGeometry.Scheme.FiniteEtale
open AlgebraicGeometry.Scheme.FiniteEtale.InertiaTorsor
open AlgebraicGeometry.Scheme.FiniteEtale.FieldGalois.OverRing Algebra.FiniteEtale.TorsorExtension
open integralClosure Algebra.FiniteEtale.TorsorCoordinates

namespace AlgebraicGeometry.Scheme.FiniteEtale.InertiaTorsor.SheafClass
universe u w

variable (R K Ω A H Lambda : Type u)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
  [IsGalois K Ω] [IsAlgClosed Ω]
  [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A] [Algebra.Etale K A]
  [CommRing H] [HopfAlgebra R H] [Coalgebra.IsCocomm R H]
  [Module.Finite R H] [Algebra.Etale R H]
  [AddCommGroup Lambda] [TopologicalSpace Lambda] [DiscreteTopology Lambda]
  [IsTopologicalAddGroup Lambda] [DistribMulAction (Ω ≃ₐ[K] Ω) Lambda]
  [ContinuousSMul (Ω ≃ₐ[K] Ω) Lambda]

local instance : Module.Finite K A := Algebra.FormallyUnramified.finite_of_free K A

variable (tau : OriginalTorsorData R K A H (Bialgebra.counitAlgHom R H) (Bialgebra.comulAlgHom R H))
  (coords : CoefficientPointCoordinates R K Ω H Lambda
    (Bialgebra.counitAlgHom R H) (Bialgebra.comulAlgHom R H))
  (f : A →ₐ[K] Ω)
  (Q : Ideal (integralClosure R Ω)) [Q.IsPrime] [Q.LiesOver (IsLocalRing.maximalIdeal R)]
  (hvan : inertiaClass R K Ω A H Lambda tau coords f Q = 0)

/-- Actual sections of the same cocommutative Hopf group scheme. Commutativity,
finiteness and étaleness come from the existing coefficientGroup instances. -/
abbrev normalizationCoefficientSheaf : AbelianSheaf.{u, u + 1} (Spec (.of R)) :=
  representedSheaf (coefficientGroup R H)

include coords in
/-- The given genuine coefficient marking derives finiteness of Lambda from
the finite fibre of the actual coefficient group scheme. -/
theorem coefficientModule_finite : Finite Lambda := by
  exact Finite.of_equiv
    ((fiberToFinite (basePoint R Ω)).obj (coefficientCover (coefficientGroup R H)))
    (coefficientSchemeMark R K Ω H Lambda coords).toAdditiveLeft.toEquiv

/-- The SAME normalization cover and its original action define a genuine
small-étale torsor. Its carrier is finiteRepresentedSetSheaf normalizationCover. -/
def normalizationSheafTorsor : Torsor (normalizationCoefficientSheaf R H) := by
  letI : Surjective (normalizationCover R K Ω A H Lambda tau coords f Q hvan).obj.hom :=
    normalizationCover_surjective R K Ω A H Lambda tau coords f Q hvan
  exact torsorOfSchemeAction (coefficientGroup R H)
    (normalizationCover R K Ω A H Lambda tau coords f Q hvan)
    (normalizationSchemeAction R K Ω A H Lambda tau coords f Q hvan)

section Ext
variable [HasExt.{w} (AbelianSheaf.{u, u + 1} (Spec (.of R)))]

/-- The genuine Ext¹ class of that actual represented sheaf torsor. -/
def normalizationExtClass : H1Etale (Spec (.of R)) (normalizationCoefficientSheaf R H) :=
  torsorExtClass (normalizationSheafTorsor R K Ω A H Lambda tau coords f Q hvan)

end Ext

section Comparison
variable [GaloisCategory (Scheme.FiniteEtale (Spec (.of R)))]
  [PreGaloisCategory.FiberFunctor (fiberToFinite (basePoint R Ω))]

include coords in
/-- Actual finite local constancy follows by the existing marked group-scheme
descent and its sheaf isomorphism, using the derived finite module. -/
theorem normalizationCoefficientSheaf_locallyConstant :
    IsFiniteLocallyConstant (normalizationCoefficientSheaf R H) := by
  let := coefficientModule_finite R K Ω H Lambda coords
  let := modelCoefficientAction R K Ω H Lambda coords
  let := modelCoefficientAction_continuous R K Ω H Lambda coords
  exact (isFiniteLocallyConstant_iff_of_iso
    (MarkedCoefficients.moduleSheafIso (basePoint R Ω) (coefficientGroup R H) Lambda
      (coefficientSchemeMark R K Ω H Lambda coords)
      (coefficientFullAction_mark (basePoint R Ω) (coefficientGroup R H) Lambda
        (coefficientSchemeMark R K Ω H Lambda coords)))).mp
    (moduleSheaf_isFiniteLocallyConstant (s := basePoint R Ω) Lambda)

include coords in
/-- An annihilator of the original marked module annihilates the actual
represented coefficient sheaf, by faithfulness of its finite geometric fibre. -/
theorem normalizationCoefficientSheaf_killedBy (n : ℕ) (hkill : ∀ a : Lambda, n • a = 0) :
    KilledBy n (normalizationCoefficientSheaf R H) := by
  apply representedSheaf_killedBy_of_identity_pow
  apply identity_pow_eq_one_of_fiber (basePoint R Ω)
  intro a
  apply (coefficientSchemeMark R K Ω H Lambda coords).injective
  rw [map_pow, map_one]
  exact congrArg Multiplicative.ofAdd (hkill ((coefficientSchemeMark R K Ω H Lambda coords
    a).toAdd))

/-- The coefficient record is derived from an explicit positive module
annihilator and its invertibility on the same Spec(R). Local constancy is proved. -/
def normalizationFiniteCoefficient (n : ℕ) (hpos : 0 < n)
    (hkill : ∀ a : Lambda, n • a = 0) (hunit : LevelInvertible (Spec (.of R)) n) :
    FiniteCoefficient (normalizationCoefficientSheaf R H) where
  level := n
  positive := hpos
  killed := normalizationCoefficientSheaf_killedBy R K Ω H Lambda coords n hkill
  invertible := hunit
  locally_constant := normalizationCoefficientSheaf_locallyConstant R K Ω H Lambda coords

variable [HasExt.{w} (AbelianSheaf.{u, u + 1} (Spec (.of R)))]
  (hA : Stacks03AJ.{u, w} (Spec (.of R))) (hR : Stacks03RV (Spec (.of R)))
  (n : ℕ) (hpos : 0 < n) (hkill : ∀ a : Lambda, n • a = 0)
  (hunit : LevelInvertible (Spec (.of R)) n)

/-- Source K2-018#prop:k2018-arithmetic-characters at revision
e73d98b1b5c1e5abcdebf7d058e436d792b87982: conditional local comparison subset.
The genuine Ext class maps to the existing native schemeTorsorClass of the
SAME normalization, coefficients and action. The additional comparison and
invertible-annihilator inputs are displayed, never the class equality itself. -/
theorem normalizationExtClass_comparison :
    letI := coefficientModule_finite R K Ω H Lambda coords
    letI := modelCoefficientAction R K Ω H Lambda coords
    letI := modelCoefficientAction_continuous R K Ω H Lambda coords
    FundamentalGroupComparison.representedH1AddEquiv (basePoint R Ω) (coefficientGroup R H)
      hA hR Lambda (coefficientSchemeMark R K Ω H Lambda coords)
      (coefficientFullAction_mark (basePoint R Ω) (coefficientGroup R H) Lambda
        (coefficientSchemeMark R K Ω H Lambda coords))
      (normalizationFiniteCoefficient R K Ω H Lambda coords n hpos hkill hunit)
      (normalizationExtClass R K Ω A H Lambda tau coords f Q hvan) =
    fullSchemeClass R K Ω A H Lambda tau coords f Q hvan := by
  let := coefficientModule_finite R K Ω H Lambda coords
  let := modelCoefficientAction R K Ω H Lambda coords
  let := modelCoefficientAction_continuous R K Ω H Lambda coords
  let : Surjective (normalizationCover R K Ω A H Lambda tau coords f Q hvan).obj.hom :=
    normalizationCover_surjective R K Ω A H Lambda tau coords f Q hvan
  unfold normalizationExtClass normalizationSheafTorsor
  rw [FundamentalGroupComparison.representedH1AddEquiv_torsor,
    SchemeTorsorClassification.representedTorsorClass_of_schemeAction]
  rfl

/-- Source K2-018#prop:k2018-arithmetic-characters at revision
e73d98b1b5c1e5abcdebf7d058e436d792b87982: the same local Ext-H¹ class, after
the actual comparison and literal identity-coefficient Galois restriction,
recovers genericClass of the ORIGINAL A-torsor. Global gluing is separate. -/
theorem normalizationExtClass_restriction_generic :
    letI := coefficientModule_finite R K Ω H Lambda coords
    letI := modelCoefficientAction R K Ω H Lambda coords
    letI := modelCoefficientAction_continuous R K Ω H Lambda coords
    (coefficientRestriction R K Ω H Lambda coords).onH1
      (FundamentalGroupComparison.representedH1AddEquiv (basePoint R Ω) (coefficientGroup R H)
        hA hR Lambda (coefficientSchemeMark R K Ω H Lambda coords)
        (coefficientFullAction_mark (basePoint R Ω) (coefficientGroup R H) Lambda
          (coefficientSchemeMark R K Ω H Lambda coords))
        (normalizationFiniteCoefficient R K Ω H Lambda coords n hpos hkill hunit)
        (normalizationExtClass R K Ω A H Lambda tau coords f Q hvan)) =
    genericClass R K Ω A H Lambda tau coords f := by
  let := coefficientModule_finite R K Ω H Lambda coords
  let := modelCoefficientAction R K Ω H Lambda coords
  let := modelCoefficientAction_continuous R K Ω H Lambda coords
  rw [normalizationExtClass_comparison,
    fullSchemeClass_restriction_generic]

end Comparison
end AlgebraicGeometry.Scheme.FiniteEtale.InertiaTorsor.SheafClass
