/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.FieldCoordinates
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Differentials.Euler.PolynomialChart
public import Aglib.AlgebraicGeometry.FunctionField.Map
public import Aglib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.MvPolynomial.Localization
public import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Original projective ambient stalks at a generic image

A dominant structural map with finite original function-field extension
places the generic image at a maximal polynomial prime after the actual
base-field localization. The original chart factorization and original
open-immersion stalk map identify its ambient local ring with that
polynomial local ring. No normality or dimension hypothesis on the source
is required. In particular the result applies to an actual closed immersion.

The current consumer is chosen-embedding normal-surface concentration.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial

universe u

attribute [local instance] MvPolynomial.gradedAlgebra MvPolynomial.algebraMvPolynomial

namespace AlgebraicGeometry.ProjectiveSpace

/-- The native algebra structure is selected while its base is an abstract ring object. -/
@[instance_reducible]
def specFunctionFieldAlgebra (B : CommRingCat.{u}) [IsDomain B] :
    Algebra B (Spec B).functionField := inferInstance

/-- The original affine function field is a fraction ring for that same native algebra. -/
theorem specFunctionField_isFractionRing (B : CommRingCat.{u}) [IsDomain B] :
    letI := specFunctionFieldAlgebra B
    IsFractionRing B (Spec B).functionField := by
  let := specFunctionFieldAlgebra B
  exact functionField_isFractionRing_of_affine B

private theorem spec_genericMap (B : CommRingCat.{u}) [IsDomain B] :
    letI := specFunctionFieldAlgebra B
    (Spec B).fromSpecStalk (genericPoint (Spec B)) =
      Spec.map (CommRingCat.ofHom (algebraMap B (Spec B).functionField)) := by
  let := specFunctionFieldAlgebra B
  exact Spec.fromSpecStalk_eq' B _

private theorem localizationAtPrime_congr
    {B T : Type*} [CommSemiring B] [CommSemiring T] [Algebra B T]
    {p q : Ideal B} [p.IsPrime] [q.IsPrime] (h : p = q)
    (hp : IsLocalization.AtPrime T p) : IsLocalization.AtPrime T q := by
  subst q
  exact hp

variable (R : Type u) [CommRing R] [IsDomain R] (ι : Type u)
  {X : Scheme.{u}} [IsIntegral X] (i : X ⟶ ProjectiveSpace R ι)
  [IsDominant (i ≫ toSpec R ι)]

/-- The canonical `R`-algebra structure on the function field of `Spec R`. -/
local instance baseFunctionFieldAlgebra : Algebra R (Spec (.of R)).functionField :=
  specFunctionFieldAlgebra (CommRingCat.of R)

local instance baseFunctionField_isFractionRing :
    IsFractionRing R (Spec (.of R)).functionField :=
  specFunctionField_isFractionRing (CommRingCat.of R)

/-- The original finite-extension scalar map, before any projective chart is chosen. -/
def genericImageBaseMap : (Spec (.of R)).functionField →+* X.functionField :=
  Scheme.functionFieldMap (i ≫ toSpec R ι)

/-- The original base coefficients followed by the same dominant field map. -/
def genericImageCoefficients : R →+* X.functionField :=
  (genericImageBaseMap R ι i).comp (algebraMap R (Spec (.of R)).functionField)

/-- The actual generic inclusion retains its original structural coefficient triangle. -/
theorem genericImage_toSpec :
    (X.fromSpecStalk (genericPoint X) ≫ i) ≫ toSpec R ι =
      Spec.map (CommRingCat.ofHom (genericImageCoefficients R ι i)) := by
  rw [Category.assoc, Scheme.fromSpecStalk_genericPoint_naturality,
    spec_genericMap, ← Spec.map_comp]
  rfl

/-- Data chosen from the original generic morphism, containing no stalk comparison premise. -/
structure GenericStalkChart where
  /-- The coordinate chart containing the original generic image. -/
  index : ι
  /-- The original polynomial coordinate map into the source function field. -/
  polynomialMap : MvPolynomial {j : ι // j ≠ index} R →+* X.functionField
  coefficient : polynomialMap.comp C = genericImageCoefficients R ι i
  factorization : Spec.map (CommRingCat.ofHom polynomialMap) ≫
    eulerPolynomialChart R ι index = X.fromSpecStalk (genericPoint X) ≫ i

/-- The original field-valued generic morphism supplies the actual polynomial chart data. -/
theorem nonempty_genericStalkChart : Nonempty (GenericStalkChart R ι i) := by
  let : Algebra R X.functionField := (genericImageCoefficients R ι i).toAlgebra
  obtain ⟨k, φ, hφ, hfac⟩ := exists_coordinateChart_factorization_over
    (X.fromSpecStalk (genericPoint X) ≫ i) (genericImage_toSpec R ι i)
  let E := coordinateRingEquivPolynomial R ι k
  let ψ := φ.comp E.symm.toRingHom
  refine ⟨⟨k, ψ, ?_, ?_⟩⟩
  · apply RingHom.ext
    intro r
    change φ (polynomialToCoordinateRing R ι k (C r)) = genericImageCoefficients R ι i r
    rw [polynomialToCoordinateRing_C]
    exact RingHom.congr_fun hφ r
  · change Spec.map (CommRingCat.ofHom ψ) ≫
      (Spec.map (CommRingCat.ofHom E.toRingHom) ≫
        Proj.awayι (homogeneousSubmodule ι R) (MvPolynomial.X k)
          (isHomogeneous_X R k) Nat.zero_lt_one) = _
    rw [← Category.assoc, ← Spec.map_comp]
    have he : CommRingCat.ofHom E.toRingHom ≫ CommRingCat.ofHom ψ =
        CommRingCat.ofHom φ := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro a
      exact congrArg φ (E.symm_apply_apply a)
    rw [he]
    exact hfac

/-- A chart constructed from the original generic morphism and its original coefficient map. -/
def genericStalkChart : GenericStalkChart R ι i :=
  Classical.choice (nonempty_genericStalkChart R ι i)

namespace GenericStalkChart

variable {R ι i} (D : GenericStalkChart R ι i)

/-- The actual image of the unique point of the source function-field spectrum in the chart. -/
def point : Spec (.of (MvPolynomial {j : ι // j ≠ D.index} R)) :=
  Spec.map (CommRingCat.ofHom D.polynomialMap) ⟨⊥, inferInstance⟩

/-- The chart prime is the original evaluation kernel. -/
theorem point_asIdeal : D.point.asIdeal = RingHom.ker D.polynomialMap := rfl

instance point_isPrime : D.point.asIdeal.IsPrime := D.point.isPrime

/-- The actual open chart sends this point to the original generic image. -/
theorem point_image :
    eulerPolynomialChart R ι D.index D.point = i (genericPoint X) := by
  let z : Spec X.functionField := ⟨⊥, inferInstance⟩
  have h := congrArg (fun f : Spec X.functionField ⟶ ProjectiveSpace R ι => f z)
    D.factorization
  change eulerPolynomialChart R ι D.index D.point =
    i (X.fromSpecStalk (genericPoint X) z) at h
  exact h.trans (congrArg i (Scheme.fromSpecStalk_genericPoint_apply X z))

/-- The original open-immersion stalk map, followed by the original affine stalk comparison. -/
def ambientPolynomialStalkIso :
    (ProjectiveSpace R ι).presheaf.stalk (i (genericPoint X)) ≅
      CommRingCat.of (Localization.AtPrime D.point.asIdeal) :=
  TopCat.Presheaf.stalkCongr _ (.of_eq D.point_image.symm) ≪≫
    asIso ((eulerPolynomialChart R ι D.index).stalkMap D.point) ≪≫
      Spec.stalkIso (.of (MvPolynomial {j : ι // j ≠ D.index} R)) D.point

/-- The actual polynomial map into the original ambient stalk through its original chart. -/
def polynomialToAmbientStalk : MvPolynomial {j : ι // j ≠ D.index} R →+*
    (ProjectiveSpace R ι).presheaf.stalk (i (genericPoint X)) :=
  D.ambientPolynomialStalkIso.inv.hom.comp
    (algebraMap _ (Localization.AtPrime D.point.asIdeal))

/-- The original chart comparison fixes every polynomial numerator. -/
theorem ambientPolynomialStalkIso_polynomialToAmbientStalk
    (p : MvPolynomial {j : ι // j ≠ D.index} R) :
    D.ambientPolynomialStalkIso.hom (D.polynomialToAmbientStalk p) =
      algebraMap _ (Localization.AtPrime D.point.asIdeal) p := by
  exact ConcreteCategory.congr_hom D.ambientPolynomialStalkIso.inv_hom_id _

/-- Extend the original coordinate values along the original function-field embedding. -/
def fieldPolynomialMap :
    MvPolynomial {j : ι // j ≠ D.index} (Spec (.of R)).functionField →+* X.functionField :=
  MvPolynomial.eval₂Hom (genericImageBaseMap R ι i)
    (fun j => D.polynomialMap (MvPolynomial.X j))

/-- The extended map is the same original map on every polynomial over the base. -/
theorem fieldPolynomialMap_comp :
    D.fieldPolynomialMap.comp
        (MvPolynomial.map (algebraMap R (Spec (.of R)).functionField)) = D.polynomialMap := by
  apply MvPolynomial.ringHom_ext
  · intro r
    change (MvPolynomial.eval₂Hom (genericImageBaseMap R ι i)
      (fun j => D.polynomialMap (MvPolynomial.X j)))
        (MvPolynomial.map (algebraMap R (Spec (.of R)).functionField) (C r)) =
      D.polynomialMap (C r)
    rw [MvPolynomial.map_C, MvPolynomial.eval₂Hom_C]
    exact (RingHom.congr_fun D.coefficient r).symm
  · intro j
    change (MvPolynomial.eval₂Hom (genericImageBaseMap R ι i)
      (fun j => D.polynomialMap (MvPolynomial.X j)))
        (MvPolynomial.map (algebraMap R (Spec (.of R)).functionField) (MvPolynomial.X j)) =
      D.polynomialMap (MvPolynomial.X j)
    rw [MvPolynomial.map_X, MvPolynomial.eval₂Hom_X']

/-- The original generic polynomial prime. -/
def fieldPrime : Ideal (MvPolynomial {j : ι // j ≠ D.index} (Spec (.of R)).functionField) :=
  RingHom.ker D.fieldPolynomialMap

instance fieldPrime_isPrime : D.fieldPrime.IsPrime :=
  RingHom.ker_isPrime D.fieldPolynomialMap

/-- The original coefficient localization contracts the generic field prime to the actual point. -/
theorem fieldPrime_comap :
    D.fieldPrime.comap (algebraMap (MvPolynomial {j : ι // j ≠ D.index} R)
      (MvPolynomial {j : ι // j ≠ D.index} (Spec (.of R)).functionField)) = D.point.asIdeal := by
  rw [point_asIdeal, MvPolynomial.algebraMap_def]
  change (RingHom.ker D.fieldPolynomialMap).comap _ = _
  rw [RingHom.comap_ker, D.fieldPolynomialMap_comp]

/-- The finite original structural function-field extension makes this original prime maximal. -/
theorem fieldPrime_isMaximal (hfin : (genericImageBaseMap R ι i).Finite) :
    D.fieldPrime.IsMaximal := by
  let : Algebra (Spec (.of R)).functionField X.functionField :=
    (genericImageBaseMap R ι i).toAlgebra
  let : Module.Finite (Spec (.of R)).functionField X.functionField := hfin
  let φ : MvPolynomial {j : ι // j ≠ D.index} (Spec (.of R)).functionField →ₐ[
      (Spec (.of R)).functionField] X.functionField :=
    { D.fieldPolynomialMap with
      commutes' r := MvPolynomial.eval₂Hom_C _ _ r }
  let : (⊥ : Ideal X.functionField).IsMaximal := Ideal.bot_isMaximal
  simpa only [fieldPrime, RingHom.ker_eq_comap_bot] using
    Ideal.isMaximal_comap_of_finiteType_field (Spec (.of R)).functionField
      φ (⊥ : Ideal X.functionField)

/-- The second localization has its native polynomial algebra and scalar action. -/
@[instance_reducible]
def fieldLocalAlgebra : Algebra (MvPolynomial {j : ι // j ≠ D.index} R)
    (Localization.AtPrime D.fieldPrime) := inferInstance

attribute [local instance] fieldLocalAlgebra

local instance fieldLocal_scalarTower :
    IsScalarTower (MvPolynomial {j : ι // j ≠ D.index} R)
      (MvPolynomial {j : ι // j ≠ D.index} (Spec (.of R)).functionField)
      (Localization.AtPrime D.fieldPrime) := inferInstance

/-- The native localization algebra map is the original composite of the two polynomial maps. -/
theorem fieldLocalAlgebra_algebraMap :
    algebraMap (MvPolynomial {j : ι // j ≠ D.index} R) (Localization.AtPrime D.fieldPrime) =
      (algebraMap (MvPolynomial {j : ι // j ≠ D.index} (Spec (.of R)).functionField)
        (Localization.AtPrime D.fieldPrime)).comp
      (algebraMap (MvPolynomial {j : ι // j ≠ D.index} R)
        (MvPolynomial {j : ι // j ≠ D.index} (Spec (.of R)).functionField)) :=
  IsScalarTower.algebraMap_eq _ _ _

local instance fieldLocal_isLocalization :
    IsLocalization.AtPrime (Localization.AtPrime D.fieldPrime) D.point.asIdeal := by
  have h := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
    ((nonZeroDivisors R).map (MvPolynomial.C : R →+* MvPolynomial {j : ι // j ≠ D.index} R))
    (Localization.AtPrime D.fieldPrime) D.fieldPrime
  exact localizationAtPrime_congr D.fieldPrime_comap h

/-- The canonical localization comparison, with its original polynomial algebra map fixed. -/
def polynomialLocalizationEquiv :
    Localization.AtPrime D.point.asIdeal ≃ₐ[MvPolynomial {j : ι // j ≠ D.index} R]
      Localization.AtPrime D.fieldPrime :=
  IsLocalization.algEquiv D.point.asIdeal.primeCompl _ _

/-- The actual ambient stalk comparison uses the original open stalk map and localizations. -/
def ambientFieldStalkEquiv :
    (ProjectiveSpace R ι).presheaf.stalk (i (genericPoint X)) ≃+*
      Localization.AtPrime D.fieldPrime :=
  D.ambientPolynomialStalkIso.commRingCatIsoToRingEquiv.trans
    D.polynomialLocalizationEquiv.toRingEquiv

/-- Original polynomial numerators are preserved by the complete ambient local-ring comparison. -/
theorem ambientFieldStalkEquiv_polynomialToAmbientStalk
    (p : MvPolynomial {j : ι // j ≠ D.index} R) :
    D.ambientFieldStalkEquiv (D.polynomialToAmbientStalk p) =
      algebraMap _ (Localization.AtPrime D.fieldPrime) p := by
  change D.polynomialLocalizationEquiv
    (D.ambientPolynomialStalkIso.hom (D.polynomialToAmbientStalk p)) = _
  rw [D.ambientPolynomialStalkIso_polynomialToAmbientStalk]
  exact D.polynomialLocalizationEquiv.commutes p

/-- The original ambient local ring has the dimension of the generic polynomial chart. -/
theorem ambient_ringKrullDim [Finite ι]
    (hfin : (genericImageBaseMap R ι i).Finite) :
    ringKrullDim ((ProjectiveSpace R ι).presheaf.stalk (i (genericPoint X))) =
      Nat.card {j : ι // j ≠ D.index} := by
  let : D.fieldPrime.IsMaximal := D.fieldPrime_isMaximal hfin
  rw [ringKrullDim_eq_of_ringEquiv D.ambientFieldStalkEquiv]
  exact MvPolynomial.mvPolynomial_localizationAtPrime_dimension_of_isMaximal
    (Spec (.of R)).functionField {j : ι // j ≠ D.index} D.fieldPrime

end GenericStalkChart

/-- The actual image of the source generic point has ambient local dimension n.
The map need not be a closed immersion; a supplied closed immersion is included. -/
theorem genericImage_stalk_dimension
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    (hfin : (genericImageBaseMap R ι i).Finite) :
    ringKrullDim ((ProjectiveSpace R ι).presheaf.stalk (i (genericPoint X))) = n := by
  classical
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let D := genericStalkChart R ι i
  have he : {j : ι // j ≠ D.index} ≃ {k : Fin (n + 1) // k ≠ e D.index} :=
    { toFun := fun j => ⟨e j.val, fun h => j.property (e.injective h)⟩
      invFun := fun k => ⟨e.symm k.val, fun h => k.property
        ((e.apply_symm_apply k.val).symm.trans (congrArg e h))⟩
      left_inv := fun j => Subtype.ext (e.symm_apply_apply j.val)
      right_inv := fun k => Subtype.ext (e.apply_symm_apply k.val) }
  rw [D.ambient_ringKrullDim hfin, Nat.card_congr (he.trans (finSuccAboveEquiv (e D.index)).symm)]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin]

end AlgebraicGeometry.ProjectiveSpace
