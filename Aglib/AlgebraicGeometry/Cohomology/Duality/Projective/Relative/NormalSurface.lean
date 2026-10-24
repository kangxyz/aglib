/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.ClosedImmersion.RightAdjoint.FiniteSource.Derived
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.ClosedEmbedding
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Differentials.Determinant.Frames
public import Aglib.AlgebraicGeometry.ProjectiveSpace.GenericStalk
public import Aglib.AlgebraicGeometry.Modules.Flat.Relative.Unit
public import Aglib.AlgebraicGeometry.Properties.Normal.Basic
public import Aglib.AlgebraicGeometry.Properties.Regular.Basic
public import Aglib.AlgebraicGeometry.Stalk.Dimension
public import Aglib.Algebra.Homology.Koszul.Ext.Quotient
public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov.Layers
public import Aglib.RingTheory.RegularLocalRing.PrimeLocalization
public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import Mathlib.LinearAlgebra.Finsupp.Pi

/-!
# Chosen-embedding concentration on a normal integral surface

The coefficient is the original relative top differential coefficient at the
structure module, with its installed unit normalization. The derived object
is the original `derivedClosedImmersionRightAdjointPlus`, applied to that same
coefficient in degree zero.

For a closed immersion of a normal integral scheme of actual dimension at
most two into finite-dimensional projective space over a regular local
domain, dominance and finiteness of the original function-field map imply
concentration in the projective relative dimension. Coherence is proved
before concentration. The original generic stalk has a nonzero top Koszul
class, so closed support is the whole source. The normal-quotient Ext theorem
then forces the actual local codimension and vanishing in every other degree.

The argument allows inseparable function fields and projective dimension
zero. It applies in particular to the specified two-dimensional regular local
base. No regularity of the source, invertibility of its canonical module,
trace identity, Grauert--Riemenschneider vanishing, or resolution statement is
asserted.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules.Differentials
open AlgebraicGeometry.Scheme.Modules.FiniteSourceStalk
open scoped ModuleCat.Algebra

private def normalSurfaceExtIsoTransport {S : Type u} [CommRing S]
    {M M' N N' : ModuleCat.{u} S} (eM : M' ≅ M) (eN : N ≅ N') (q : ℕ) :
    Ext.{u} M N q ≃ₗ[S] Ext.{u} M' N' q where
  toFun x := ((Ext.mk₀ eM.hom).comp x (zero_add q)).comp (Ext.mk₀ eN.hom) (add_zero q)
  invFun x := ((Ext.mk₀ eM.inv).comp x (zero_add q)).comp (Ext.mk₀ eN.inv) (add_zero q)
  left_inv x := by
    simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
      Iso.hom_inv_id, Ext.comp_mk₀_id, Ext.mk₀_comp_mk₀_assoc,
      Iso.inv_hom_id, Ext.mk₀_id_comp]
  right_inv x := by
    simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
      Iso.inv_hom_id, Ext.comp_mk₀_id, Ext.mk₀_comp_mk₀_assoc,
      Iso.hom_inv_id, Ext.mk₀_id_comp]
  map_add' x y := by simp only [Ext.comp_add, Ext.add_comp]
  map_smul' a x := by
    simp only [Ext.comp_smul, Ext.smul_comp]
    rfl

/-- Top Ext of the actual surjective local map to a field is nonzero.
The source identification comes from the original quotient map and the
nonzero class comes from the original top Koszul quotient isomorphism. -/
private theorem normalSurface_nontrivial_topExt
    {S B : Type u} [CommRing S] [CommRing B] [IsRegularLocalRing S]
    (f : S →+* B) (hf : Function.Surjective f) (hB : IsField B)
    (d : ℕ) (hd : ringKrullDim S = (d : ℕ)) :
    letI := f.toAlgebra
    Nontrivial (Ext.{u} (ModuleCat.of S B) (ModuleCat.of S S) d) := by
  let := f.toAlgebra
  let := hB.toField
  obtain ⟨rs, hlen, hreg, hspan⟩ :=
    IsRegularLocalRing.exists_regular_sequence_maximalIdeal S d hd
  have hker : RingHom.ker f = IsLocalRing.maximalIdeal S :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective f hf)
  let q : (S ⧸ Ideal.ofList rs) ≃ₗ[S] B :=
    (Submodule.quotEquivOfEq _ _ (hspan.trans hker.symm)).trans
      (Ideal.quotientKerAlgEquivOfSurjective
        (f := Algebra.ofId S B) hf).toLinearEquiv
  let : Nontrivial (S ⧸ Ideal.ofList rs) :=
    Ideal.Quotient.nontrivial_iff.mpr
      (by rw [hspan]; exact (IsLocalRing.maximalIdeal.isMaximal S).ne_top)
  let : Nontrivial (Ext.{u} (ModuleCat.of S (S ⧸ Ideal.ofList rs))
      (ModuleCat.of S S) rs.length) :=
    (ChainComplex.Koszul.topExtRingQuotientLinearEquiv.{u, u}
      rs hreg.toIsWeaklyRegular).toEquiv.symm.nontrivial
  have h := (normalSurfaceExtIsoTransport q.symm.toModuleIso
    (Iso.refl (ModuleCat.of S S)) rs.length).toEquiv.symm.nontrivial
  simpa only [hlen] using h

private theorem normalSurface_dimension_nat_of_le_two
    (B : Type u) [CommRing B] [Nontrivial B] (hB : ringKrullDim B ≤ 2) :
    ∃ r : ℕ, ringKrullDim B = (r : ℕ) ∧ r ≤ 2 := by
  have h0 : 0 ≤ ringKrullDim B := ringKrullDim_nonneg_of_nontrivial
  lift ringKrullDim B to ℕ∞ using
    (ne_bot_of_le_ne_bot (by simp) h0) with d hd
  obtain ⟨r, hr, hr2⟩ := ENat.le_natCast_iff.mp (WithBot.coe_le_coe.mp hB)
  exact ⟨r, by rw [hr]; rfl, hr2⟩

@[expose] public section

namespace AlgebraicGeometry.Scheme.Cohomology

/-- The standard derived-category model for module sheaves on the given scheme. -/
local instance normalSurfaceHasDerivedCategoryModules (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules :=
  HasDerivedCategory.standard _

variable (R : Type u) [CommRing R] (ι : Type u)

/-- The original top differential coefficient with its original structure
coefficient, exactly as used by the relative closed-embedding Serre map. -/
abbrev normalSurfaceAmbientCoefficient (n : ℕ) : (ProjectiveSpace R ι).Modules :=
  (relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n).obj
    (SheafOfModules.unit (Spec (.of R)).ringCatSheaf)

/-- The actual Euler polynomial frame gives a frame of the original top
coefficient, preserving the original coefficient-unit normalization. -/
def normalSurfacePolynomialCoefficientIso (n : ℕ) (e : ι ≃ Fin (n + 1)) (k : ι) :
    (normalSurfaceAmbientCoefficient R ι n).restrict (eulerPolynomialChart R ι k) ≅
      SheafOfModules.unit (Spec (.of (MvPolynomial {j : ι // j ≠ k} R))).ringCatSheaf :=
  (Scheme.Modules.restrictFunctor (eulerPolynomialChart R ι k)).mapIso
      (relativeTopDifferentialCoefficientsUnitIso (toSpec R ι) n) ≪≫
    (moduleExteriorPowerRestrictionIso (eulerPolynomialChart R ι k)
      (relativeDifferentialSheaf (toSpec R ι)) n).symm ≪≫
    (moduleExteriorPowerFunctor (Spec (.of (MvPolynomial {j : ι // j ≠ k} R))) n).mapIso
      (eulerPolynomialOmegaFreeIso R ι k ≪≫
        (SheafOfModules.freeFunctor
          (R := (Spec (.of (MvPolynomial {j : ι // j ≠ k} R))).ringCatSheaf)).mapIso
            (determinantComplementEquiv ι n e k).toIso) ≪≫
    SheafOfModulesOfCommRing.exteriorTopFreeIso
      (Spec (.of (MvPolynomial {j : ι // j ≠ k} R))).sheaf n

/-- A genuine frame of the actual ambient coefficient at a polynomial-chart
stalk. The frame is used only for zero/nonzero detection. -/
def normalSurfacePolynomialCoefficientStalkIso (n : ℕ) (e : ι ≃ Fin (n + 1)) (k : ι)
    (y : Spec (.of (MvPolynomial {j : ι // j ≠ k} R))) :
    (moduleStalk _ y).obj
        ((normalSurfaceAmbientCoefficient R ι n).restrict (eulerPolynomialChart R ι k)) ≅
      ModuleCat.of ((Spec (.of (MvPolynomial {j : ι // j ≠ k} R))).presheaf.stalk y)
        ((Spec (.of (MvPolynomial {j : ι // j ≠ k} R))).presheaf.stalk y) := by
  let Y := Spec (.of (MvPolynomial {j : ι // j ≠ k} R))
  let S : CommRingCat.{u} := Y.presheaf.stalk y
  let e₁ : (ULift.{u} (PLift (y ∈ (⊤ : Y.Opens))) →₀ S) ≃ₗ[S] S :=
    Finsupp.uniqueLinearEquiv S S (ULift.up (PLift.up trivial))
  exact (moduleStalk _ y).mapIso (normalSurfacePolynomialCoefficientIso R ι n e k) ≪≫
    unitStalkIso _ y ≪≫ e₁.toModuleIso

/-- Finite presentation of the original ambient coefficient follows from the
actual Euler rank and native top exterior construction. -/
theorem normalSurfaceAmbientCoefficient_finitePresentation
    (n : ℕ) (e : ι ≃ Fin (n + 1)) :
    (normalSurfaceAmbientCoefficient R ι n).IsFinitePresentation := by
  have : IsFiniteLocallyFree (ProjectiveSpace R ι)
      (moduleExteriorPower (ProjectiveSpace R ι) (relativeDifferentialSheaf (toSpec R ι)) n) :=
    moduleExteriorTop_isFiniteLocallyFree _ _ n (projectiveDifferential_hasRank R ι n e)
  exact (SheafOfModules.isFinitePresentation (ProjectiveSpace R ι).ringCatSheaf).prop_of_iso
    (relativeTopDifferentialCoefficientsUnitIso (toSpec R ι) n).symm inferInstance

/-- The original chosen-embedding derived object. -/
abbrev normalSurfaceDualizingObject {X : Scheme.{u}} (i : X ⟶ ProjectiveSpace R ι)
    [IsClosedImmersion i] (n : ℕ) : DerivedCategory.Plus X.Modules :=
  (derivedClosedImmersionRightAdjointPlus i).obj
    ((DerivedCategory.Plus.singleFunctor (ProjectiveSpace R ι).Modules 0).obj
      (normalSurfaceAmbientCoefficient R ι n))

/-- The original top differential sheaf itself in the original derived
closed right adjoint, before choosing its coefficient-functor presentation. -/
abbrev normalSurfaceTopDifferentialObject {X : Scheme.{u}}
    (i : X ⟶ ProjectiveSpace R ι) [IsClosedImmersion i] (n : ℕ) :
    DerivedCategory.Plus X.Modules :=
  (derivedClosedImmersionRightAdjointPlus i).obj
    ((DerivedCategory.Plus.singleFunctor (ProjectiveSpace R ι).Modules 0).obj
      (moduleExteriorPower (ProjectiveSpace R ι) (relativeDifferentialSheaf (toSpec R ι)) n))

/-- The existing coefficient-unit normalization gives the explicit original
derived comparison. It is used whenever the consumer names raw `Ω^n` rather
than the coefficient functor at the structure module. -/
def normalSurfaceDualizingObjectUnitIso {X : Scheme.{u}}
    (i : X ⟶ ProjectiveSpace R ι) [IsClosedImmersion i] (n : ℕ) :
    normalSurfaceDualizingObject R ι i n ≅ normalSurfaceTopDifferentialObject R ι i n :=
  (derivedClosedImmersionRightAdjointPlus i).mapIso
    ((DerivedCategory.Plus.singleFunctor (ProjectiveSpace R ι).Modules 0).mapIso
      (relativeTopDifferentialCoefficientsUnitIso (toSpec R ι) n))

/-- Homology of the same original chosen-embedding object. -/
abbrev normalSurfaceHomology {X : Scheme.{u}} (i : X ⟶ ProjectiveSpace R ι)
    [IsClosedImmersion i] (n : ℕ) (q : ℤ) : X.Modules :=
  derivedClosedImmersionRightAdjointHomology i (normalSurfaceAmbientCoefficient R ι n) q

/-- The canonical module is the actual degree-`n` homology; no local freeness
is included in its definition. -/
abbrev normalSurfaceCanonicalModule {X : Scheme.{u}} (i : X ⟶ ProjectiveSpace R ι)
    [IsClosedImmersion i] (n : ℕ) : X.Modules := normalSurfaceHomology R ι i n (n : ℤ)

/-- Homology of the original derived object whose coefficient is raw `Ω^n`. -/
abbrev normalSurfaceTopDifferentialHomology {X : Scheme.{u}}
    (i : X ⟶ ProjectiveSpace R ι) [IsClosedImmersion i] (n : ℕ) (q : ℤ) : X.Modules :=
  (DerivedCategory.Plus.homologyFunctor X.Modules q).obj
    (normalSurfaceTopDifferentialObject R ι i n)

/-- The original coefficient-unit map induces the homology comparison. -/
def normalSurfaceTopDifferentialHomologyIso {X : Scheme.{u}}
    (i : X ⟶ ProjectiveSpace R ι) [IsClosedImmersion i] (n : ℕ) (q : ℤ) :
    normalSurfaceHomology R ι i n q ≅ normalSurfaceTopDifferentialHomology R ι i n q :=
  (DerivedCategory.Plus.homologyFunctor X.Modules q).mapIso
    (normalSurfaceDualizingObjectUnitIso R ι i n)

/-- Coherence of all the original homology sheaves is established before
any use of their support or concentration. -/
theorem normalSurfaceHomology_finitePresentation [IsNoetherianRing R]
    {X : Scheme.{u}} (i : X ⟶ ProjectiveSpace R ι) [IsClosedImmersion i]
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (q : ℤ) :
    (normalSurfaceHomology R ι i n q).IsFinitePresentation := by
  let : Finite ι := Finite.of_equiv _ e.symm
  have := normalSurfaceAmbientCoefficient_finitePresentation R ι n e
  exact derivedClosedImmersionRightAdjointHomology_finitePresentation i _ q

/-- Coherence for the same original object named with raw top differential
coefficient, transported only through the original coefficient-unit map. -/
theorem normalSurfaceTopDifferentialHomology_finitePresentation [IsNoetherianRing R]
    {X : Scheme.{u}} (i : X ⟶ ProjectiveSpace R ι) [IsClosedImmersion i]
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (q : ℤ) :
    (normalSurfaceTopDifferentialHomology R ι i n q).IsFinitePresentation :=
  (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso
    (normalSurfaceTopDifferentialHomologyIso R ι i n q)
    (normalSurfaceHomology_finitePresentation R ι i n e q)

/-- Every actual ambient point lies on an original polynomial chart. -/
theorem normalSurface_exists_polynomialPoint (p : ProjectiveSpace R ι) :
    ∃ k : ι, ∃ y : Spec (.of (MvPolynomial {j : ι // j ≠ k} R)),
      eulerPolynomialChart R ι k y = p := by
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (show p ∈ iSup (coordinateOpen R ι) by rw [iSup_coordinateOpen_eq_top]; trivial)
  let z : (coordinateOpen R ι k).toScheme := ⟨p, hk⟩
  refine ⟨k, (coordinateOpenIsoSpecPolynomial R ι k).hom z, ?_⟩
  exact (Scheme.Hom.comp_apply (coordinateOpenIsoSpecPolynomial R ι k).hom
    (eulerPolynomialChart R ι k) z).symm.trans
      (congrArg (fun f : (coordinateOpen R ι k).toScheme ⟶ ProjectiveSpace R ι => f z)
        (determinantCoordinateChart_comp R ι k))

/-- Regularity at the actual polynomial-chart stalk uses arbitrary finite
ambient dimension, without a regularity assumption on the source. -/
theorem normalSurface_polynomialStalk_regular [IsRegularLocalRing R] [Finite ι]
    (k : ι) (y : Spec (.of (MvPolynomial {j : ι // j ≠ k} R))) :
    IsRegularLocalRing ((Spec (.of (MvPolynomial {j : ι // j ≠ k} R))).presheaf.stalk y) := by
  let : IsRegularRing R := IsRegularLocalRing.isRegularRing_of_regularLocal R
  exact regularStalks_spec (MvPolynomial {j : ι // j ≠ k} R) y

section LocalVanishing

variable [IsRegularLocalRing R] {X : Scheme.{u}}
  (i : X ⟶ ProjectiveSpace R ι) [IsClosedImmersion i]
  (hX : NormalStalks X) (hXdim : topologicalKrullDim X ≤ 2)
  (n : ℕ) (e : ι ≃ Fin (n + 1))

include hX hXdim e

/-- At every original source point, the normal-quotient Ext calculation
vanishes outside the actual difference of local dimensions. The natural
dimensions, quotient chart, coefficient frame and stalk comparison are all
constructed from the supplied geometry. -/
theorem normalSurface_localVanishing (x : X) :
    ∃ d r : ℕ,
      ringKrullDim ((ProjectiveSpace R ι).presheaf.stalk (i x)) = (d : ℕ) ∧
      ringKrullDim (X.presheaf.stalk x) = (r : ℕ) ∧ r ≤ 2 ∧
      ∀ q : ℕ, q + r ≠ d →
        IsZero ((stalkFunctor X x).obj (normalSurfaceHomology R ι i n (q : ℤ))) := by
  let : Finite ι := Finite.of_equiv _ e.symm
  have := normalSurfaceAmbientCoefficient_finitePresentation R ι n e
  obtain ⟨k, y, hy⟩ := normalSurface_exists_polynomialPoint R ι (i x)
  let P : CommRingCat.{u} := .of (MvPolynomial {j : ι // j ≠ k} R)
  let j := eulerPolynomialChart R ι k
  let C := closedImmersionAffineQuotientChart i P j
  let : IsClosedImmersion (Spec.map (quotientMap C.ideal)) :=
    quotientClosedImmersion C.ideal
  obtain ⟨z, hz, hzy⟩ := C.exists_point x y hy.symm
  let y' : Spec P := imagePoint C.ideal z
  let S : CommRingCat.{u} := ambientRing C.ideal z
  let B : CommRingCat.{u} := sourceRing C.ideal z
  let eB := (asIso (C.sourceMap.stalkMap z)).commRingCatIsoToRingEquiv
  let eS := (asIso (j.stalkMap y')).commRingCatIsoToRingEquiv
  let : IsDomain (X.presheaf.stalk (C.sourceMap z)) := (hX _).1
  let : IsIntegrallyClosed (X.presheaf.stalk (C.sourceMap z)) := (hX _).2
  let : IsDomain B := eB.symm.toMulEquiv.isDomain _
  let : IsIntegrallyClosed B := IsIntegrallyClosed.of_equiv eB
  let : IsRegularLocalRing S := normalSurface_polynomialStalk_regular R ι k y'
  let d := Module.finrank (IsLocalRing.ResidueField S) (IsLocalRing.CotangentSpace S)
  have hd : ringKrullDim S = (d : ℕ) :=
    ((IsRegularLocalRing.iff_finrank_cotangentSpace S).mp inferInstance).symm
  have hBdim : ringKrullDim B ≤ 2 := by
    rw [← ringKrullDim_eq_of_ringEquiv eB]
    rw [Scheme.topologicalKrullDim_eq_iSup_stalk] at hXdim
    exact (le_iSup (fun z : X => ringKrullDim (X.presheaf.stalk z)) (C.sourceMap z)).trans hXdim
  obtain ⟨r, hr, hr2⟩ := normalSurface_dimension_nat_of_le_two B hBdim
  have hj : j y' = i x := (congrArg j hzy).trans hy
  have hdX : ringKrullDim ((ProjectiveSpace R ι).presheaf.stalk (i x)) = (d : ℕ) := by
    rw [← hj]
    exact (ringKrullDim_eq_of_ringEquiv eS).trans hd
  have hrX : ringKrullDim (X.presheaf.stalk x) = (r : ℕ) := by
    let ex : X.presheaf.stalk x ≅ X.presheaf.stalk (C.sourceMap z) :=
      TopCat.Presheaf.stalkCongr X.presheaf (.of_eq hz.symm)
    exact (ringKrullDim_eq_of_ringEquiv ex.commRingCatIsoToRingEquiv).trans
      ((ringKrullDim_eq_of_ringEquiv eB).trans hr)
  refine ⟨d, r, hdX, hrX, hr2, ?_⟩
  intro q hq
  let L := (normalSurfaceAmbientCoefficient R ι n).restrict j
  have : L.IsFinitePresentation := finitePresentation_restrict j _
  let J := injectiveResolution L
  let : Subsingleton ((moduleStalk (Spec (.of (P ⧸ C.ideal))) z).obj
      ((closedImmersionRightAdjointQuotientResolutionComplex C.ideal J).homology (q : ℤ))) :=
    closedImmersionQuotientHomologyStalk_subsingleton_of_coefficientFrame C.ideal z J
      (normalSurfacePolynomialCoefficientStalkIso R ι n e k y') d r hd hr hr2 q hq
  let E := (moduleStalk (Spec (.of (P ⧸ C.ideal))) z).mapIso
    (derivedClosedImmersionRightAdjointQuotientHomologyIso C.ideal J (q : ℤ))
  let : Subsingleton ((stalkFunctor (Spec (.of (P ⧸ C.ideal))) z).obj
      (derivedClosedImmersionRightAdjointHomology
        (Spec.map (quotientMap C.ideal)) L (q : ℤ))) :=
    E.toLinearEquiv.toEquiv.subsingleton
  have hzero := AddCommGrpCat.isZero_of_subsingleton
    ((stalkFunctor (Spec (.of (P ⧸ C.ideal))) z).obj
      (derivedClosedImmersionRightAdjointHomology
        (Spec.map (quotientMap C.ideal)) L (q : ℤ)))
  simpa only [hz] using hzero.of_iso
    (C.homologyStalkIso (normalSurfaceAmbientCoefficient R ι n) (q : ℤ) z)

end LocalVanishing

section Generic

variable [IsDomain R] [IsRegularLocalRing R] {X : Scheme.{u}} [IsIntegral X]
  (i : X ⟶ ProjectiveSpace R ι) [IsClosedImmersion i]
  [IsDominant (i ≫ toSpec R ι)]
  (n : ℕ) (e : ι ≃ Fin (n + 1))
  (hfin : (genericImageBaseMap R ι i).Finite)

include e hfin

/-- The actual generic degree-`n` stalk is nonzero, by transport of the
original top Koszul class. No separability assumption is used. -/
theorem normalSurface_generic_mem_support :
    genericPoint X ∈ support (normalSurfaceCanonicalModule R ι i n) := by
  let : Finite ι := Finite.of_equiv _ e.symm
  have := normalSurfaceAmbientCoefficient_finitePresentation R ι n e
  obtain ⟨k, y, hy⟩ := normalSurface_exists_polynomialPoint R ι (i (genericPoint X))
  let P : CommRingCat.{u} := .of (MvPolynomial {j : ι // j ≠ k} R)
  let j := eulerPolynomialChart R ι k
  let C := closedImmersionAffineQuotientChart i P j
  let : IsClosedImmersion (Spec.map (quotientMap C.ideal)) :=
    quotientClosedImmersion C.ideal
  obtain ⟨z, hz, hzy⟩ := C.exists_point (genericPoint X) y hy.symm
  let y' : Spec P := imagePoint C.ideal z
  let S : CommRingCat.{u} := ambientRing C.ideal z
  let B : CommRingCat.{u} := sourceRing C.ideal z
  let f : S ⟶ B := FiniteSourceStalk.stalkMap C.ideal z
  let eB := (asIso (C.sourceMap.stalkMap z)).commRingCatIsoToRingEquiv
  let eS := (asIso (j.stalkMap y')).commRingCatIsoToRingEquiv
  let eη : X.presheaf.stalk (C.sourceMap z) ≃+* X.functionField :=
    (TopCat.Presheaf.stalkCongr X.presheaf (.of_eq hz)).commRingCatIsoToRingEquiv
  have hfield : IsField (X.presheaf.stalk (C.sourceMap z)) :=
    MulEquiv.isField (Field.toIsField X.functionField) eη.toMulEquiv
  have hB : IsField B := MulEquiv.isField hfield eB.symm.toMulEquiv
  let : IsRegularLocalRing S := normalSurface_polynomialStalk_regular R ι k y'
  have hj : j y' = i (genericPoint X) := (congrArg j hzy).trans hy
  have hd : ringKrullDim S = (n : ℕ) := by
    rw [← ringKrullDim_eq_of_ringEquiv eS, hj]
    exact genericImage_stalk_dimension R ι i n e hfin
  let := f.hom.toAlgebra
  let L := (normalSurfaceAmbientCoefficient R ι n).restrict j
  have : L.IsFinitePresentation := finitePresentation_restrict j _
  let J := injectiveResolution L
  let eB' : ModuleCat.of S B ≅
      (ModuleCat.restrictScalars f.hom).obj (ModuleCat.of B B) :=
    (LinearEquiv.refl S B).toModuleIso
  let E := (derivedClosedImmersionRightAdjointQuotientStalkExtLinearEquiv C.ideal J z n).trans
    (normalSurfaceExtIsoTransport eB'
      (normalSurfacePolynomialCoefficientStalkIso R ι n e k y') n)
  let : Nontrivial (Ext.{u} (ModuleCat.of S B) (ModuleCat.of S S) n) :=
    normalSurface_nontrivial_topExt f.hom
      ((Spec.map (quotientMap C.ideal)).stalkMap_surjective z) hB n hd
  let : Nontrivial ((moduleStalk (Spec (.of (P ⧸ C.ideal))) z).obj
      (derivedClosedImmersionRightAdjointHomology
        (Spec.map (quotientMap C.ideal)) L (n : ℤ))) :=
    E.toEquiv.nontrivial
  intro hz0
  have hzero : IsZero ((stalkFunctor X (C.sourceMap z)).obj
      (normalSurfaceCanonicalModule R ι i n)) := by simpa only [hz] using hz0
  have hq0 := hzero.of_iso
    (C.homologyStalkIso (normalSurfaceAmbientCoefficient R ι n) (n : ℤ) z).symm
  let : Subsingleton ((moduleStalk (Spec (.of (P ⧸ C.ideal))) z).obj
      (derivedClosedImmersionRightAdjointHomology
        (Spec.map (quotientMap C.ideal)) L (n : ℤ))) :=
    AddCommGrpCat.subsingleton_of_isZero hq0
  obtain ⟨a, b, hab⟩ := exists_pair_ne
    (((moduleStalk (Spec (.of (P ⧸ C.ideal))) z).obj
      (derivedClosedImmersionRightAdjointHomology
        (Spec.map (quotientMap C.ideal)) L (n : ℤ))))
  exact hab (Subsingleton.elim a b)

/-- The coherent top homology has support all of the actual integral source.
Coherence and the generic nonzero class have both already been proved. -/
theorem normalSurfaceCanonicalModule_support :
    support (normalSurfaceCanonicalModule R ι i n) = Set.univ := by
  let : Finite ι := Finite.of_equiv _ e.symm
  have := normalSurfaceAmbientCoefficient_finitePresentation R ι n e
  have hc := derivedClosedImmersionRightAdjointHomology_isClosed_support
    i (normalSurfaceAmbientCoefficient R ι n) (n : ℤ)
  apply Set.eq_univ_of_univ_subset
  rw [← genericPoint_closure X]
  exact hc.closure_subset_iff.mpr
    (Set.singleton_subset_iff.mpr (normalSurface_generic_mem_support R ι i n e hfin))

/-- Full support for original `H^n(Ri!(Ω^n[0]))`, using the explicit original
coefficient-unit homology map. -/
theorem normalSurfaceTopDifferentialHomology_support :
    support (normalSurfaceTopDifferentialHomology R ι i n (n : ℤ)) = Set.univ := by
  rw [← support_eq_of_iso (normalSurfaceTopDifferentialHomologyIso R ι i n (n : ℤ))]
  exact normalSurfaceCanonicalModule_support R ι i n e hfin

end Generic

section Concentration

variable [IsDomain R] [IsRegularLocalRing R] {X : Scheme.{u}} [IsIntegral X]
  (i : X ⟶ ProjectiveSpace R ι) [IsClosedImmersion i]
  [IsDominant (i ≫ toSpec R ι)]
  (hX : NormalStalks X) (hXdim : topologicalKrullDim X ≤ 2)
  (n : ℕ) (e : ι ≃ Fin (n + 1))
  (hfin : (genericImageBaseMap R ι i).Finite)

include hX hXdim e hfin

/-- The constant codimension formula is a consequence of the nonzero top
stalk and the normal-quotient Ext calculation, at the original local rings. -/
theorem normalSurface_stalk_dimension (x : X) :
    ringKrullDim ((ProjectiveSpace R ι).presheaf.stalk (i x)) =
      (n : ℕ) + ringKrullDim (X.presheaf.stalk x) := by
  obtain ⟨d, r, hd, hr, _, hv⟩ := normalSurface_localVanishing R ι i hX hXdim n e x
  have hx : x ∈ support (normalSurfaceCanonicalModule R ι i n) := by
    rw [normalSurfaceCanonicalModule_support R ι i n e hfin]
    trivial
  have hnr : n + r = d := by
    by_contra hn
    exact hx (hv n hn)
  rw [hd, hr, ← hnr, Nat.cast_add]

/-- All homology sheaves of the original chosen-embedding object vanish
outside degree `n`. No concentration or local codimension premise is assumed. -/
theorem normalSurfaceHomology_isZero (q : ℤ) (hq : q ≠ (n : ℤ)) :
    IsZero (normalSurfaceHomology R ι i n q) := by
  by_cases hneg : q < 0
  · exact derivedClosedImmersionRightAdjointHomology_isZero_of_neg i _ q hneg
  obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt hneg)
  apply (isZero_iff_stalks _).mpr
  intro x
  obtain ⟨d, r, _, _, _, hv⟩ := normalSurface_localVanishing R ι i hX hXdim n e x
  have hx : x ∈ support (normalSurfaceCanonicalModule R ι i n) := by
    rw [normalSurfaceCanonicalModule_support R ι i n e hfin]
    trivial
  have hnr : n + r = d := by
    by_contra hn
    exact hx (hv n hn)
  apply hv j
  have hj : j ≠ n := by exact_mod_cast hq
  omega

/-- The lower homology bound of the same original derived object. -/
theorem normalSurfaceDualizingObject_isGE :
    (normalSurfaceDualizingObject R ι i n).IsGE (n : ℤ) := by
  rw [← DerivedCategory.Plus.isGE_ι_obj_iff, DerivedCategory.isGE_iff]
  intro q hq
  exact normalSurfaceHomology_isZero R ι i hX hXdim n e hfin q (ne_of_lt hq)

/-- The upper homology bound of the same original derived object. -/
theorem normalSurfaceDualizingObject_isLE :
    (normalSurfaceDualizingObject R ι i n).IsLE (n : ℤ) := by
  rw [← DerivedCategory.Plus.isLE_ι_obj_iff, DerivedCategory.isLE_iff]
  intro q hq
  exact normalSurfaceHomology_isZero R ι i hX hXdim n e hfin q (ne_of_gt hq)

/-- The actual original-homology-normalized single reconstruction of the
chosen-embedding object. The canonical module is coherent, with full support,
and is not asserted to be invertible. -/
def normalSurfaceCanonicalIso :
    normalSurfaceDualizingObject R ι i n ≅
      (DerivedCategory.Plus.singleFunctor X.Modules (n : ℤ)).obj
        (normalSurfaceCanonicalModule R ι i n) := by
  let := normalSurfaceDualizingObject_isGE R ι i hX hXdim n e hfin
  let := normalSurfaceDualizingObject_isLE R ι i hX hXdim n e hfin
  exact DerivedCategory.Plus.isoSingleHomology (normalSurfaceDualizingObject R ι i n) (n : ℤ)

/-- The single reconstruction induces the identity on the original degree-`n`
homology under the installed single/homology comparison. -/
theorem normalSurfaceCanonicalIso_homology :
    (DerivedCategory.Plus.homologyFunctor X.Modules (n : ℤ)).map
        (normalSurfaceCanonicalIso R ι i hX hXdim n e hfin).hom ≫
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso
        (C := X.Modules) (n : ℤ)).hom.app (normalSurfaceCanonicalModule R ι i n) = 𝟙 _ := by
  let := normalSurfaceDualizingObject_isGE R ι i hX hXdim n e hfin
  let := normalSurfaceDualizingObject_isLE R ι i hX hXdim n e hfin
  change (DerivedCategory.homologyFunctor X.Modules (n : ℤ)).map
    ((DerivedCategory.Plus.ι : _ ⥤ DerivedCategory X.Modules).map
      (DerivedCategory.Plus.isoSingleHomology
        (normalSurfaceDualizingObject R ι i n) (n : ℤ)).hom) ≫ _ = _
  rw [DerivedCategory.Plus.ι_map_isoSingleHomology_hom]
  exact DerivedCategory.isoSingleHomology_homology _ (n : ℤ)

/-- Concentration for the original derived object with raw `Ω^n` coefficient. -/
theorem normalSurfaceTopDifferentialHomology_isZero (q : ℤ) (hq : q ≠ (n : ℤ)) :
    IsZero (normalSurfaceTopDifferentialHomology R ι i n q) :=
  (normalSurfaceHomology_isZero R ι i hX hXdim n e hfin q hq).of_iso
    (normalSurfaceTopDifferentialHomologyIso R ι i n q).symm

theorem normalSurfaceTopDifferentialObject_isGE :
    (normalSurfaceTopDifferentialObject R ι i n).IsGE (n : ℤ) := by
  rw [← DerivedCategory.Plus.isGE_ι_obj_iff, DerivedCategory.isGE_iff]
  intro q hq
  exact normalSurfaceTopDifferentialHomology_isZero R ι i hX hXdim n e hfin q (ne_of_lt hq)

theorem normalSurfaceTopDifferentialObject_isLE :
    (normalSurfaceTopDifferentialObject R ι i n).IsLE (n : ℤ) := by
  rw [← DerivedCategory.Plus.isLE_ι_obj_iff, DerivedCategory.isLE_iff]
  intro q hq
  exact normalSurfaceTopDifferentialHomology_isZero R ι i hX hXdim n e hfin q (ne_of_gt hq)

/-- The native single-homology comparison for exactly the original
`Ri!(Ω^n[0])`, normalized by its own original `H^n`. -/
def normalSurfaceTopDifferentialCanonicalIso :
    normalSurfaceTopDifferentialObject R ι i n ≅
      (DerivedCategory.Plus.singleFunctor X.Modules (n : ℤ)).obj
        (normalSurfaceTopDifferentialHomology R ι i n (n : ℤ)) := by
  let := normalSurfaceTopDifferentialObject_isGE R ι i hX hXdim n e hfin
  let := normalSurfaceTopDifferentialObject_isLE R ι i hX hXdim n e hfin
  exact DerivedCategory.Plus.isoSingleHomology
    (normalSurfaceTopDifferentialObject R ι i n) (n : ℤ)

/-- The original raw-coefficient reconstruction induces the identity on its
own original degree-`n` homology under the installed normalization. -/
theorem normalSurfaceTopDifferentialCanonicalIso_homology :
    (DerivedCategory.Plus.homologyFunctor X.Modules (n : ℤ)).map
        (normalSurfaceTopDifferentialCanonicalIso R ι i hX hXdim n e hfin).hom ≫
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso
        (C := X.Modules) (n : ℤ)).hom.app
          (normalSurfaceTopDifferentialHomology R ι i n (n : ℤ)) = 𝟙 _ := by
  let := normalSurfaceTopDifferentialObject_isGE R ι i hX hXdim n e hfin
  let := normalSurfaceTopDifferentialObject_isLE R ι i hX hXdim n e hfin
  change (DerivedCategory.homologyFunctor X.Modules (n : ℤ)).map
    ((DerivedCategory.Plus.ι : _ ⥤ DerivedCategory X.Modules).map
      (DerivedCategory.Plus.isoSingleHomology
        (normalSurfaceTopDifferentialObject R ι i n) (n : ℤ)).hom) ≫ _ = _
  rw [DerivedCategory.Plus.ι_map_isoSingleHomology_hom]
  exact DerivedCategory.isoSingleHomology_homology _ (n : ℤ)

end Concentration

end AlgebraicGeometry.Scheme.Cohomology

end
