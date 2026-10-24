/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.RationalSingularities.Blowup.Normality
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.GlobalSections
public import Aglib.AlgebraicGeometry.Modules.ClosedImmersion.StructureQuotient

/-!
# The full exceptional fibre and its original residue-field coefficients

The original maximal-ideal centre defines the full exceptional scheme E.
Its native closed-immersion lift to Spec(A/m) retains the original blowdown
triangle and is the actual Cartesian closed fibre. Properness and
surjectivity follow by base change of the original ordinary blowdown.

The actual positive ideal-power normalization maps are isomorphisms, using
the proved ordinary normalization theorem and its original projection/unit
square. Their H1 vanishing transports the normalized ideal-power vanishing.
The original ideal short exact sequence then makes restriction of global
functions onto E surjective. Consequently the original structural map
A/m → Γ(E,O_E) is bijective, with its original quotient values retained.

These statements include regular rational local surfaces. No Gorenstein,
Hilbert-function, degree or closed-stalk Cohen–Macaulay conclusion is made.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open AlgebraicGeometry.Scheme.Modules.Invertible AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Blowup

universe u

namespace AlgebraicGeometry.Scheme.RationalSingularities.MaximalIdealBlowup

section CategoryBoundary

variable {C : Type*} [Category* C]

private theorem isIso_of_original_square {U V W Z : C}
    (x : U ⟶ V) (e : V ≅ W) (r : U ≅ Z) (f : Z ⟶ W)
    (hx : IsIso x) (h : x ≫ e.hom = r.hom ≫ f) : IsIso f := by
  let := hx
  have hp : IsIso (x ≫ e.hom) := inferInstance
  have hq : IsIso (r.hom ≫ f) := (congrArg IsIso h).mp hp
  exact (isIso_comp_left_iff _ _).mp hq

end CategoryBoundary

private theorem original_subscheme_closed {X : Scheme.{u}} (I : X.IdealSheafData) :
    IsClosedImmersion I.subschemeι := inferInstance

variable (A : Type u) [CommRing A] [IsLocalRing A]

/-- The original quotient spectrum, before any residue-field identification. -/
def residueSpectrumInclusion : Spec (.of (A ⧸ IsLocalRing.maximalIdeal A)) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)))

/-- The original residue-spectrum inclusion is closed. -/
instance residueSpectrumInclusion_isClosedImmersion :
    IsClosedImmersion (residueSpectrumInclusion A) :=
  IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)))
    Ideal.Quotient.mk_surjective

/-- The actual full exceptional scheme; no reduction is taken. -/
def exceptionalCurve (hd : ringKrullDim A = 2) : Scheme.{u} :=
  (exceptionalIdeal A hd).subscheme

/-- The literal original exceptional closed immersion. -/
def exceptionalCurveInclusion (hd : ringKrullDim A = 2) :
    exceptionalCurve A hd ⟶ source A hd := (exceptionalIdeal A hd).subschemeι

/-- The original full exceptional inclusion is closed. -/
instance exceptionalCurveInclusion_isClosedImmersion (hd : ringKrullDim A = 2) :
    IsClosedImmersion (exceptionalCurveInclusion A hd) :=
  original_subscheme_closed (exceptionalIdeal A hd)

/-- The original κ-structure, constructed by the native closed-immersion lift. -/
def exceptionalStructureMap (hd : ringKrullDim A = 2) :
    exceptionalCurve A hd ⟶ Spec (.of (A ⧸ IsLocalRing.maximalIdeal A)) :=
  IsClosedImmersion.lift (residueSpectrumInclusion A)
    (exceptionalCurveInclusion A hd ≫ map A hd) (by
      change affineCenter A (IsLocalRing.maximalIdeal A) ≤
        (exceptionalIdeal A hd).map (map A hd)
      exact Scheme.IdealSheafData.le_map_iff_comap_le.mpr le_rfl)

/-- The original residue, exceptional inclusion and blowdown triangle. -/
theorem exceptionalStructureMap_triangle (hd : ringKrullDim A = 2) :
    exceptionalStructureMap A hd ≫ residueSpectrumInclusion A =
      exceptionalCurveInclusion A hd ≫ map A hd :=
  IsClosedImmersion.lift_fac _ _ _

/-- The full exceptional scheme is the actual scheme-theoretic closed fibre. -/
theorem exceptionalStructureMap_isPullback (hd : ringKrullDim A = 2) :
    IsPullback (exceptionalCurveInclusion A hd) (exceptionalStructureMap A hd)
      (map A hd) (residueSpectrumInclusion A) :=
  isPullback_of_isClosedImmersion _ _ _ _
    (exceptionalStructureMap_triangle A hd).symm (ordinaryCentre_kernel A hd)

/-- Properness is actual base change of the original ordinary blowdown. -/
theorem exceptionalStructureMap_isProper (hd : ringKrullDim A = 2) [IsNoetherianRing A] :
    IsProper (exceptionalStructureMap A hd) :=
  MorphismProperty.of_isPullback (P := @IsProper)
    (exceptionalStructureMap_isPullback A hd) inferInstance

/-- The same full exceptional structure map is surjective. -/
theorem exceptionalStructureMap_surjective (hd : ringKrullDim A = 2)
    [IsDomain A] [IsNoetherianRing A] :
    Surjective (exceptionalStructureMap A hd) :=
  MorphismProperty.of_isPullback (P := @Surjective)
    (exceptionalStructureMap_isPullback A hd) inferInstance

/-- The original quotient-field coefficients of the actual exceptional scheme. -/
def exceptionalCoefficients (hd : ringKrullDim A = 2) :
    A ⧸ IsLocalRing.maximalIdeal A →+* Γ(exceptionalCurve A hd, ⊤) :=
  (exceptionalStructureMap A hd).appTop.hom.comp
    (Scheme.ΓSpecIso (.of (A ⧸ IsLocalRing.maximalIdeal A))).inv.hom

/-- This coefficient map factors the original base-ring coefficient map. -/
theorem exceptionalCoefficients_quotient (hd : ringKrullDim A = 2) (a : A) :
    exceptionalCoefficients A hd (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a) =
      (exceptionalCurveInclusion A hd).appTop (ordinaryCoefficients A hd a) := by
  let q := Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)
  have hn := congrArg (fun f : CommRingCat.of A ⟶
      Γ(Spec (.of (A ⧸ IsLocalRing.maximalIdeal A)), ⊤) => f a)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom q))
  have ht := congrArg (fun f : exceptionalCurve A hd ⟶ Spec (.of A) =>
    f.appTop ((Scheme.ΓSpecIso (.of A)).inv a)) (exceptionalStructureMap_triangle A hd)
  exact (congrArg (exceptionalStructureMap A hd).appTop hn).trans ht

variable [IsDomain A]

/-- The original positive ideal-power normalization map is an isomorphism. -/
theorem ordinaryPositivePowerNormalization_isIso (hd : ringKrullDim A = 2)
    [IsNoetherianRing A] [IsIntegrallyClosed A]
    (hA : IsNagataRing.{u, 0} A) (hRat : NormalModificationH1Vanishing A) (n : ℕ) :
    IsIso (idealPowerNormalizationUnit A hd (n + 1)) := by
  let : IsIso (nu A hd) := normalization_isIso A hd hA hRat
  let X := source A hd
  let P := ordinaryIdealPower A hd (n + 1)
  let T := moduleTensorLeftFunctor X P
  let μ : originalUnit X ⟶
      (Modules.pushforward (nu A hd)).obj (originalUnit (normalization A hd)) :=
    structureModuleMap (nu A hd)
  let : IsIso μ := Hom.structureModuleMap_isIso (nu A hd)
  have hx : IsIso (T.map μ) := inferInstance
  exact isIso_of_original_square (C := X.Modules) (T.map μ)
    (normalizedPositivePowerProjectionIso A hd n) (rightUnitor (C := X.Modules) P)
    (idealPowerNormalizationUnit A hd (n + 1)) hx (positivePowerProjection_unit A hd n)

/-- Normalized H1 vanishing transports through the same original power map. -/
theorem ordinaryPositiveIdealPower_H1 (hd : ringKrullDim A = 2)
    [IsNoetherianRing A] [IsIntegrallyClosed A]
    (hA : IsNagataRing.{u, 0} A) (hRat : NormalModificationH1Vanishing A) (n : ℕ) :
    Subsingleton (Sheaf.H.{u + 1} (Cohomology.moduleAddSheaf (source A hd)
      (ordinaryIdealPower A hd (n + 1))) 1) := by
  let X := source A hd
  let Y := normalization A hd
  let f := nu A hd
  let : IsFinite f := nu_isFinite A hd hA
  let M : Y.Modules := normalizedIdealPower A hd (n + 1)
  let P := tensorPowerLineBundle Y (normalizedIdealLineBundle A hd) (n + 1)
  let : IsFiniteLocallyFree Y M := isFiniteLocallyFree_of_isLocallyRankOne
    (isLocallyRankOne_of_iso Y (normalizedIdealPowerIso A hd (n + 1)) P.property)
  let : M.IsQuasicoherent := quasicoherent_of_affineCharts M
    (fun R j _ => (coherent_of_finiteLocallyFree M R j).1)
  let : Subsingleton (Sheaf.H.{u + 1} (Cohomology.moduleAddSheaf Y M) 1) :=
    normalizedIdealPower_H1 A hd hA hRat (n + 1)
  have hpush : Subsingleton (Sheaf.H.{u + 1}
      (Cohomology.moduleAddSheaf X ((Modules.pushforward f).obj M)) 1) :=
    (Cohomology.moduleAffinePushforwardCohomologyLinearEquiv f
      (ordinaryCoefficients A hd) M 1).toEquiv.subsingleton
  have hv : IsIso (idealPowerNormalizationUnit A hd (n + 1)) :=
    ordinaryPositivePowerNormalization_isIso A hd hA hRat n
  let e : ordinaryIdealPower A hd (n + 1) ≅ (Modules.pushforward f).obj M :=
    @asIso X.Modules inferInstance _ _ (idealPowerNormalizationUnit A hd (n + 1)) hv
  exact Cohomology.moduleCohomology_subsingleton_of_iso e.symm 1 hpush

/-- The original exceptional restriction on global functions is onto. -/
theorem exceptionalRestriction_surjective (hd : ringKrullDim A = 2)
    [IsNoetherianRing A] [IsIntegrallyClosed A]
    (hA : IsNagataRing.{u, 0} A) (hRat : NormalModificationH1Vanishing A) :
    Function.Surjective (exceptionalCurveInclusion A hd).appTop := by
  let X := source A hd
  let i := exceptionalCurveInclusion A hd
  let S := Hom.idealSequence i
  have hS := Hom.idealSequence_shortExact i
  let e : ordinaryIdealPower A hd 1 ≅ idealModule i :=
    eqToIso (congrArg (fun J : X.IdealSheafData => idealModule J.subschemeι)
      (pow_one (exceptionalIdeal A hd)))
  let : Subsingleton (Sheaf.H.{u + 1} (Cohomology.moduleAddSheaf X S.X₁) 1) :=
    Cohomology.moduleCohomology_subsingleton_of_iso e 1
      (ordinaryPositiveIdealPower_H1 A hd hA hRat 0)
  let α := ordinaryCoefficients A hd
  let := Cohomology.moduleCohomologyModuleOfHom X α S.X₃ 0
  let := Cohomology.moduleCohomologyModuleOfHom X α S.X₁ (0 + 1)
  exact Cohomology.surjective_of_moduleCohomologyConnectingOfHom_zero_eq_zero
    (X := X) α S hS (by
      apply LinearMap.ext
      intro x
      exact Subsingleton.elim _ _)

/-- H0 of the full exceptional scheme is the original residue field. -/
theorem exceptionalCoefficients_bijective (hd : ringKrullDim A = 2)
    [IsNoetherianRing A] [IsIntegrallyClosed A]
    (hA : IsNagataRing.{u, 0} A) (hRat : NormalModificationH1Vanishing A) :
    Function.Bijective (exceptionalCoefficients A hd) := by
  let : Surjective (exceptionalStructureMap A hd) := exceptionalStructureMap_surjective A hd
  obtain ⟨e, _⟩ := (exceptionalStructureMap A hd).surjective
    (genericPoint (Spec (.of (A ⧸ IsLocalRing.maximalIdeal A))))
  let : Nonempty (⊤ : (exceptionalCurve A hd).Opens) := ⟨⟨e, trivial⟩⟩
  have hinj : Function.Injective (exceptionalCoefficients A hd) := by
    let : Field (A ⧸ IsLocalRing.maximalIdeal A) :=
      Ideal.Quotient.field (IsLocalRing.maximalIdeal A)
    exact RingHom.injective _
  refine ⟨hinj, ?_⟩
  intro z
  obtain ⟨c, hc⟩ := exceptionalRestriction_surjective A hd hA hRat z
  obtain ⟨a, ha⟩ := (ordinaryCoefficients_bijective A hd).2 c
  refine ⟨Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a, ?_⟩
  exact (exceptionalCoefficients_quotient A hd a).trans
    ((congrArg (exceptionalCurveInclusion A hd).appTop ha).trans hc)

/-- The bijective coefficient map itself, retaining its original quotient values. -/
def exceptionalCoefficientsEquiv (hd : ringKrullDim A = 2)
    [IsNoetherianRing A] [IsIntegrallyClosed A]
    (hA : IsNagataRing.{u, 0} A) (hRat : NormalModificationH1Vanishing A) :
    A ⧸ IsLocalRing.maximalIdeal A ≃+* Γ(exceptionalCurve A hd, ⊤) :=
  RingEquiv.ofBijective (exceptionalCoefficients A hd)
    (exceptionalCoefficients_bijective A hd hA hRat)

end AlgebraicGeometry.Scheme.RationalSingularities.MaximalIdealBlowup
