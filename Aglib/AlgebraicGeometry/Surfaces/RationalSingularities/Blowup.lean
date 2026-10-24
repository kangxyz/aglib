/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.RationalSingularities.Regular
public import Aglib.AlgebraicGeometry.Normalization.FunctionField
public import Aglib.AlgebraicGeometry.Properties.Normal.Affine
public import Aglib.AlgebraicGeometry.Blowup.Integral
public import Aglib.AlgebraicGeometry.Blowup.Properness
public import Aglib.AlgebraicGeometry.Blowup.AffineCenter.Support
public import Aglib.AlgebraicGeometry.Blowup.ProjectivePresentation
public import Aglib.AlgebraicGeometry.IdealSheaf.Cartier.Avoidance
public import Aglib.AlgebraicGeometry.Dimension.OpenCover
public import Aglib.AlgebraicGeometry.Cohomology.Proper.FibreDimension
public import Aglib.AlgebraicGeometry.Cohomology.Proper.FibreDimension.Local
public import Aglib.AlgebraicGeometry.Cohomology.Proper.BirationalStructureSheaf
public import Aglib.AlgebraicGeometry.Cohomology.Proper.StructureSheaf.Coefficient
public import Aglib.AlgebraicGeometry.Cohomology.Exact.Modules
public import Aglib.AlgebraicGeometry.Modules.Coherent.Basic
public import Aglib.RingTheory.Nagata.FiniteTypeSurface
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts

/-!
# The actual normalized ordinary blowup of a rational local surface

This first part of the rational-blowup argument constructs the literal generic
normalization of the ordinary maximal-ideal blowup. Actual birational affine
scalar maps and finite-type algebraicity give its finite normalization and
dimension bound. Universal normal-modification H1 vanishing and local proper
coherent vanishing give its original H1 and H2 results. The original exceptional
ideal pulls back through the actual integral-avoidance comparison.

Normality of the ordinary blowup, the ideal-power section algebra and the
exceptional-fibre section quotients remain later conclusions. They are not
inputs here. No completeness, Gorensteinness, regular source, resolution,
projectivity of the normalization, or finite-normalization oracle is used.

The mathematical route is Stacks 0B4X--0B4Z; all maps below are the original
maps of the supplied scheme and its native generic normalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open AlgebraicGeometry.Scheme.Modules.Invertible AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.RationalSingularities

universe u

section ActualCharts

variable {A : CommRingCat.{u}} {W : Scheme.{u}} (f : W ⟶ Spec A)

local instance [IsDomain A] : Nonempty (⊤ : (Spec A).Opens) :=
  ⟨⟨genericPoint (Spec A), trivial⟩⟩

/-- The literal structural scalar map on an original affine open. -/
private def chartScalar (U : W.Opens) : A →+* Γ(W, U) :=
  (f.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso A).inv.hom

private theorem chartScalar_finiteType [LocallyOfFiniteType f]
    (U : W.Opens) (hU : IsAffineOpen U) : (chartScalar f U).FiniteType :=
  (f.finiteType_appLE (isAffineOpen_top _) hU le_top).comp
    (RingHom.FiniteType.of_surjective (Scheme.ΓSpecIso A).inv.hom
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso A).inv).2)

private theorem chartScalar_injective [IsDomain A] [IsIntegral W]
    [IsDominant f] [QuasiCompact f] (U : W.Opens) [Nonempty U] :
    Function.Injective (chartScalar f U) := by
  let : IsSchemeTheoreticallyDominant f := IsSchemeTheoreticallyDominant.of_isDominant f
  exact (AlgebraicGeometry.map_injective_of_isIntegral W (homOfLE (le_top : U ≤ ⊤))).comp
    ((f.app_injective ⊤).comp
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso A).inv).1)

private theorem chartScalar_germ [IsDomain A] [IsIntegral W] [IsDominant f]
    (U : W.Opens) [Nonempty U] :
    CommRingCat.ofHom (chartScalar f U) ≫ W.germToFunctionField U =
      (Scheme.ΓSpecIso A).inv ≫ (Spec A).germToFunctionField ⊤ ≫
        CommRingCat.ofHom (Scheme.functionFieldMap f) := by
  let : Nonempty (⊤ : W.Opens) := ⟨⟨genericPoint W, trivial⟩⟩
  have hg : genericPoint W ∈ U :=
    ((genericPoint_spec W).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  have hres : W.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫
      W.germToFunctionField U = W.germToFunctionField ⊤ :=
    W.presheaf.germ_res (homOfLE (le_top : U ≤ ⊤)) (genericPoint W) hg
  rw [Scheme.functionFieldMap_germ]
  change (Scheme.ΓSpecIso A).inv ≫ f.appTop ≫
      W.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ W.germToFunctionField U =
    (Scheme.ΓSpecIso A).inv ≫ f.appTop ≫ W.germToFunctionField ⊤
  rw [hres]

private theorem chartScalar_germ_apply [IsDomain A] [IsIntegral W] [IsDominant f]
    (U : W.Opens) [Nonempty U] (a : A) :
    W.germToFunctionField U (chartScalar f U a) =
      Scheme.functionFieldMap f (algebraMap A (Spec A).functionField a) := by
  exact congrArg (fun k : A ⟶ W.functionField => k a) (chartScalar_germ f U)

private theorem chartScalar_isAlgebraic [IsDomain A] [IsIntegral W] [IsDominant f]
    (hff : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f)))
    (U : W.Opens) [Nonempty U] :
    letI := (chartScalar f U).toAlgebra
    Algebra.IsAlgebraic A Γ(W, U) := by
  let := (chartScalar f U).toAlgebra
  let := hff
  refine ⟨fun b => ?_⟩
  obtain ⟨z, hz⟩ := (ConcreteCategory.bijective_of_isIso
    (CommRingCat.ofHom (Scheme.functionFieldMap f))).2 (W.germToFunctionField U b)
  obtain ⟨a, s, hs, has⟩ := IsFractionRing.div_surjective A z
  have hs0 : s ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hs
  have hsF : Scheme.functionFieldMap f (algebraMap A (Spec A).functionField s) ≠ 0 := by
    apply (map_ne_zero (Scheme.functionFieldMap f)).mpr
    exact (map_ne_zero_iff _ (IsFractionRing.injective A (Spec A).functionField)).mpr hs0
  have hrat : Scheme.functionFieldMap f (algebraMap A (Spec A).functionField a) /
      Scheme.functionFieldMap f (algebraMap A (Spec A).functionField s) =
        W.germToFunctionField U b := by
    rw [← map_div₀, has]
    exact hz
  have hrel : chartScalar f U s * b = chartScalar f U a := by
    apply W.germToFunctionField_injective U
    rw [map_mul, chartScalar_germ_apply, chartScalar_germ_apply]
    simpa only [mul_comm] using ((div_eq_iff hsF).mp hrat).symm
  refine ⟨Polynomial.C s * Polynomial.X - Polynomial.C a, ?_, ?_⟩
  · intro hp
    apply hs0
    have hc := congrArg (fun p : Polynomial A => p.coeff 1) hp
    simpa using hc
  · change Polynomial.aeval b (Polynomial.C s * Polynomial.X - Polynomial.C a) = 0
    simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X,
      RingHom.algebraMap_toAlgebra, sub_eq_zero]
    exact hrel

private theorem actualChart_nagata_and_dimension
    [IsDomain A] [IsIntegral W] [IsDominant f] [QuasiCompact f] [LocallyOfFiniteType f]
    (hA : IsNagataRing.{u, 0} A) (hd : ringKrullDim A ≤ 2)
    (hff : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f)))
    (U : W.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    IsNagataRing.{u, 0} Γ(W, U) ∧ ringKrullDim Γ(W, U) ≤ 2 := by
  let := (chartScalar f U).toAlgebra
  let : Algebra.FiniteType A Γ(W, U) := chartScalar_finiteType f U hU
  let : Algebra.IsAlgebraic A Γ(W, U) := chartScalar_isAlgebraic f hff U
  exact ⟨hA.of_finiteType_isAlgebraic_of_dimLE_two hd (chartScalar_injective f U),
    hA.ringKrullDim_le_two_of_finiteType_isAlgebraic hd (chartScalar_injective f U)⟩

private theorem actualModification_dimension
    [IsDomain A] [IsIntegral W] [IsDominant f] [QuasiCompact f] [LocallyOfFiniteType f]
    (hA : IsNagataRing.{u, 0} A) (hd : ringKrullDim A ≤ 2)
    (hff : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f))) :
    topologicalKrullDim W ≤ 2 := by
  let C : W.OpenCover := Scheme.Cover.mkOfCovers W.affineOpens
    (fun U => U.1.toScheme) (fun U => U.1.ι) (by
      intro x
      obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset
        (show x ∈ (⊤ : W.Opens) from trivial)
      exact ⟨⟨U, hU⟩, ⟨⟨x, hx⟩, rfl⟩⟩) (fun _ => inferInstance)
  apply Scheme.topologicalKrullDim_le_of_openCover C 2
  intro U
  change topologicalKrullDim U.1 ≤ 2
  by_cases hne : Nonempty U.1
  · let := hne
    calc
      _ = topologicalKrullDim (Spec Γ(W, U.1)) :=
        IsHomeomorph.topologicalKrullDim_eq _ U.2.isoSpec.hom.homeomorph.isHomeomorph
      _ = ringKrullDim Γ(W, U.1) := PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _
      _ ≤ 2 := (actualChart_nagata_and_dimension f hA hd hff U.1 U.2).2
  · let : IsEmpty U.1 := ⟨fun x => hne ⟨x⟩⟩
    exact (topologicalKrullDim_zero_of_discreteTopology U.1).trans (by norm_num)

end ActualCharts

namespace MaximalIdealBlowup

open AlgebraicGeometry.Scheme.Blowup

variable (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]

/-- The actual ordinary maximal-ideal blowup datum. -/
def datum : BlowupDatum (affineCenter A (IsLocalRing.maximalIdeal A)) :=
  blowupDatum (affineCenter A (IsLocalRing.maximalIdeal A))

/-- The original local closed point is nongeneric in dimension two. -/
theorem closedPoint_ne_generic (hd : ringKrullDim A = 2) :
    (IsLocalRing.closedPoint A : Spec (.of A)) ≠ genericPoint (Spec (.of A)) := by
  intro he
  have hf : IsField ((Spec (.of A)).presheaf.stalk (IsLocalRing.closedPoint A)) :=
    he.symm ▸ Field.toIsField (Spec (.of A)).functionField
  have hA : IsField A := (stalkClosedPointIso (.of A)).symm.commRingCatIsoToRingEquiv.isField hf
  have hh := ringKrullDim_eq_zero_of_isField hA
  rw [hd] at hh
  norm_num at hh

private theorem generic_avoids_centre (hd : ringKrullDim A = 2) :
    genericPoint (Spec (.of A)) ∉
      ((affineCenter A (IsLocalRing.maximalIdeal A)).support : Set (Spec (.of A))) := by
  rw [support_affineCenter, PrimeSpectrum.zeroLocus_eq_singleton]
  exact (closedPoint_ne_generic A hd).symm

/-- The literal ordinary blowup source. The dimension witness supplies its integral instances. -/
def source (_ : ringKrullDim A = 2) : Scheme.{u} := (datum A).Y

/-- The original ordinary blowdown. -/
def map (hd : ringKrullDim A = 2) : source A hd ⟶ Spec (.of A) := (datum A).map

instance source_isIntegral (hd : ringKrullDim A = 2) : IsIntegral (source A hd) :=
  (datum A).isIntegral_of_genericPoint_not_mem_support (generic_avoids_centre A hd)

instance map_isDominant (hd : ringKrullDim A = 2) : IsDominant (map A hd) :=
  (datum A).isDominant_of_genericPoint_not_mem_support (generic_avoids_centre A hd)

instance map_isProper [IsNoetherianRing A] (hd : ringKrullDim A = 2) : IsProper (map A hd) :=
  (datum A).isProper_of_spectrum

instance source_isLocallyNoetherian [IsNoetherianRing A] (hd : ringKrullDim A = 2) :
    IsLocallyNoetherian (source A hd) := LocallyOfFiniteType.isLocallyNoetherian (map A hd)

/-- Birationality is the isomorphism of the original blowdown function-field map. -/
theorem map_fieldMap_isIso (hd : ringKrullDim A = 2) :
    IsIso (CommRingCat.ofHom (Scheme.functionFieldMap (map A hd))) :=
  (datum A).functionFieldMap_isIso (generic_avoids_centre A hd)

/-- Original ordinary-blowup global coefficients, before normality of that blowup is known. -/
def ordinaryCoefficients (hd : ringKrullDim A = 2) : A →+* Γ(source A hd, ⊤) :=
  (map A hd).appTop.hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom

/-- A normal base gives the original ordinary-blowup coefficient bijection.
Normality of the ordinary blowup is not used. -/
theorem ordinaryCoefficients_bijective [IsNoetherianRing A] [IsIntegrallyClosed A]
    (hd : ringKrullDim A = 2) : Function.Bijective (ordinaryCoefficients A hd) :=
  Hom.bijective_structuralCoefficients_of_isProper_birational A (map A hd)
    (fun x => (isIntegrallyClosed_and_isDomain_stalk_Spec A x).symm) (map_fieldMap_isIso A hd)

/-- The actual generic-point inclusion of the ordinary blowup. -/
def gamma (hd : ringKrullDim A = 2) : Spec (source A hd).functionField ⟶ source A hd :=
  (source A hd).fromSpecStalk (genericPoint (source A hd))

/-- Normalize the actual generic-point inclusion in its original function field. -/
def normalization (hd : ringKrullDim A = 2) : Scheme.{u} := (gamma A hd).normalization

/-- The literal normalization arrow to the ordinary blowup. -/
def nu (hd : ringKrullDim A = 2) : normalization A hd ⟶ source A hd :=
  (gamma A hd).fromNormalization

/-- The original composite to the original local base. -/
def q (hd : ringKrullDim A = 2) : normalization A hd ⟶ Spec (.of A) := nu A hd ≫ map A hd

/-- The original triangle is retained literally. -/
theorem nu_map (hd : ringKrullDim A = 2) : nu A hd ≫ map A hd = q A hd := rfl

instance normalization_isIntegral (hd : ringKrullDim A = 2) :
    IsIntegral (normalization A hd) := inferInstanceAs (IsIntegral (gamma A hd).normalization)

instance nu_isDominant (hd : ringKrullDim A = 2) : IsDominant (nu A hd) :=
  Scheme.genericNormalization_isDominant (source A hd)

instance q_isDominant (hd : ringKrullDim A = 2) : IsDominant (q A hd) :=
  inferInstanceAs (IsDominant (nu A hd ≫ map A hd))

/-- The constructed normalization is normal on its actual stalks. -/
theorem normalization_normalStalks (hd : ringKrullDim A = 2) :
    NormalStalks (normalization A hd) := Scheme.genericNormalization_normalStalks (source A hd)

/-- Finiteness is derived from the actual original affine coefficient maps and Nagata GF2. -/
theorem nu_isFinite [IsNoetherianRing A] (hd : ringKrullDim A = 2)
    (hA : IsNagataRing.{u, 0} A) : IsFinite (nu A hd) := by
  apply Scheme.genericNormalization_isFinite (source A hd)
  intro U hne
  let := hne
  exact (actualChart_nagata_and_dimension (map A hd) hA hd.le (map_fieldMap_isIso A hd)
    U.1 U.2).1

/-- The actual normalized blowdown is proper; no projectivity of its source is assumed. -/
theorem q_isProper [IsNoetherianRing A] (hd : ringKrullDim A = 2)
    (hA : IsNagataRing.{u, 0} A) : IsProper (q A hd) := by
  let : IsFinite (nu A hd) := nu_isFinite A hd hA
  exact inferInstanceAs (IsProper (nu A hd ≫ map A hd))

/-- The literal composite retains the original function-field isomorphism. -/
theorem q_fieldMap_isIso (hd : ringKrullDim A = 2) :
    IsIso (CommRingCat.ofHom (Scheme.functionFieldMap (q A hd))) := by
  let : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap (map A hd))) := map_fieldMap_isIso A hd
  let : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap (nu A hd))) :=
    Scheme.genericNormalization_fieldMap_isIso (source A hd)
  change IsIso (CommRingCat.ofHom (Scheme.functionFieldMap (nu A hd ≫ map A hd)))
  rw [Scheme.functionFieldMap_comp]
  change IsIso (CommRingCat.ofHom (Scheme.functionFieldMap (map A hd)) ≫
    CommRingCat.ofHom (Scheme.functionFieldMap (nu A hd)))
  infer_instance

/-- Local Noetherianity of the actual normalization follows from the finite original map. -/
theorem normalization_isLocallyNoetherian [IsNoetherianRing A] (hd : ringKrullDim A = 2)
    (hA : IsNagataRing.{u, 0} A) : IsLocallyNoetherian (normalization A hd) := by
  let : IsProper (q A hd) := q_isProper A hd hA
  exact LocallyOfFiniteType.isLocallyNoetherian (q A hd)

/-- The actual source dimension is derived from its original finite-type algebraic charts. -/
theorem normalization_dimension_le_two [IsNoetherianRing A] (hd : ringKrullDim A = 2)
    (hA : IsNagataRing.{u, 0} A) : topologicalKrullDim (normalization A hd) ≤ 2 := by
  let : IsProper (q A hd) := q_isProper A hd hA
  exact actualModification_dimension (q A hd) hA hd.le (q_fieldMap_isIso A hd)

/-- The full actual maximal-ideal fibre has dimension at most one. -/
theorem closedFibre_dimension_le_one [IsNoetherianRing A] (hd : ringKrullDim A = 2)
    (hA : IsNagataRing.{u, 0} A) :
    topologicalKrullDim (idealThickeningSpace (q A hd) (IsLocalRing.maximalIdeal A)) ≤ 1 :=
  closedFibre_dim_le_one_of_integral_source (q A hd)
    (normalization_dimension_le_two A hd hA) (closedPoint_ne_generic A hd)

/-- The honest universal rationality predicate kills the original structure H1
of this constructed normal proper birational model. -/
theorem normalization_structureH1 [IsNoetherianRing A] (hd : ringKrullDim A = 2)
    (hA : IsNagataRing.{u, 0} A) (hRat : NormalModificationH1Vanishing A) :
    Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf (normalization A hd)
        (SheafOfModules.unit (normalization A hd).ringCatSheaf)) 1) := by
  let : IsProper (q A hd) := q_isProper A hd hA
  exact hRat (normalization A hd) (q A hd)
    (normalization_normalStalks A hd) (q_fieldMap_isIso A hd)

/-- The original structural coefficient map, without a replacement scalar action. -/
def coefficients (hd : ringKrullDim A = 2) : A →+* Γ(normalization A hd, ⊤) :=
  (q A hd).appTop.hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom

/-- Normality of the original base identifies its scalars with the actual normalized sections. -/
theorem coefficients_bijective [IsNoetherianRing A] [IsIntegrallyClosed A]
    (hd : ringKrullDim A = 2) (hA : IsNagataRing.{u, 0} A) :
    Function.Bijective (coefficients A hd) := by
  let : IsProper (q A hd) := q_isProper A hd hA
  exact Hom.bijective_structuralCoefficients_of_isProper_birational A (q A hd)
    (fun x => (isIntegrallyClosed_and_isDomain_stalk_Spec A x).symm) (q_fieldMap_isIso A hd)

/-- Higher coherent cohomology vanishes on the original normalization, without completeness. -/
theorem normalization_coherent_higher_vanishing [IsNoetherianRing A]
    (hd : ringKrullDim A = 2) (hA : IsNagataRing.{u, 0} A)
    (M : (normalization A hd).Modules) (hM : affineLocallyFiniteType (normalization A hd) M)
    (n : ℕ) (hn : 1 < n) :
    Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (normalization A hd) M) n) := by
  let : IsProper (q A hd) := q_isProper A hd hA
  exact subsingleton_moduleCohomology_of_local_of_dim_firstThickening (q A hd) M hM 1 n
    (closedFibre_dimension_le_one A hd hA) hn

/-- The same vanishing retains the original structural A-action on the module object. -/
theorem normalization_coherent_higher_isZero [IsNoetherianRing A]
    (hd : ringKrullDim A = 2) (hA : IsNagataRing.{u, 0} A)
    (M : (normalization A hd).Modules) (hM : affineLocallyFiniteType (normalization A hd) M)
    (n : ℕ) (hn : 1 < n) :
    IsZero ((moduleCohomologyFunctorOfHom (normalization A hd) (coefficients A hd) n).obj M) := by
  let : Subsingleton
      ((moduleCohomologyFunctorOfHom (normalization A hd) (coefficients A hd) n).obj M) := by
    change Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (normalization A hd) M) n)
    exact normalization_coherent_higher_vanishing A hd hA M hM n hn
  exact ModuleCat.isZero_of_subsingleton _

/-- A coherent quotient by an actual finite row of original global sections has H1 zero.
Kernel coherence and H2 are derived; neither is an input oracle. -/
theorem normalization_finiteRow_H1 [IsNoetherianRing A]
    (hd : ringKrullDim A = 2) (hA : IsNagataRing.{u, 0} A)
    (hRat : NormalModificationH1Vanishing A)
    {ι : Type u} [Finite ι] (M : (normalization A hd).Modules)
    (hM : affineLocallyFiniteType (normalization A hd) M)
    (s : ι → (SheafOfModules.unit (normalization A hd).ringCatSheaf ⟶ M))
    [Epi (Sigma.desc s)] :
    Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (normalization A hd) M) 1) := by
  let Y := normalization A hd
  let : IsLocallyNoetherian Y := normalization_isLocallyNoetherian A hd hA
  let O : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  let r : (∐ fun _ : ι => O) ⟶ M := Sigma.desc s
  have hO : affineLocallyFiniteType Y O := affineLocallyFiniteType_unit Y
  have hfree : affineLocallyFiniteType Y (∐ fun _ : ι => O) :=
    (affineLocallyFiniteType Y).prop_coproduct (fun _ => hO)
  have hK : affineLocallyFiniteType Y (kernel r) :=
    (affineLocallyFiniteType Y).prop_kernel r hfree hM
  let S := ShortComplex.mk (kernel.ι r) r (kernel.condition r)
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_kernel r
      epi_g := inferInstanceAs (Epi (Sigma.desc s)) }
  have hfreeH1 : Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf Y (∐ fun _ : ι => O)) 1) :=
    moduleCohomology_subsingleton_coproduct (𝟭 Y.Modules) (fun _ : ι => O) 1
      (fun _ => normalization_structureH1 A hd hA hRat)
  exact moduleCohomology_subsingleton_X₃ S hS 1 hfreeH1
    (normalization_coherent_higher_vanishing A hd hA (kernel r) hK 2 (by decide))

/-- The full original exceptional ideal on the ordinary blowup. -/
def exceptionalIdeal (hd : ringKrullDim A = 2) : (source A hd).IdealSheafData :=
  (affineCenter A (IsLocalRing.maximalIdeal A)).comap (map A hd)

/-- The literal inverse image of that original exceptional ideal under normalization. -/
def normalizedExceptionalIdeal (hd : ringKrullDim A = 2) :
    (normalization A hd).IdealSheafData := (exceptionalIdeal A hd).comap (nu A hd)

/-- This is the full maximal-ideal centre pulled back along the original composite. -/
theorem normalizedExceptionalIdeal_eq (hd : ringKrullDim A = 2) :
    normalizedExceptionalIdeal A hd =
      (affineCenter A (IsLocalRing.maximalIdeal A)).comap (q A hd) :=
  (Scheme.IdealSheafData.comap_comp _ (nu A hd) (map A hd)).symm

/-- The actual map of the inverse-image exceptional subscheme. -/
def normalizedCentreMap (hd : ringKrullDim A = 2) :
    (normalizedExceptionalIdeal A hd).subscheme ⟶ (exceptionalIdeal A hd).subscheme :=
  (normalizedExceptionalIdeal A hd).subschemeMap (exceptionalIdeal A hd) (nu A hd)
    ((exceptionalIdeal A hd).le_map_comap (nu A hd))

/-- The original exceptional-centre triangle. -/
theorem normalizedCentreMap_ι (hd : ringKrullDim A = 2) :
    normalizedCentreMap A hd ≫ (exceptionalIdeal A hd).subschemeι =
      (normalizedExceptionalIdeal A hd).subschemeι ≫ nu A hd :=
  Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _

/-- The full original exceptional-centre square is Cartesian. -/
theorem normalizedCentre_isPullback (hd : ringKrullDim A = 2) :
    IsPullback (normalizedCentreMap A hd) (normalizedExceptionalIdeal A hd).subschemeι
      (exceptionalIdeal A hd).subschemeι (nu A hd) :=
  (isPullback_of_isClosedImmersion (normalizedExceptionalIdeal A hd).subschemeι
    (exceptionalIdeal A hd).subschemeι (normalizedCentreMap A hd) (nu A hd)
    (normalizedCentreMap_ι A hd).symm (by simp [normalizedExceptionalIdeal])).flip

private theorem normalization_avoids_exceptional (hd : ringKrullDim A = 2) :
    ¬ Set.range (nu A hd) ⊆ Set.range (exceptionalIdeal A hd).subschemeι := by
  intro h
  have hx := h (Set.mem_range_self (genericPoint (normalization A hd)))
  rw [Scheme.IdealSheafData.range_subschemeι,
    Scheme.map_genericPoint_of_isDominant (normalization A hd) (nu A hd)] at hx
  change genericPoint (source A hd) ∈
    ((affineCenter A (IsLocalRing.maximalIdeal A)).comap (map A hd)).support at hx
  rw [Scheme.IdealSheafData.support_comap] at hx
  change map A hd (genericPoint (source A hd)) ∈
    (affineCenter A (IsLocalRing.maximalIdeal A)).support at hx
  rw [Scheme.map_genericPoint_of_isDominant (source A hd) (map A hd)] at hx
  exact generic_avoids_centre A hd hx

/-- The actual normalized exceptional support is nonempty, by proper dominance
of the original composite over the original local closed point. -/
theorem normalizedExceptional_nonempty [IsNoetherianRing A] (hd : ringKrullDim A = 2)
    (hA : IsNagataRing.{u, 0} A) :
    Set.Nonempty ((normalizedExceptionalIdeal A hd).support : Set (normalization A hd)) := by
  let : IsProper (q A hd) := q_isProper A hd hA
  obtain ⟨y, hy⟩ := (q A hd).surjective (IsLocalRing.closedPoint A)
  refine ⟨y, ?_⟩
  rw [normalizedExceptionalIdeal_eq, Scheme.IdealSheafData.support_comap]
  change q A hd y ∈
    ((affineCenter A (IsLocalRing.maximalIdeal A)).support : Set (Spec (.of A)))
  rw [support_affineCenter (IsLocalRing.maximalIdeal A)]
  change IsLocalRing.maximalIdeal A ≤ (q A hd y : PrimeSpectrum A).asIdeal
  exact le_of_eq (congrArg (fun x : Spec (.of A) => (x : PrimeSpectrum A).asIdeal) hy).symm

/-- Integral avoidance makes the original nonflat ideal-pullback map an isomorphism. -/
theorem normalizedIdealPullback_isIso (hd : ringKrullDim A = 2) :
    IsIso (Hom.idealPullbackMap (exceptionalIdeal A hd).subschemeι
      (normalizedExceptionalIdeal A hd).subschemeι (nu A hd) (normalizedCentreMap A hd)
      (normalizedCentreMap_ι A hd)) :=
  Hom.idealPullbackMap_isIso_of_integral_avoidance (exceptionalIdeal A hd).subschemeι
    (normalizedExceptionalIdeal A hd).subschemeι (nu A hd) (normalizedCentreMap A hd)
    (normalizedCentreMap_ι A hd) (normalizedCentre_isPullback A hd)
    (datum A).cartier (normalization_avoids_exceptional A hd)

/-- The actual normalized exceptional ideal is the original ideal pullback. -/
def normalizedIdealPullbackIso (hd : ringKrullDim A = 2) :
    (Modules.pullback (nu A hd)).obj (Hom.idealModule (exceptionalIdeal A hd).subschemeι) ≅
      Hom.idealModule (normalizedExceptionalIdeal A hd).subschemeι := by
  let := normalizedIdealPullback_isIso A hd
  exact asIso (Hom.idealPullbackMap (exceptionalIdeal A hd).subschemeι
    (normalizedExceptionalIdeal A hd).subschemeι (nu A hd) (normalizedCentreMap A hd)
    (normalizedCentreMap_ι A hd))

/-- The comparison retains the original ideal inclusion, without flatness of normalization. -/
theorem normalizedIdealPullbackIso_inclusion (hd : ringKrullDim A = 2) :
    (normalizedIdealPullbackIso A hd).hom ≫
        Hom.idealInclusion (normalizedExceptionalIdeal A hd).subschemeι =
      (Modules.pullback (nu A hd)).map (Hom.idealInclusion (exceptionalIdeal A hd).subschemeι) ≫
        (pullbackUnitIso (nu A hd)).hom :=
  Hom.idealPullbackMap_inclusion _ _ _ _ _

/-- The original normalized exceptional image ideal is invertible. -/
theorem normalizedExceptional_isLocallyRankOne (hd : ringKrullDim A = 2) :
    IsLocallyRankOne (normalization A hd)
      (Hom.idealModule (normalizedExceptionalIdeal A hd).subschemeι) :=
  isLocallyRankOne_of_iso (normalization A hd) (normalizedIdealPullbackIso A hd)
    (pullback_locallyRankOne (nu A hd) _ (datum A).cartier)

end MaximalIdealBlowup

end AlgebraicGeometry.Scheme.RationalSingularities
