/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.Integral
public import Aglib.AlgebraicGeometry.Blowup.Properness
public import Aglib.AlgebraicGeometry.Blowup.AffineCenter.Support
public import Aglib.AlgebraicGeometry.IdealSheaf.Cartier.Avoidance
public import Aglib.AlgebraicGeometry.Normalization.FunctionField
public import Aglib.RingTheory.Nagata.FiniteTypeSurface

/-!
# A finite normal cover of the actual normalized ideal blowup

The base construction is the native ordinary blowup of a specified nonzero
ideal, followed by its literal generic normalization in the original function
field. Nagata finiteness is derived on the actual blowup charts by GF2.
The ideal may be the unit ideal.

The actual image ideal remains invertible after the nonflat normalization,
with nonzero regular local frames. The general dominant ideal-pullback lemmas
retain the original inclusion into the structure sheaf. The second finite
normalization over the extension field is a subsequent construction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Scheme.Modules Scheme.Modules.Invertible
open scoped nonZeroDivisors

namespace AlgebraicGeometry.Scheme.Birational.NormalizedBlowupCover

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

end ActualCharts

section IdealPullback

variable {W V : Scheme.{u}} [IsIntegral W] [IsIntegral V]
  (I : W.IdealSheafData) (f : V ⟶ W) [IsDominant f]

/-- A dominant map between integral schemes avoids an actual ideal whose
support misses the original generic point. -/
theorem avoids_ideal (hI : genericPoint W ∉ (I.support : Set W)) :
    ¬ Set.range f ⊆ Set.range I.subschemeι := by
  intro h
  have hx := h (Set.mem_range_self (genericPoint V))
  rw [Scheme.IdealSheafData.range_subschemeι,
    Scheme.map_genericPoint_of_isDominant V f] at hx
  exact hI hx

/-- The canonical map from the actual inverse-image centre to its centre. -/
def centreMap : (I.comap f).subscheme ⟶ I.subscheme :=
  (I.comap f).subschemeMap I f (I.le_map_comap f)

omit [IsIntegral W] [IsIntegral V] [IsDominant f] in
@[reassoc] theorem centreMap_ι :
    centreMap I f ≫ I.subschemeι = (I.comap f).subschemeι ≫ f :=
  Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _

omit [IsIntegral W] [IsIntegral V] [IsDominant f] in
/-- The centre comparison is the literal closed-subscheme pullback square. -/
theorem centre_isPullback :
    IsPullback (centreMap I f) (I.comap f).subschemeι I.subschemeι f :=
  (isPullback_of_isClosedImmersion (I.comap f).subschemeι I.subschemeι
    (centreMap I f) f (centreMap_ι I f).symm (by simp)).flip

/-- The original ideal pullback map is an isomorphism without flatness,
using dominance and the actual generic avoidance condition. -/
theorem idealPullback_isIso
    (hI : genericPoint W ∉ (I.support : Set W))
    (hCartier : IsLocallyRankOne W (Hom.idealModule I.subschemeι)) :
    IsIso (Hom.idealPullbackMap I.subschemeι (I.comap f).subschemeι f
      (centreMap I f) (centreMap_ι I f)) :=
  Hom.idealPullbackMap_isIso_of_integral_avoidance I.subschemeι
    (I.comap f).subschemeι f (centreMap I f) (centreMap_ι I f)
    (centre_isPullback I f) hCartier (avoids_ideal I f hI)

/-- The nonflat image ideal is the actual pullback of the original invertible ideal. -/
def idealPullbackIso
    (hI : genericPoint W ∉ (I.support : Set W))
    (hCartier : IsLocallyRankOne W (Hom.idealModule I.subschemeι)) :
    (Modules.pullback f).obj (Hom.idealModule I.subschemeι) ≅
      Hom.idealModule (I.comap f).subschemeι := by
  let := idealPullback_isIso I f hI hCartier
  exact asIso (Hom.idealPullbackMap I.subschemeι (I.comap f).subschemeι f
    (centreMap I f) (centreMap_ι I f))

/-- The nonflat comparison retains the original inclusion into the structure sheaf. -/
theorem idealPullbackIso_inclusion
    (hI : genericPoint W ∉ (I.support : Set W))
    (hCartier : IsLocallyRankOne W (Hom.idealModule I.subschemeι)) :
    (idealPullbackIso I f hI hCartier).hom ≫ Hom.idealInclusion (I.comap f).subschemeι =
      (Modules.pullback f).map (Hom.idealInclusion I.subschemeι) ≫
        (pullbackUnitIso f).hom :=
  Hom.idealPullbackMap_inclusion _ _ _ _ _

/-- An actual Cartier ideal remains invertible after a dominant nonflat pullback. -/
theorem imageIdeal_isLocallyRankOne
    (hI : genericPoint W ∉ (I.support : Set W))
    (hCartier : IsLocallyRankOne W (Hom.idealModule I.subschemeι)) :
    IsLocallyRankOne V (Hom.idealModule (I.comap f).subschemeι) :=
  isLocallyRankOne_of_iso V (idealPullbackIso I f hI hCartier)
    (pullback_locallyRankOne f _ hCartier)

/-- Each actual image ideal has a nonzero regular local frame on an affine
neighborhood. The frame generates the literal section ideal. -/
theorem imageIdeal_nonzero_localFrame
    (hI : genericPoint W ∉ (I.support : Set W))
    (hCartier : IsLocallyRankOne W (Hom.idealModule I.subschemeι)) (v : V) :
    ∃ U : V.Opens, IsAffineOpen U ∧ v ∈ U ∧
      ∃ t : Γ(V, U), t ≠ 0 ∧ IsSMulRegular Γ(V, U) t ∧
        RingHom.ker ((I.comap f).subschemeι.app U).hom = Ideal.span {t} := by
  obtain ⟨U, hU, hvU, t, ht, hgen⟩ :=
    Hom.exists_affine_regular_idealGenerator_of_isLocallyRankOne
      (I.comap f).subschemeι (imageIdeal_isLocallyRankOne I f hI hCartier) v
  let : Nonempty U := ⟨⟨v, hvU⟩⟩
  refine ⟨U, hU, hvU, t, ?_, ht, hgen⟩
  intro hz
  have h10 : (1 : Γ(V, U)) = 0 := ht (by simp [hz])
  exact one_ne_zero h10

end IdealPullback

namespace Base

open AlgebraicGeometry.Scheme.Blowup

variable (A : Type u) [CommRing A] [IsDomain A] (J : Ideal A) (hJ : J ≠ ⊥)

/-- The literal native ordinary blowup of the specified ideal. -/
def datum : BlowupDatum (affineCenter A J) := blowupDatum (affineCenter A J)

/-- A nonzero ideal, including the unit ideal, misses the original generic point. -/
theorem generic_avoids_centre (hJ : J ≠ ⊥) :
    genericPoint (Spec (.of A)) ∉ ((affineCenter A J).support : Set (Spec (.of A))) := by
  rw [support_affineCenter, genericPoint_eq_bot_of_affine]
  change ¬ J ≤ ⊥
  exact fun h => hJ (le_bot_iff.mp h)

/-- The source of the literal ordinary blowup. -/
def source (_ : J ≠ ⊥) : Scheme.{u} := (datum A J).Y

/-- The original ordinary blowdown. -/
def map : source A J hJ ⟶ Spec (.of A) := (datum A J).map

instance source_isIntegral : IsIntegral (source A J hJ) :=
  (datum A J).isIntegral_of_genericPoint_not_mem_support (generic_avoids_centre A J hJ)

instance map_isDominant : IsDominant (map A J hJ) :=
  (datum A J).isDominant_of_genericPoint_not_mem_support (generic_avoids_centre A J hJ)

instance map_isProper [IsNoetherianRing A] : IsProper (map A J hJ) :=
  (datum A J).isProper_of_spectrum

instance source_isLocallyNoetherian [IsNoetherianRing A] :
    IsLocallyNoetherian (source A J hJ) := LocallyOfFiniteType.isLocallyNoetherian (map A J hJ)

/-- The isomorphism is induced by the original blowdown. -/
theorem map_fieldMap_isIso :
    IsIso (CommRingCat.ofHom (Scheme.functionFieldMap (map A J hJ))) :=
  (datum A J).functionFieldMap_isIso (generic_avoids_centre A J hJ)

/-- The actual generic inclusion of the ordinary blowup. -/
def gamma : Spec (source A J hJ).functionField ⟶ source A J hJ :=
  (source A J hJ).fromSpecStalk (genericPoint (source A J hJ))

/-- The literal generic normalization in the original function field. -/
def normalization : Scheme.{u} := (gamma A J hJ).normalization

/-- The original normalization map. -/
def nu : normalization A J hJ ⟶ source A J hJ := (gamma A J hJ).fromNormalization

/-- The original normalized blowdown to the original affine base. -/
def a : normalization A J hJ ⟶ Spec (.of A) := nu A J hJ ≫ map A J hJ

@[reassoc] theorem nu_map : nu A J hJ ≫ map A J hJ = a A J hJ := rfl

instance normalization_isIntegral : IsIntegral (normalization A J hJ) :=
  inferInstanceAs (IsIntegral (gamma A J hJ).normalization)

instance nu_isDominant : IsDominant (nu A J hJ) :=
  Scheme.genericNormalization_isDominant (source A J hJ)

instance a_isDominant : IsDominant (a A J hJ) :=
  inferInstanceAs (IsDominant (nu A J hJ ≫ map A J hJ))

/-- Normality is supplied on every actual stalk. -/
theorem normalization_normalStalks : NormalStalks (normalization A J hJ) :=
  Scheme.genericNormalization_normalStalks (source A J hJ)

/-- GF2 proves finiteness on the actual finite-type blowup charts. -/
theorem nu_isFinite [IsNoetherianRing A] (hd : ringKrullDim A ≤ 2)
    (hA : IsNagataRing.{u, 0} A) : IsFinite (nu A J hJ) := by
  apply Scheme.genericNormalization_isFinite (source A J hJ)
  intro U hne
  let := hne
  exact (actualChart_nagata_and_dimension (map A J hJ) hA hd (map_fieldMap_isIso A J hJ)
    U.1 U.2).1

/-- The normalized blowdown is proper by actual finite normalization and ordinary properness. -/
theorem a_isProper [IsNoetherianRing A] (hd : ringKrullDim A ≤ 2)
    (hA : IsNagataRing.{u, 0} A) : IsProper (a A J hJ) := by
  let : IsFinite (nu A J hJ) := nu_isFinite A J hJ hd hA
  exact inferInstanceAs (IsProper (nu A J hJ ≫ map A J hJ))

/-- Birationality retains the function-field map of the literal composite. -/
theorem a_fieldMap_isIso :
    IsIso (CommRingCat.ofHom (Scheme.functionFieldMap (a A J hJ))) := by
  let : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap (map A J hJ))) :=
    map_fieldMap_isIso A J hJ
  let : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap (nu A J hJ))) :=
    Scheme.genericNormalization_fieldMap_isIso (source A J hJ)
  change IsIso (CommRingCat.ofHom (Scheme.functionFieldMap (nu A J hJ ≫ map A J hJ)))
  rw [Scheme.functionFieldMap_comp]
  change IsIso (CommRingCat.ofHom (Scheme.functionFieldMap (map A J hJ)) ≫
    CommRingCat.ofHom (Scheme.functionFieldMap (nu A J hJ)))
  infer_instance

/-- Local Noetherianity is derived from the finite normalization morphism. -/
theorem normalization_isLocallyNoetherian [IsNoetherianRing A] (hd : ringKrullDim A ≤ 2)
    (hA : IsNagataRing.{u, 0} A) : IsLocallyNoetherian (normalization A J hJ) := by
  let : IsProper (a A J hJ) := a_isProper A J hJ hd hA
  exact LocallyOfFiniteType.isLocallyNoetherian (a A J hJ)

/-- The original ideal on the ordinary blowup. -/
def ordinaryIdeal : (source A J hJ).IdealSheafData := (affineCenter A J).comap (map A J hJ)

/-- The actual image ideal on the generic normalization. -/
def imageIdeal : (normalization A J hJ).IdealSheafData := (ordinaryIdeal A J hJ).comap (nu A J hJ)

/-- This image ideal is the original J-image along the literal composite. -/
theorem imageIdeal_eq : imageIdeal A J hJ = (affineCenter A J).comap (a A J hJ) :=
  (Scheme.IdealSheafData.comap_comp _ (nu A J hJ) (map A J hJ)).symm

/-- The ordinary image ideal still misses the actual generic point. -/
theorem ordinaryIdeal_generic_avoidance :
    genericPoint (source A J hJ) ∉ ((ordinaryIdeal A J hJ).support : Set (source A J hJ)) := by
  rw [ordinaryIdeal, Scheme.IdealSheafData.support_comap]
  change map A J hJ (genericPoint (source A J hJ)) ∉ (affineCenter A J).support
  rw [Scheme.map_genericPoint_of_isDominant]
  exact generic_avoids_centre A J hJ

/-- The normalized image ideal still misses the actual generic point. -/
theorem imageIdeal_generic_avoidance :
    genericPoint (normalization A J hJ) ∉
      ((imageIdeal A J hJ).support : Set (normalization A J hJ)) := by
  rw [imageIdeal, Scheme.IdealSheafData.support_comap]
  change nu A J hJ (genericPoint (normalization A J hJ)) ∉ (ordinaryIdeal A J hJ).support
  rw [Scheme.map_genericPoint_of_isDominant]
  exact ordinaryIdeal_generic_avoidance A J hJ

/-- The actual J-image ideal on X is invertible after the nonflat normalization. -/
theorem imageIdeal_isLocallyRankOne :
    IsLocallyRankOne (normalization A J hJ) (Hom.idealModule (imageIdeal A J hJ).subschemeι) :=
  NormalizedBlowupCover.imageIdeal_isLocallyRankOne (ordinaryIdeal A J hJ) (nu A J hJ)
    (ordinaryIdeal_generic_avoidance A J hJ) (datum A J).cartier

/-- Nonzero regular frames generate the actual image of J on X. -/
theorem imageIdeal_nonzero_localFrame (x : normalization A J hJ) :
    ∃ U : (normalization A J hJ).Opens, IsAffineOpen U ∧ x ∈ U ∧
      ∃ t : Γ(normalization A J hJ, U), t ≠ 0 ∧ IsSMulRegular Γ(normalization A J hJ, U) t ∧
        RingHom.ker ((imageIdeal A J hJ).subschemeι.app U).hom = Ideal.span {t} :=
  NormalizedBlowupCover.imageIdeal_nonzero_localFrame (ordinaryIdeal A J hJ) (nu A J hJ)
    (ordinaryIdeal_generic_avoidance A J hJ) (datum A J).cartier x

end Base

end AlgebraicGeometry.Scheme.Birational.NormalizedBlowupCover
