/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Resolution.ExtensionGraph
public import Aglib.AlgebraicGeometry.Normalization.FunctionField
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Ext.OpenKernel
public import Aglib.AlgebraicGeometry.Cohomology.Proper.FiniteLength
public import Aglib.AlgebraicGeometry.SchemeTheoreticImage.IntegralOpen
public import Aglib.RingTheory.Nagata.FiniteTypeSurface
public import Aglib.RingTheory.Nagata.CompleteLocalSurface
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.Algebraic.Basic

/-!
# The actual complementary graph and punctured H1 injectivity

The graph is the literal schematic image of the original complementary
section on the inverse image of the punctured spectrum. Its original
field triangle supplies injective, finite-type and algebraic affine chart
maps. Native dimension-two Nagata stability makes those actual charts
Nagata, so normalization of the original generic inclusion is finite.
The original normal graph then splits the extension.

The native restriction-kernel representative supplies that extension and
its actual punctured retraction. This proves injectivity of the original
structural H1 restriction over a normal Nagata local surface. Completeness
supplies the base Nagata property for the complete-base corollary.

This is the construction step following the conditional graph argument in
Stacks Project, Lemma 54.7.5, tag 0AXB. It does not construct a surface
resolution or supply the later residue-field derived Hom comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules

local instance graphNonemptyTop (Y : Scheme) [IsIntegral Y] :
    Nonempty (⊤ : Y.Opens) :=
  ⟨⟨genericPoint Y, trivial⟩⟩

namespace AlgebraicGeometry.Scheme.ProjectiveBundle.RankTwoExtension

universe u

variable {X : Scheme.{u}} {E : X.Modules}
  (i : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ E)
  (g : E ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
  (hig : i ≫ g = 0)
  (hS : (extensionComplex i g hig).ShortExact)
  (V : X.Opens)
  (rV : E.over V ⟶ (SheafOfModules.unit X.ringCatSheaf).over V)
  (hrV : (SheafOfModules.overFunctor X.ringCatSheaf V).map i ≫ rV = 𝟙 _)

local notation "π" => projection i g hig hS
local notation "τ" =>
  complementarySection i g hig hS rV hrV ≫
    Scheme.Opens.ι (quotientComplement i g hig hS)
local notation "p" => Scheme.Hom.imageι τ ≫ π

/-- The actual graph projection has the original open immersion as its
composite with the original image factor. -/
private theorem complementaryGraph_toImage_projection : (τ).toImage ≫ p = V.ι := by
  rw [← Category.assoc, Scheme.Hom.toImage_imageι]
  simpa only [Category.assoc, complementProjection] using
    complementarySection_projection i g hig hS rV hrV

/-- This is the actual schematic image, not a replacement graph model. -/
private theorem complementaryGraph_isIntegral [IsIntegral V.toScheme] [QuasiCompact τ] :
    IsIntegral (τ).image :=
  Scheme.schemeImage_isIntegral τ

/-- The original image inclusion followed by the original projective
projection is proper, before any normalization is supplied. -/
private theorem complementaryGraph_projection_isProper : IsProper p := by infer_instance

/-- Dominance follows from the original open-immersion triangle. -/
private theorem complementaryGraph_projection_isDominant
    [IsIntegral X] [IsIntegral V.toScheme] :
    IsDominant p := by
  let : IsDominant ((τ).toImage ≫ p) := by
    rw [complementaryGraph_toImage_projection i g hig hS V rV hrV]
    exact Scheme.isDominant_of_isOpenImmersion V.ι
  exact IsDominant.of_comp (τ).toImage p

/-- The original graph projection is birational. Both field maps in the
original image factorization are injections; surjectivity of their
composite is the original open-immersion field isomorphism. -/
private theorem complementaryGraph_fieldMap_isIso
    [IsIntegral X] [IsIntegral V.toScheme] [QuasiCompact τ] :
    letI := complementaryGraph_isIntegral i g hig hS V rV hrV
    letI := complementaryGraph_projection_isDominant i g hig hS V rV hrV
    IsIso (CommRingCat.ofHom (Scheme.functionFieldMap p)) := by
  let := complementaryGraph_isIntegral i g hig hS V rV hrV
  let := complementaryGraph_projection_isDominant i g hig hS V rV hrV
  let : IsOpenImmersion ((τ).toImage ≫ p) := by
    rw [complementaryGraph_toImage_projection i g hig hS V rV hrV]
    infer_instance
  let : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap ((τ).toImage ≫ p))) :=
    Scheme.FunctionField.fieldMap_isIso ((τ).toImage ≫ p)
  have hmap : (Scheme.functionFieldMap (τ).toImage).comp
      (Scheme.functionFieldMap p) = Scheme.functionFieldMap ((τ).toImage ≫ p) :=
    (Scheme.functionFieldMap_comp (τ).toImage p).symm
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  refine ⟨(Scheme.functionFieldMap p).injective, ?_⟩
  intro y
  obtain ⟨x, hx⟩ := (ConcreteCategory.bijective_of_isIso
    (CommRingCat.ofHom (Scheme.functionFieldMap ((τ).toImage ≫ p)))).2
      (Scheme.functionFieldMap (τ).toImage y)
  refine ⟨x, (Scheme.functionFieldMap (τ).toImage).injective ?_⟩
  change ((Scheme.functionFieldMap (τ).toImage).comp (Scheme.functionFieldMap p)) x = _
  exact (RingHom.congr_fun hmap x).trans hx

end AlgebraicGeometry.Scheme.ProjectiveBundle.RankTwoExtension

namespace AlgebraicGeometry.Scheme.ProjectiveBundle.RankTwoExtension

universe u

variable {A : CommRingCat.{u}} {W : Scheme.{u}}
  (q : W ⟶ Spec A)

/-- The literal structural scalar map on a displayed actual affine chart. -/
private def graphChartScalar (U : W.Opens) : A →+* Γ(W, U) :=
  (q.appLE ⊤ U le_top).hom.comp
    (Scheme.ΓSpecIso A).inv.hom

/-- Finite type is for this original map, obtained by the original affine
section map and the original spectrum-section isomorphism. -/
private theorem graphChartScalar_finiteType [LocallyOfFiniteType q]
    (U : W.Opens) (hU : IsAffineOpen U) : (graphChartScalar q U).FiniteType := by
  exact (q.finiteType_appLE (isAffineOpen_top _) hU le_top).comp
      (RingHom.FiniteType.of_surjective (Scheme.ΓSpecIso A).inv.hom
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso A).inv).2)

/-- A nonempty graph chart has the original injective base map, using
dominance and restriction in the actual integral source. -/
private theorem graphChartScalar_injective
    [IsDomain A] [IsIntegral W] [IsDominant q] [QuasiCompact q]
    (U : W.Opens) [Nonempty U] : Function.Injective (graphChartScalar q U) := by
  let : IsSchemeTheoreticallyDominant q := IsSchemeTheoreticallyDominant.of_isDominant q
  exact (AlgebraicGeometry.map_injective_of_isIntegral W (homOfLE (le_top : U ≤ ⊤))).comp
    ((q.app_injective ⊤).comp
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso A).inv).1)

/-- This commutative square fixes the structural actions used by GF2:
the chart embedding into the original function field and the actual
function-field map of q agree on the original A. -/
private theorem graphChartScalar_germ [IsDomain A] [IsIntegral W] [IsDominant q]
    (U : W.Opens) [Nonempty U] :
    CommRingCat.ofHom (graphChartScalar q U) ≫ W.germToFunctionField U =
      (Scheme.ΓSpecIso A).inv ≫
        (Spec A).germToFunctionField ⊤ ≫
          CommRingCat.ofHom (Scheme.functionFieldMap q) := by
  have hg : genericPoint W ∈ U :=
    ((genericPoint_spec W).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  have hres : W.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫
      W.germToFunctionField U = W.germToFunctionField ⊤ :=
    W.presheaf.germ_res (homOfLE (le_top : U ≤ ⊤)) (genericPoint W) hg
  rw [Scheme.functionFieldMap_germ]
  change (Scheme.ΓSpecIso A).inv ≫ q.appTop ≫
      W.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ W.germToFunctionField U =
    (Scheme.ΓSpecIso A).inv ≫ q.appTop ≫ W.germToFunctionField ⊤
  rw [hres]

end AlgebraicGeometry.Scheme.ProjectiveBundle.RankTwoExtension

namespace AlgebraicGeometry.Scheme.ProjectiveBundle.RankTwoExtension

universe u

/-- Equality of actual dominant arrows gives equality of their original field maps.
Substitution also transports the dominance proof. -/
private theorem graphFieldMap_congr {Y T : Scheme.{u}} [IsIntegral Y] [IsIntegral T]
    {a b : Y ⟶ T} [IsDominant a] [IsDominant b] (hab : a = b) :
    Scheme.functionFieldMap a = Scheme.functionFieldMap b := by
  subst b
  rfl

/-- A surjective concrete normalization of the actual image retains a
point of the original complementary section and hence avoids the divisor
at some point. -/
private theorem graphMap_not_range_subset
    {V P₀ N₀ D : Scheme.{u}} [Nonempty V]
    (τ : V ⟶ P₀)
    (ν : N₀ ⟶ τ.image) [Surjective ν] (σ₀ : D ⟶ P₀)
    (hdisjoint : Disjoint (Set.range τ) (Set.range σ₀)) :
    ¬ Set.range (ν ≫ τ.imageι) ⊆ Set.range σ₀ := by
  intro hsub
  obtain ⟨v⟩ := (inferInstance : Nonempty V)
  obtain ⟨n, hn⟩ := ν.surjective (τ.toImage v)
  have he : (ν ≫ τ.imageι) n = τ v := by
    change τ.imageι (ν n) = τ v
    rw [hn]
    have hfac := congrArg (fun k : V ⟶ P₀ => k v) (Scheme.Hom.toImage_imageι τ)
    exact hfac
  have hmem := hsub (show (ν ≫ τ.imageι) n ∈ Set.range (ν ≫ τ.imageι) from ⟨n, rfl⟩)
  rw [he] at hmem
  exact Set.disjoint_left.mp hdisjoint ⟨v, rfl⟩ hmem

/-- The actual graph closure adds no points over an open on which the
original range is closed. Only topological closure on this open is used. -/
private theorem imageRange_mem_of_closed_on_open
    {V P₀ : Scheme.{u}} (τ : V ⟶ P₀) [QuasiCompact τ]
    (U : P₀.Opens) (hclosed : IsClosed (U.ι ⁻¹' Set.range τ))
    (w : τ.image) (hw : τ.imageι w ∈ U) :
    τ.imageι w ∈ Set.range τ := by
  let y : U := ⟨τ.imageι w, hw⟩
  have hy : y ∈ U.ι ⁻¹' closure (Set.range τ) := by
    change τ.imageι w ∈ closure (Set.range τ)
    rw [← Scheme.Hom.Image.inclusion_range τ]
    exact ⟨w, rfl⟩
  rw [U.ι.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
    U.ι.continuous _, hclosed.closure_eq] at hy
  exact hy

/-- The original section on an open factors through the actual inverse-image
open of its ambient projection. -/
private def sectionOverOpenFactor
    {P₀ Y : Scheme.{u}} (π : P₀ ⟶ Y) (U : Y.Opens)
    (τ : U.toScheme ⟶ P₀) (hτ : τ ≫ π = U.ι) :
    U.toScheme ⟶ (π ⁻¹ᵁ U).toScheme :=
  IsOpenImmersion.lift (π ⁻¹ᵁ U).ι τ (by
    rintro _ ⟨u, rfl⟩
    rw [Scheme.Opens.range_ι]
    change π (τ u) ∈ U
    have hu := congrArg (fun k : U.toScheme ⟶ Y => k u) hτ
    change π (τ u) = U.ι u at hu
    rw [hu]
    exact u.property)

private theorem sectionOverOpenFactor_ι
    {P₀ Y : Scheme.{u}} (π : P₀ ⟶ Y) (U : Y.Opens)
    (τ : U.toScheme ⟶ P₀) (hτ : τ ≫ π = U.ι) :
    sectionOverOpenFactor π U τ hτ ≫ (π ⁻¹ᵁ U).ι = τ :=
  IsOpenImmersion.lift_fac _ _ _

private theorem sectionOverOpenFactor_projection
    {P₀ Y : Scheme.{u}} (π : P₀ ⟶ Y) (U : Y.Opens)
    (τ : U.toScheme ⟶ P₀) (hτ : τ ≫ π = U.ι) :
    sectionOverOpenFactor π U τ hτ ≫ (π ∣_ U) = 𝟙 U.toScheme := by
  apply (cancel_mono U.ι).mp
  rw [Category.assoc, morphismRestrict_ι, ← Category.assoc,
    sectionOverOpenFactor_ι, hτ, Category.id_comp]

private theorem sectionOverOpenFactor_isClosedImmersion
    {P₀ Y : Scheme.{u}} (π : P₀ ⟶ Y) [IsSeparated π] (U : Y.Opens)
    (τ : U.toScheme ⟶ P₀) (hτ : τ ≫ π = U.ι) :
    IsClosedImmersion (sectionOverOpenFactor π U τ hτ) := by
  let : IsClosedImmersion (sectionOverOpenFactor π U τ hτ ≫ (π ∣_ U)) := by
    rw [sectionOverOpenFactor_projection]
    infer_instance
  exact IsClosedImmersion.of_comp (sectionOverOpenFactor π U τ hτ) (π ∣_ U)

/-- A closed factor through the actual open gives precisely the closed
restricted range needed in the graph-closure argument. -/
private theorem closed_preimage_range_of_closed_open_factor
    {V P₀ : Scheme.{u}} (U : P₀.Opens) (τ : V ⟶ P₀)
    (τU : V ⟶ U.toScheme) [IsClosedImmersion τU]
    (hτ : τU ≫ U.ι = τ) : IsClosed (U.ι ⁻¹' Set.range τ) := by
  have he : U.ι ⁻¹' Set.range τ = Set.range τU := by
    ext y
    constructor
    · rintro ⟨v, hv⟩
      refine ⟨v, U.ι.isOpenEmbedding.injective ?_⟩
      simpa only [← Scheme.Hom.comp_apply, hτ] using hv
    · rintro ⟨v, rfl⟩
      exact ⟨v, (congrArg (fun k : V ⟶ P₀ => k v) hτ).symm⟩
  rw [he]
  exact τU.isClosedEmbedding.isClosed_range

/-- Closedness of the original complementary section over its original
open follows from separatedness of the ambient projection. -/
private theorem closed_preimage_range_of_open_section
    {P₀ Y : Scheme.{u}} (π : P₀ ⟶ Y) [IsSeparated π] (U : Y.Opens)
    (τ : U.toScheme ⟶ P₀) (hτ : τ ≫ π = U.ι) :
    IsClosed ((π ⁻¹ᵁ U).ι ⁻¹' Set.range τ) := by
  let : IsClosedImmersion (sectionOverOpenFactor π U τ hτ) :=
    sectionOverOpenFactor_isClosedImmersion π U τ hτ
  exact closed_preimage_range_of_closed_open_factor (π ⁻¹ᵁ U) τ
    (sectionOverOpenFactor π U τ hτ) (sectionOverOpenFactor_ι π U τ hτ)

/-- On the actual pullback intersection, every point lies outside the
open where the complementary section is closed. No base-change identity
for the scheme-theoretic image is assumed. -/
private theorem graphIntersection_not_mem_open
    {V P₀ N₀ D Y : Scheme.{u}}
    (τ : V ⟶ P₀) [QuasiCompact τ] (ν : N₀ ⟶ τ.image)
    (σ₀ : D ⟶ P₀) (π : P₀ ⟶ Y) (U : Y.Opens)
    (hclosed : IsClosed ((π ⁻¹ᵁ U).ι ⁻¹' Set.range τ))
    (hdisjoint : Disjoint (Set.range τ) (Set.range σ₀))
    (z : Limits.pullback (C := Scheme.{u}) σ₀ (ν ≫ τ.imageι)) :
    π ((ν ≫ τ.imageι) (Limits.pullback.snd σ₀ (ν ≫ τ.imageι) z)) ∉ U := by
  intro hz
  let n := Limits.pullback.snd σ₀ (ν ≫ τ.imageι) z
  have hτ : (ν ≫ τ.imageι) n ∈ Set.range τ :=
    imageRange_mem_of_closed_on_open τ (π ⁻¹ᵁ U) hclosed (ν n) hz
  have hσ : (ν ≫ τ.imageι) n ∈ Set.range σ₀ := by
    refine ⟨Limits.pullback.fst σ₀ (ν ≫ τ.imageι) z, ?_⟩
    exact congrArg (fun k : Limits.pullback (C := Scheme.{u}) σ₀ (ν ≫ τ.imageι) ⟶ P₀ => k z)
      (Limits.pullback.condition (f := σ₀) (g := ν ≫ τ.imageι))
  exact Set.disjoint_left.mp hdisjoint hτ hσ

end AlgebraicGeometry.Scheme.ProjectiveBundle.RankTwoExtension

namespace AlgebraicGeometry.Scheme.ProjectiveBundle.RankTwoExtension

universe u

variable {A : CommRingCat.{u}} [IsDomain A]
  {W : Scheme.{u}} [IsIntegral W]
  (q : W ⟶ Spec A) [IsDominant q]

/-- Evaluating the original germ square gives exactly the native base-field action. -/
private theorem graphChartScalar_germ_apply (U : W.Opens) [Nonempty U] (a : A) :
    W.germToFunctionField U (graphChartScalar q U a) =
      Scheme.functionFieldMap q (algebraMap A (Spec A).functionField a) := by
  have h := congrArg (fun k : A ⟶ W.functionField => k a)
    (graphChartScalar_germ q U)
  exact h

/-- Each element of a literal graph chart satisfies the nonzero linear
polynomial sX-a from the original birational generic field map. -/
private theorem graphChartScalar_isAlgebraic
    (hff : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap q)))
    (U : W.Opens) [Nonempty U] :
    letI := (graphChartScalar q U).toAlgebra
    Algebra.IsAlgebraic A Γ(W, U) := by
  let := (graphChartScalar q U).toAlgebra
  let := hff
  refine ⟨fun b => ?_⟩
  obtain ⟨z, hz⟩ := (ConcreteCategory.bijective_of_isIso
    (CommRingCat.ofHom (Scheme.functionFieldMap q))).2 (W.germToFunctionField U b)
  obtain ⟨a, s, hs, has⟩ := IsFractionRing.div_surjective A z
  have hs0 : s ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hs
  have hsF : Scheme.functionFieldMap q
      (algebraMap A (Spec A).functionField s) ≠ 0 := by
    apply (map_ne_zero (Scheme.functionFieldMap q)).mpr
    exact (map_ne_zero_iff _
      (IsFractionRing.injective A (Spec A).functionField)).mpr hs0
  have hrat : Scheme.functionFieldMap q
        (algebraMap A (Spec A).functionField a) /
      Scheme.functionFieldMap q (algebraMap A (Spec A).functionField s) =
        W.germToFunctionField U b := by
    rw [← map_div₀, has]
    exact hz
  have hrel : graphChartScalar q U s * b = graphChartScalar q U a := by
    apply W.germToFunctionField_injective U
    rw [map_mul, graphChartScalar_germ_apply, graphChartScalar_germ_apply]
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

end AlgebraicGeometry.Scheme.ProjectiveBundle.RankTwoExtension

namespace AlgebraicGeometry.Scheme.ProjectiveBundle.RankTwoExtension

universe u

private theorem puncturedPreimage_nonempty
    {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A]
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of A)) [IsDominant f] (hdim : ringKrullDim A = 2) :
    Nonempty (f ⁻¹ᵁ Scheme.localPuncturedSpectrum A) := by
  refine ⟨⟨genericPoint X, ?_⟩⟩
  change f (genericPoint X) ≠ IsLocalRing.closedPoint A
  rw [Scheme.map_genericPoint_of_isDominant X f, genericPoint_eq_bot_of_affine]
  intro he
  have hm : IsLocalRing.maximalIdeal A = ⊥ :=
    congrArg PrimeSpectrum.asIdeal he.symm
  have hzero := ringKrullDim_eq_zero_of_isField
    (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hm)
  rw [hdim] at hzero
  norm_num at hzero

/-- An actual punctured retraction splits the original extension over a
normal Nagata local surface. All affine chart Nagata conditions and the
finite original normalization are constructed in the proof. -/
public theorem splitting_of_punctured_complementary_section
    {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [IsIntegrallyClosed A]
    {X : Scheme.{u}} [IsIntegral X] {E : X.Modules}
    (i : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ E)
    (g : E ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (hig : i ≫ g = 0) (hS : (extensionComplex i g hig).ShortExact)
    (f : X ⟶ Spec (.of A)) [IsProper f] [IsDominant f]
    (hff : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f)))
    (hdim : ringKrullDim A = 2) (hX : Scheme.NormalStalks X)
    (hA : IsNagataRing.{u, 0} A)
    (rV : E.over (f ⁻¹ᵁ Scheme.localPuncturedSpectrum A) ⟶
      (SheafOfModules.unit X.ringCatSheaf).over (f ⁻¹ᵁ Scheme.localPuncturedSpectrum A))
    (hrV : (SheafOfModules.overFunctor X.ringCatSheaf
      (f ⁻¹ᵁ Scheme.localPuncturedSpectrum A)).map i ≫ rV = 𝟙 _) :
    Nonempty ((extensionComplex i g hig).Splitting) := by
  let V := f ⁻¹ᵁ Scheme.localPuncturedSpectrum A
  let : Nonempty V := puncturedPreimage_nonempty f hdim
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : IsNoetherian X := ⟨⟩
  let : NoetherianSpace X := inferInstance
  let : NoetherianSpace V.toScheme := NoetherianSpace.set (V : Set X)
  let tau := complementarySection i g hig hS rV hrV ≫
    (quotientComplement i g hig hS).ι
  let : QuasiCompact tau := quasiCompact_of_noetherianSpace_source tau
  let W := tau.image
  let : IsIntegral W := complementaryGraph_isIntegral i g hig hS V rV hrV
  let pi := projection i g hig hS
  let p := tau.imageι ≫ pi
  let : IsProper p := complementaryGraph_projection_isProper i g hig hS V rV hrV
  let : IsDominant p := complementaryGraph_projection_isDominant i g hig hS V rV hrV
  let : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap p)) :=
    complementaryGraph_fieldMap_isIso i g hig hS V rV hrV
  let := hff
  have hffq : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap (p ≫ f))) := by
    rw [Scheme.functionFieldMap_comp]
    change IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f) ≫
      CommRingCat.ofHom (Scheme.functionFieldMap p))
    infer_instance
  have hNagata : ∀ U : W.affineOpens,
      Nonempty U.1 → IsNagataRing.{u, 0} Γ(W, U.1) := by
    intro U hne
    let := hne
    let := (graphChartScalar (p ≫ f) U.1).toAlgebra
    let : Algebra.FiniteType A Γ(W, U.1) :=
      graphChartScalar_finiteType (p ≫ f) U.1 U.2
    let : Algebra.IsAlgebraic A Γ(W, U.1) :=
      graphChartScalar_isAlgebraic (p ≫ f) hffq U.1
    exact hA.of_finiteType_isAlgebraic_of_dimLE_two hdim.le
      (graphChartScalar_injective (p ≫ f) U.1)
  let gamma := W.fromSpecStalk (genericPoint W)
  let nu := gamma.fromNormalization
  let : IsFinite nu := Scheme.genericNormalization_isFinite W hNagata
  let : IsDominant nu := Scheme.genericNormalization_isDominant W
  let : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap nu)) :=
    Scheme.genericNormalization_fieldMap_isIso W
  let h := nu ≫ tau.imageι
  let : IsFinite h := inferInstance
  let : IsDominant (h ≫ pi) := by
    dsimp only [h]
    rw [Category.assoc]
    infer_instance
  have hmap : Scheme.functionFieldMap (h ≫ pi) =
      Scheme.functionFieldMap (nu ≫ p) :=
    graphFieldMap_congr (Category.assoc nu tau.imageι pi)
  have hffh : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap (h ≫ pi))) := by
    rw [hmap, Scheme.functionFieldMap_comp]
    change IsIso (CommRingCat.ofHom (Scheme.functionFieldMap p) ≫
      CommRingCat.ofHom (Scheme.functionFieldMap nu))
    infer_instance
  have hdisjoint : Disjoint (Set.range tau) (Set.range (quotientSection i g hig hS)) :=
    complementarySection_disjoint i g hig hS rV hrV
  have havoid : ¬ Set.range h ⊆ Set.range (quotientSection i g hig hS) :=
    graphMap_not_range_subset tau nu (quotientSection i g hig hS) hdisjoint
  have htriangle : tau ≫ pi = V.ι := by
    simpa only [tau, pi, Category.assoc, complementProjection] using
      complementarySection_projection i g hig hS rV hrV
  have hclosed : IsClosed ((pi ⁻¹ᵁ V).ι ⁻¹' Set.range tau) :=
    closed_preimage_range_of_open_section pi V tau htriangle
  have hvertical : ∀ z : Limits.pullback (C := Scheme.{u}) (quotientSection i g hig hS) h,
      ((h ≫ pi) ≫ f) (Limits.pullback.snd (quotientSection i g hig hS) h z) =
        IsLocalRing.closedPoint A := by
    intro z
    have hz := graphIntersection_not_mem_open
      tau nu (quotientSection i g hig hS) pi V hclosed hdisjoint z
    change ¬ f (pi (h (Limits.pullback.snd (quotientSection i g hig hS) h z))) ≠
      IsLocalRing.closedPoint A at hz
    change f (pi (h (Limits.pullback.snd (quotientSection i g hig hS) h z))) =
      IsLocalRing.closedPoint A
    exact Classical.not_not.mp hz
  exact splitting_of_finite_normal_graph i g hig hS f hff hdim hX
    (Scheme.genericNormalization_normalStalks W) h hffh havoid hvertical

end AlgebraicGeometry.Scheme.ProjectiveBundle.RankTwoExtension

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

/-- The original structural H1 restriction to the punctured inverse image is
injective over a normal Nagata local surface. -/
public theorem structureH1_puncturedRestriction_injective_of_isNagata
    {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [IsIntegrallyClosed A]
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of A)) [IsProper f] [IsDominant f]
    (hff : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f)))
    (hdim : ringKrullDim A = 2) (hX : Scheme.NormalStalks X)
    (hA : IsNagataRing.{u, 0} A) :
    Function.Injective (moduleCohomologyMapAlong
      (f ⁻¹ᵁ Scheme.localPuncturedSpectrum A).ι
      (Scheme.Hom.structureModuleMap (f ⁻¹ᵁ Scheme.localPuncturedSpectrum A).ι) 1) := by
  let OX : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let comparison : CategoryTheory.Abelian.Ext.{u + 1} (C := X.Modules) OX OX 1 →+
      Sheaf.H.{u + 1} (moduleAddSheaf X OX) 1 :=
    moduleExtCohomologyMap X OX 1
  let V := f ⁻¹ᵁ Scheme.localPuncturedSpectrum A
  intro a b hab
  have hz : moduleCohomologyMapAlong V.ι (Scheme.Hom.structureModuleMap V.ι) 1 (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  obtain ⟨E, hEc, rV, hrV⟩ :=
    exists_extension_retraction_of_structureRestriction_eq_zero X V (a - b) hz
  obtain ⟨s⟩ := ProjectiveBundle.RankTwoExtension.splitting_of_punctured_complementary_section
    E.i E.p E.zero E.shortExact f hff hdim hX hA rV hrV
  have hclass : (E.extClass :
      CategoryTheory.Abelian.Ext.{u + 1} (C := X.Modules) OX OX 1) = 0 :=
    (ShortComplex.ShortExact.extClass_eq_zero_iff_splitting E.shortExact).mpr ⟨s⟩
  apply sub_eq_zero.mp
  calc
    a - b = comparison E.extClass := hEc.symm
    _ = 0 := (congrArg comparison hclass).trans comparison.map_zero

/-- Completeness of the original normal local surface supplies its Nagata
property and gives injectivity of the actual punctured H1 restriction. -/
public theorem structureH1_puncturedRestriction_injective
    {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [IsIntegrallyClosed A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of A)) [IsProper f] [IsDominant f]
    (hff : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f)))
    (hdim : ringKrullDim A = 2) (hX : Scheme.NormalStalks X) :
    Function.Injective (moduleCohomologyMapAlong
      (f ⁻¹ᵁ Scheme.localPuncturedSpectrum A).ι
      (Scheme.Hom.structureModuleMap (f ⁻¹ᵁ Scheme.localPuncturedSpectrum A).ι) 1) := by
  let : Ring.KrullDimLE 2 A := Ring.krullDimLE_iff.mpr hdim.le
  exact structureH1_puncturedRestriction_injective_of_isNagata f hff hdim hX
    (IsNagataRing.of_complete_local_dimLE_two A)

end AlgebraicGeometry.Scheme.Cohomology
