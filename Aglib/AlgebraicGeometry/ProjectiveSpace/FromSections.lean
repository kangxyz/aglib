/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Gluing.Frames
public import Aglib.AlgebraicGeometry.Modules.Invertible.Gluing.Pullback
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Hom
public import Aglib.AlgebraicGeometry.ProjectiveSpace.FiniteEmbedding.Map
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Aglib.Algebra.Category.ModuleCat.Sheaf.Free.Sections
public import Aglib.Algebra.Category.ModuleCat.Sheaf.Epimorphisms

/-!
# Projective morphisms defined by original line-module sections

An actual covering by frames given by members of an original global-section family
produces normalized coefficients, compatible native projective chart maps and an
actual morphism over the original base. The coordinate-open preimages are the
nonvanishing opens of the original sections, computed in the supplied frames.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory MvPolynomial Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveSpace.FromSections

variable {R : Type u} [CommRing R] {I : Type u} {X : Scheme.{u}}

/-- A cover by actual frames in which a specified original section is the generator.
The chart index may refine the original coordinate index. -/
structure SectionFrames (M : X.Modules) (s : I → M.sections) where
  /-- The index of the actual source cover. -/
  K : Type u
  /-- Original open subsets of the source scheme. -/
  U : K → X.Opens
  covers : iSup U = ⊤
  /-- The member of the original family used as the frame on each open. -/
  coordinate : K → I
  /-- Actual trivializations of the original module, on the original opens. -/
  frame : ∀ k, M.over (U k) ≅ SheafOfModules.unit (X.ringCatSheaf.over (U k))
  selected : ∀ k, LocalFrames.coefficient U M frame k le_rfl
    ((s (coordinate k)).val (op (U k))) = 1

namespace SectionFrames

variable {M : X.Modules} {s : I → M.sections} (F : SectionFrames M s)

/-- The original coefficient of a section on a subopen of an actual frame. -/
abbrev coefficientOn (k : F.K) {O : X.Opens} (hk : O ≤ F.U k) (j : I) : Γ(X, O) :=
  LocalFrames.coefficient F.U M F.frame k hk ((s j).val (op O))

theorem coefficientOn_restrict (k : F.K) {O V : X.Opens} (h : V ≤ O)
    (hk : O ≤ F.U k) (j : I) :
    sectionRestrict X h (F.coefficientOn k hk j) =
      F.coefficientOn k (h.trans hk) j := by
  simpa only [PresheafOfModules.sections_property] using
    (LocalFrames.coefficient_restrict F.U M F.frame k h hk ((s j).val (op O))).symm

@[simp]
theorem coefficientOn_selected (k : F.K) {O : X.Opens} (hk : O ≤ F.U k) :
    F.coefficientOn k hk (F.coordinate k) = 1 := by
  rw [← coefficientOn_restrict F k hk le_rfl]
  exact (congrArg (sectionRestrict X hk) (F.selected k)).trans (map_one _)

theorem selected_eq_generator (k : F.K) {O : X.Opens} (hk : O ≤ F.U k) :
    (s (F.coordinate k)).val (op O) = LocalFrames.generator F.U M F.frame k hk := by
  apply (LocalFrames.coefficient F.U M F.frame k hk).injective
  rw [LocalFrames.coefficient_generator]
  exact F.coefficientOn_selected k hk

theorem coefficientOn_transition (k l : F.K) {O : X.Opens}
    (hk : O ≤ F.U k) (hl : O ≤ F.U l) (j : I) :
    F.coefficientOn k hk j =
      F.coefficientOn k hk (F.coordinate l) * F.coefficientOn l hl j := by
  unfold coefficientOn
  rw [selected_eq_generator F l hl]
  exact LocalFrames.coefficient_transition F.U M F.frame k l hk hl ((s j).val (op O))

theorem coefficientOn_selected_isUnit (k l : F.K) {O : X.Opens}
    (hk : O ≤ F.U k) (hl : O ≤ F.U l) :
    IsUnit (F.coefficientOn k hk (F.coordinate l)) := by
  rw [coefficientOn, selected_eq_generator F l hl]
  exact (LocalFrames.transitionUnitOn F.U M F.frame k l hk hl).isUnit

/-- The nonvanishing open of the original section, written in the actual source frames. -/
def nonvanishingOpen (j : I) : X.Opens := ⨆ k, X.basicOpen (F.coefficientOn k le_rfl j)

variable (p : X ⟶ Spec (CommRingCat.of R))

/-- The original base map on an actual source open. -/
def baseCoefficient (O : X.Opens) : R →+* Γ(X, O) :=
  (sectionRestrict X le_top).comp
    (p.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)

@[simp]
theorem baseCoefficient_restrict {O V : X.Opens} (h : V ≤ O) (r : R) :
    sectionRestrict X h (baseCoefficient p O r) = baseCoefficient p V r := by
  simp only [baseCoefficient, RingHom.comp_apply, sectionRestrict_comp]

/-- Evaluation of the actual projective chart ring at the original normalized sections. -/
def chartRingHom (k : F.K) {O : X.Opens} (hk : O ≤ F.U k) :
    coordinateRing R I (F.coordinate k) →+* Γ(X, O) :=
  (eval₂Hom (baseCoefficient p O) (fun j => F.coefficientOn k hk j.1)).comp
    (coordinateRingToPolynomial R I (F.coordinate k))

@[simp]
theorem chartRingHom_coefficient (k : F.K) {O : X.Opens} (hk : O ≤ F.U k) (r : R) :
    F.chartRingHom p k hk (coordinateRingCoefficient R I (F.coordinate k) r) =
      baseCoefficient p O r := by
  simp [chartRingHom]

@[simp]
theorem chartRingHom_ratio (k : F.K) {O : X.Opens} (hk : O ≤ F.U k) (j : I) :
    F.chartRingHom p k hk (coordinateRatio R I (F.coordinate k) j) =
      F.coefficientOn k hk j := by
  classical
  by_cases hj : j = F.coordinate k
  · subst j
    simp
  · change (eval₂Hom _ _)
      (coordinateRingToPolynomial R I (F.coordinate k)
        (coordinateRatio R I (F.coordinate k)
          (⟨j, hj⟩ : {j : I // j ≠ F.coordinate k}).1)) = _
    rw [coordinateRingToPolynomial_ratio, eval₂Hom_X']

theorem chartRingHom_restrict (k : F.K) {O V : X.Opens} (h : V ≤ O)
    (hk : O ≤ F.U k) :
    (sectionRestrict X h).comp (F.chartRingHom p k hk) =
      F.chartRingHom p k (h.trans hk) := by
  unfold chartRingHom
  rw [← RingHom.comp_assoc]
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro r
    simp
  · intro j
    simp [coefficientOn_restrict]

/-- The actual local map to native projective space defined by the original sections. -/
def chartMap (k : F.K) {O : X.Opens} (hk : O ≤ F.U k) :
    O.toScheme ⟶ ProjectiveSpace R I :=
  O.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (F.chartRingHom p k hk)) ≫
    Proj.awayι (homogeneousSubmodule I R) (MvPolynomial.X (F.coordinate k))
      (isHomogeneous_X R (F.coordinate k)) Nat.zero_lt_one

theorem chartMap_restrict (k : F.K) {O V : X.Opens} (h : V ≤ O)
    (hk : O ≤ F.U k) :
    X.homOfLE h ≫ F.chartMap p k hk = F.chartMap p k (h.trans hk) := by
  rw [chartMap]
  simp only [← Category.assoc]
  rw [← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map]
  simp only [Category.assoc]
  rw [← Spec.map_comp_assoc]
  change V.toSpecΓ ≫ Spec.map
    (CommRingCat.ofHom ((sectionRestrict X h).comp (F.chartRingHom p k hk))) ≫ _ = _
  rw [chartRingHom_restrict]
  rfl

theorem chartMap_toSpec (k : F.K) {O : X.Opens} (hk : O ≤ F.U k) :
    F.chartMap p k hk ≫ toSpec R I = O.ι ≫ p := by
  have hc : CommRingCat.ofHom (coordinateRingCoefficient R I (F.coordinate k)) ≫
      CommRingCat.ofHom (F.chartRingHom p k hk) =
        CommRingCat.ofHom (baseCoefficient p O) := by
    ext r
    exact F.chartRingHom_coefficient p k hk r
  rw [chartMap, Category.assoc, Category.assoc, coordinateChart_toSpec, ← Spec.map_comp]
  change O.toSpecΓ ≫ Spec.map
    (CommRingCat.ofHom (coordinateRingCoefficient R I (F.coordinate k)) ≫
      CommRingCat.ofHom (F.chartRingHom p k hk)) = _
  rw [hc]
  change O.toSpecΓ ≫ Spec.map
    (((Scheme.ΓSpecIso (.of R)).inv ≫ p.appTop) ≫ X.presheaf.map (homOfLE le_top).op) = _
  rw [Spec.map_comp, Spec.map_comp]
  simp only [← Category.assoc]
  rw [Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top O]
  simp only [Category.assoc]
  rw [← Scheme.toSpecΓ_naturality_assoc p, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

theorem chartMap_preimage (k : F.K) {O : X.Opens} (hk : O ≤ F.U k) (j : I) :
    F.chartMap p k hk ⁻¹ᵁ coordinateOpen R I j =
      O.ι ⁻¹ᵁ X.basicOpen (F.coefficientOn k hk j) := by
  rw [chartMap, Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage,
    coordinateChart_preimage_coordinateOpen, SpecMap_preimage_basicOpen]
  change O.toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen
    (F.chartRingHom p k hk (coordinateRatio R I (F.coordinate k) j)) = _
  rw [chartRingHom_ratio, Scheme.Opens.toSpecΓ_preimage_basicOpen]

/-- The actual coefficients of the original sections force projective overlap compatibility. -/
theorem chartMaps_agree (k l : F.K) {O : X.Opens}
    (hk : O ≤ F.U k) (hl : O ≤ F.U l) :
    F.chartMap p k hk = F.chartMap p l hl := by
  unfold chartMap
  apply congrArg (fun q => O.toSpecΓ ≫ q)
  apply FiniteEmbedding.chart_maps_eq_of_rescaling
  · intro r
    rw [chartRingHom_coefficient, chartRingHom_coefficient]
  · rw [chartRingHom_ratio]
    exact F.coefficientOn_selected_isUnit k l hk hl
  · intro j
    rw [chartRingHom_ratio, chartRingHom_ratio, chartRingHom_ratio]
    exact F.coefficientOn_transition k l hk hl j

/-- The original open cover supplied by the chosen section frames. -/
abbrev sourceOpenCover : X.OpenCover :=
  X.openCoverOfIsOpenCover F.U (.mk F.covers)

theorem localMap_compatible (k l : F.K) :
    CategoryTheory.Limits.pullback.fst (F.U k).ι (F.U l).ι ≫ F.chartMap p k le_rfl =
      CategoryTheory.Limits.pullback.snd (F.U k).ι (F.U l).ι ≫ F.chartMap p l le_rfl := by
  let h := isPullback_opens_inf (F.U k) (F.U l)
  apply (cancel_epi h.isoPullback.hom).mp
  simp only [← Category.assoc]
  rw [h.isoPullback_hom_fst, h.isoPullback_hom_snd, chartMap_restrict, chartMap_restrict]
  exact F.chartMaps_agree p k l inf_le_left inf_le_right

/-- The actual native projective morphism supplied by the original section family. -/
def map : X ⟶ ProjectiveSpace R I :=
  F.sourceOpenCover.glueMorphisms (fun k => F.chartMap p k le_rfl)
    (F.localMap_compatible p)

@[reassoc (attr := simp)]
theorem ι_map (k : F.K) : (F.U k).ι ≫ F.map p = F.chartMap p k le_rfl :=
  F.sourceOpenCover.ι_glueMorphisms _ _ k

/-- The native projective morphism commutes with the original structural map. -/
@[reassoc]
theorem map_toSpec : F.map p ≫ toSpec R I = p := by
  apply F.sourceOpenCover.hom_ext
  intro k
  change (F.U k).ι ≫ F.map p ≫ toSpec R I = (F.U k).ι ≫ p
  rw [ι_map_assoc, chartMap_toSpec]

/-- The original section's nonvanishing open is the exact coordinate-open preimage. -/
theorem map_preimage_coordinateOpen (j : I) :
    F.map p ⁻¹ᵁ coordinateOpen R I j = F.nonvanishingOpen j := by
  ext x
  constructor
  · intro hx
    obtain ⟨k, hk⟩ := Opens.mem_iSup.mp
      (show x ∈ iSup F.U by rw [F.covers]; trivial)
    have h := congrArg
      (fun O : (F.U k).toScheme.Opens => (⟨x, hk⟩ : F.U k) ∈ O)
      ((congrArg (fun q => q ⁻¹ᵁ coordinateOpen R I j) (F.ι_map p k)).trans
        (F.chartMap_preimage p k le_rfl j))
    exact Opens.mem_iSup.mpr ⟨k, (eq_iff_iff.mp h).mp hx⟩
  · intro hx
    obtain ⟨k, hk⟩ := Opens.mem_iSup.mp hx
    have hxk : x ∈ F.U k := X.basicOpen_le _ hk
    have h := congrArg
      (fun O : (F.U k).toScheme.Opens => (⟨x, hxk⟩ : F.U k) ∈ O)
      ((congrArg (fun q => q ⁻¹ᵁ coordinateOpen R I j) (F.ι_map p k)).trans
        (F.chartMap_preimage p k le_rfl j))
    exact (eq_iff_iff.mp h).mpr hk

/-- On each original source chart, the coordinate-open preimage is exactly the
basic open of the original section coefficient. -/
theorem map_preimage_coordinateOpen_inf (k : F.K) (j : I) :
    F.U k ⊓ (F.map p ⁻¹ᵁ coordinateOpen R I j) =
      X.basicOpen (F.coefficientOn k le_rfl j) := by
  ext x
  by_cases hx : x ∈ F.U k
  · have h := congrArg
      (fun O : (F.U k).toScheme.Opens => (⟨x, hx⟩ : F.U k) ∈ O)
      ((congrArg (fun q => q ⁻¹ᵁ coordinateOpen R I j) (F.ι_map p k)).trans
        (F.chartMap_preimage p k le_rfl j))
    constructor
    · intro hh
      exact (eq_iff_iff.mp h).mp hh.2
    · intro hh
      exact ⟨hx, (eq_iff_iff.mp h).mpr hh⟩
  · constructor
    · exact fun hh => (hx hh.1).elim
    · exact fun hh => (hx (X.basicOpen_le _ hh)).elim

/-- The original selected section is nonvanishing throughout its actual frame chart. -/
theorem le_nonvanishingOpen (k : F.K) : F.U k ≤ F.nonvanishingOpen (F.coordinate k) := by
  intro x hx
  change x ∈ ⨆ l, X.basicOpen (F.coefficientOn l le_rfl (F.coordinate k))
  apply Opens.mem_iSup.mpr
  refine ⟨k, ?_⟩
  simpa only [coefficientOn_selected, Scheme.basicOpen_one] using hx

/-- The actual source frame chart maps into its selected original coordinate chart. -/
theorem le_map_preimage_selected (k : F.K) {O : X.Opens} (hk : O ≤ F.U k) :
    O ≤ F.map p ⁻¹ᵁ coordinateOpen R I (F.coordinate k) := by
  rw [F.map_preimage_coordinateOpen p]
  exact hk.trans (F.le_nonvanishingOpen k)

@[reassoc]
theorem ι_map_on (k : F.K) {O : X.Opens} (hk : O ≤ F.U k) :
    O.ι ≫ F.map p = F.chartMap p k hk := by
  calc
    _ = X.homOfLE hk ≫ (F.U k).ι ≫ F.map p := by
      rw [← Category.assoc, Scheme.homOfLE_ι]
    _ = X.homOfLE hk ≫ F.chartMap p k le_rfl := by rw [F.ι_map]
    _ = _ := F.chartMap_restrict p k hk le_rfl

/-- The actual pullback on the native chart ring is the original coefficient evaluation. -/
theorem map_chartRingHom (k : F.K) {O : X.Opens} (hk : O ≤ F.U k) :
    Proj.awayToSection (homogeneousSubmodule I R) (MvPolynomial.X (F.coordinate k)) ≫
        (F.map p).appLE (coordinateOpen R I (F.coordinate k)) O
          (F.le_map_preimage_selected p k hk) =
      CommRingCat.ofHom (F.chartRingHom p k hk) := by
  let W := coordinateOpen R I (F.coordinate k)
  let E := Proj.basicOpenIsoSpec (homogeneousSubmodule I R)
    (MvPolynomial.X (F.coordinate k)) (isHomogeneous_X R (F.coordinate k)) Nat.zero_lt_one
  have hr : (F.map p).resLE W O (F.le_map_preimage_selected p k hk) =
      O.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (F.chartRingHom p k hk)) ≫ E.inv := by
    apply (cancel_mono W.ι).mp
    rw [Scheme.Hom.resLE_comp_ι]
    simpa only [chartMap, Proj.awayι, Category.assoc, E, W, coordinateOpen]
      using F.ι_map_on p k hk
  have hr' := congrArg (fun q => q ≫ E.hom) hr
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at hr'
  have hh := congrArg (fun q => q.appTop) hr'
  apply (cancel_epi (Scheme.ΓSpecIso (CommRingCat.of (coordinateRing R I (F.coordinate k)))).hom).mp
  apply (cancel_mono O.topIso.inv).mp
  simpa only [Scheme.Hom.comp_appTop, Proj.basicOpenIsoSpec_hom,
    Proj.basicOpenToSpec_app_top, Scheme.Hom.resLE_app_top, Scheme.Opens.toSpecΓ_appTop,
    Category.assoc, Iso.inv_hom_id_assoc, Scheme.ΓSpecIso_naturality_assoc,
    E, W, coordinateOpen, coordinateRing] using hh

/-- Every native projective coordinate ratio pulls back to the coefficient of the
original global section in the displayed original frame. -/
theorem map_coordinateRatioSection (k : F.K) {O : X.Opens} (hk : O ≤ F.U k) (j : I) :
    ((F.map p).appLE (coordinateOpen R I (F.coordinate k)) O
      (F.le_map_preimage_selected p k hk)).hom
        (coordinateRatioSection R I (F.coordinate k) j) = F.coefficientOn k hk j := by
  change (Proj.awayToSection (homogeneousSubmodule I R) (MvPolynomial.X (F.coordinate k)) ≫
    (F.map p).appLE (coordinateOpen R I (F.coordinate k)) O
      (F.le_map_preimage_selected p k hk)).hom (coordinateRatio R I (F.coordinate k) j) = _
  rw [F.map_chartRingHom p k hk]
  exact F.chartRingHom_ratio p k hk j

end SectionFrames

/-- Multiplication by an actual original section of the structure sheaf on the over-site. -/
def unitScaleOn (U : X.Opens) (a : Γ(X, U)) :
    SheafOfModules.unit (X.ringCatSheaf.over U) ⟶
      SheafOfModules.unit (X.ringCatSheaf.over U) where
  val := {
    app := fun V => by
      change ModuleCat.of Γ(X, V.unop.left) Γ(X, V.unop.left) ⟶
        ModuleCat.of Γ(X, V.unop.left) Γ(X, V.unop.left)
      exact ModuleCat.ofHom {
        toFun := fun r => r * sectionRestrict X (leOfHom V.unop.hom) a
        map_add' := fun r t => add_mul r t _
        map_smul' := fun r t => by
          change (r * t) * _ = r * (t * _)
          exact mul_assoc _ _ _ }
    naturality := by
      intro V W f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro r
      change Γ(X, V.unop.left) at r
      change sectionRestrict X (leOfHom f.unop.left) r *
          sectionRestrict X (leOfHom W.unop.hom) a =
        sectionRestrict X (leOfHom f.unop.left)
          (r * sectionRestrict X (leOfHom V.unop.hom) a)
      rw [map_mul, sectionRestrict_comp] }

/-- An actual unit rescales the frame of the structure module on its original open. -/
def unitScaleOnIso (U : X.Opens) (a : Γ(X, U)ˣ) :
    SheafOfModules.unit (X.ringCatSheaf.over U) ≅
      SheafOfModules.unit (X.ringCatSheaf.over U) where
  hom := unitScaleOn U a
  inv := unitScaleOn U (↑a⁻¹)
  hom_inv_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change Γ(X, V.unop.left) at r
    change (r * sectionRestrict X (leOfHom V.unop.hom) a) *
      sectionRestrict X (leOfHom V.unop.hom) (↑a⁻¹) = r
    rw [mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]
  inv_hom_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change Γ(X, V.unop.left) at r
    change (r * sectionRestrict X (leOfHom V.unop.hom) (↑a⁻¹)) *
      sectionRestrict X (leOfHom V.unop.hom) a = r
    rw [mul_assoc, ← map_mul, Units.inv_mul, map_one, mul_one]

/-- Local finite generation of a line module makes one original coefficient a unit
at the specified point. This is the rank-one local-ring argument. -/
theorem exists_unit_coefficient (M : X.Modules) (hM : IsLocallyRankOne X M)
    (σ : M.GeneratingSections) [σ.IsFiniteType] (x : X) :
    ∃ (U : X.Opens) (_ : x ∈ U)
      (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) (i : σ.I),
      IsUnit (chartSectionEquiv X M U e U le_rfl ((σ.s i).val (op U))) := by
  classical
  let := Fintype.ofFinite σ.I
  obtain ⟨U, hxU, ⟨e⟩⟩ := (isLocallyRankOne_iff_local_unit X M).mp hM x
  have hsurj : PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X) σ.π.val :=
    inferInstance
  obtain ⟨V, f, ⟨a, ha⟩, hxV⟩ := hsurj.imageSieve_mem (chartGenerator X M U e) x hxU
  let hVU : V ≤ U := leOfHom f
  have ha' : σ.π.val.app (op V) a =
      M.val.map (homOfLE hVU).op (chartGenerator X M U e) := ha
  let b := SheafOfModules.freeSectionsBasis X.ringCatSheaf σ.I (op V)
  let c : σ.I → Γ(X, V) := fun i =>
    chartSectionEquiv X M U e V hVU ((σ.s i).val (op V))
  have hfree (i : σ.I) : σ.π.val.app (op V) (b i) = (σ.s i).val (op V) := by
    rw [SheafOfModules.freeSectionsBasis_apply]
    exact congrArg (fun t : M.sections => t.val (op V))
      (SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection σ.s i)
  let d : σ.I → Γ(X, V) := fun i => b.repr a i
  have hsum : ∑ i, d i * c i = 1 := by
    have hh := congrArg (fun t => chartSectionEquiv X M U e V hVU (σ.π.val.app (op V) t))
      (b.sum_repr a)
    rw [map_sum, map_sum, ha', chartGenerator_restrict, LinearEquiv.apply_symm_apply] at hh
    have hterm (i : σ.I) :
        chartSectionEquiv X M U e V hVU (σ.π.val.app (op V) (b.repr a i • b i)) =
          d i * c i := by
      have hφ : σ.π.val.app (op V) (b.repr a i • b i) =
          d i • σ.π.val.app (op V) (b i) :=
        (σ.π.val.app (op V)).hom.map_smul (b.repr a i) (b i)
      rw [hφ, hfree]
      exact (chartSectionEquiv X M U e V hVU).map_smul (d i) ((σ.s i).val (op V))
    calc
      _ = ∑ i, chartSectionEquiv X M U e V hVU
          (σ.π.val.app (op V) (b.repr a i • b i)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact (hterm i).symm
      _ = 1 := hh
  let g : Γ(X, V) →+* X.presheaf.stalk x := (X.presheaf.germ V x hxV).hom
  have hunit : IsUnit (∑ i, g (d i * c i)) := by
    rw [← map_sum, hsum, map_one]
    exact isUnit_one
  obtain ⟨i, _, hi⟩ := IsLocalRing.exists_of_isUnit_sum hunit
  have hci : IsUnit (g (c i)) :=
    isUnit_of_mul_isUnit_right (by simpa only [map_mul] using hi)
  let W := X.basicOpen (c i)
  have hxW : x ∈ W := (X.mem_basicOpen (c i) x hxV).mpr hci
  have hWV : W ≤ V := X.basicOpen_le (c i)
  let eW := restrictOverUnitIso X M (homOfLE (hWV.trans hVU)) e
  refine ⟨W, hxW, eW, i, ?_⟩
  change IsUnit (chartSectionEquiv X M U e W (hWV.trans hVU) ((σ.s i).val (op W)))
  have hc : chartSectionEquiv X M U e W (hWV.trans hVU) ((σ.s i).val (op W)) =
      sectionRestrict X hWV (c i) := by
    let q : Over.mk (homOfLE (hWV.trans hVU)) ⟶ Over.mk (homOfLE hVU) :=
      Over.homMk (homOfLE hWV)
    have hh := PresheafOfModules.naturality_apply e.hom.val q.op ((σ.s i).val (op V))
    change chartSectionEquiv X M U e W (hWV.trans hVU)
        (M.val.map (homOfLE hWV).op ((σ.s i).val (op V))) =
      sectionRestrict X hWV (c i) at hh
    rw [PresheafOfModules.sections_property] at hh
    exact hh
  rw [hc]
  exact X.toRingedSpace.isUnit_res_basicOpen (c i)

/-- The frame normalized so that its generator is the original specified section. -/
def normalizedFrame (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (s : M.sections)
    (hs : IsUnit (chartSectionEquiv X M U e U le_rfl (s.val (op U)))) :
    M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U) :=
  e ≪≫ unitScaleOnIso U hs.unit⁻¹

theorem normalizedFrame_coefficient (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (s : M.sections)
    (hs : IsUnit (chartSectionEquiv X M U e U le_rfl (s.val (op U)))) :
    chartSectionEquiv X M U (normalizedFrame M U e s hs) U le_rfl (s.val (op U)) = 1 := by
  change chartSectionEquiv X M U e U le_rfl (s.val (op U)) *
    sectionRestrict X (show U ≤ U from le_rfl) (↑hs.unit⁻¹) = 1
  have hid (z : Γ(X, U)) : sectionRestrict X (show U ≤ U from le_rfl) z = z := by
    change X.presheaf.map (𝟙 (op U)) z = z
    simp
  rw [hid]
  exact ((congrArg (fun z : Γ(X, U) => z * (↑hs.unit⁻¹)) (IsUnit.unit_spec hs)).symm).trans
    (Units.mul_inv hs.unit)

/-- A genuinely finite globally generating family supplies its own actual section frames. -/
def framesOfGeneratingSections (M : X.Modules) (hM : IsLocallyRankOne X M)
    (σ : M.GeneratingSections) [σ.IsFiniteType] : SectionFrames M σ.s := by
  classical
  choose U hx e i hi using exists_unit_coefficient M hM σ
  exact {
    K := X
    U := U
    covers := eq_top_iff.mpr (fun x _ => Opens.mem_iSup.mpr ⟨x, hx x⟩)
    coordinate := i
    frame := fun x => normalizedFrame M (U x) (e x) (σ.s (i x)) (hi x)
    selected := fun x => normalizedFrame_coefficient M (U x) (e x) (σ.s (i x)) (hi x) }

/-- The actual native projective morphism obtained from the original finite generating family. -/
def mapOfGeneratingSections (p : X ⟶ Spec (CommRingCat.of R))
    (M : X.Modules) (hM : IsLocallyRankOne X M)
    (σ : M.GeneratingSections) [σ.IsFiniteType] : X ⟶ ProjectiveSpace R σ.I :=
  (framesOfGeneratingSections M hM σ).map p

@[reassoc]
theorem mapOfGeneratingSections_toSpec (p : X ⟶ Spec (CommRingCat.of R))
    (M : X.Modules) (hM : IsLocallyRankOne X M)
    (σ : M.GeneratingSections) [σ.IsFiniteType] :
    mapOfGeneratingSections p M hM σ ≫ toSpec R σ.I = p :=
  (framesOfGeneratingSections M hM σ).map_toSpec p

theorem mapOfGeneratingSections_preimage (p : X ⟶ Spec (CommRingCat.of R))
    (M : X.Modules) (hM : IsLocallyRankOne X M)
    (σ : M.GeneratingSections) [σ.IsFiniteType] (i : σ.I) :
    mapOfGeneratingSections p M hM σ ⁻¹ᵁ coordinateOpen R σ.I i =
      (framesOfGeneratingSections M hM σ).nonvanishingOpen i :=
  (framesOfGeneratingSections M hM σ).map_preimage_coordinateOpen p i

/-- The actual free-map epimorphism of a specified original morphism family, retaining
its original coordinate index. -/
def generatingSectionsOfFamily {M : X.Modules}
    (s : I → (SheafOfModules.unit X.ringCatSheaf ⟶ M))
    [Epi (CategoryTheory.Limits.Sigma.desc s)] : M.GeneratingSections where
  I := I
  s := M.freeHomEquiv (CategoryTheory.Limits.Sigma.desc s)
  epi := by
    rw [Equiv.symm_apply_apply]
    infer_instance

@[simp]
theorem generatingSectionsOfFamily_section {M : X.Modules}
    (s : I → (SheafOfModules.unit X.ringCatSheaf ⟶ M))
    [Epi (CategoryTheory.Limits.Sigma.desc s)] (i : I) :
    (generatingSectionsOfFamily s).s i = M.unitHomEquiv (s i) := by
  change M.unitHomEquiv (SheafOfModules.ιFree i ≫ CategoryTheory.Limits.Sigma.desc s) = _
  rw [SheafOfModules.ιFree, CategoryTheory.Limits.Sigma.ι_comp_desc]

instance generatingSectionsOfFamily_isFiniteType {M : X.Modules} [Finite I]
    (s : I → (SheafOfModules.unit X.ringCatSheaf ⟶ M))
    [Epi (CategoryTheory.Limits.Sigma.desc s)] :
    (generatingSectionsOfFamily s).IsFiniteType where
  finite := inferInstanceAs (Finite I)

/-- A finite original family of structure-module maps with an epimorphic free map
constructs an actual native projective morphism, with the same coordinate index. -/
def mapOfFiniteFamily (p : X ⟶ Spec (CommRingCat.of R))
    (M : X.Modules) (hM : IsLocallyRankOne X M) [Finite I]
    (s : I → (SheafOfModules.unit X.ringCatSheaf ⟶ M))
    [Epi (CategoryTheory.Limits.Sigma.desc s)] : X ⟶ ProjectiveSpace R I :=
  mapOfGeneratingSections p M hM (generatingSectionsOfFamily s)

@[reassoc]
theorem mapOfFiniteFamily_toSpec (p : X ⟶ Spec (CommRingCat.of R))
    (M : X.Modules) (hM : IsLocallyRankOne X M) [Finite I]
    (s : I → (SheafOfModules.unit X.ringCatSheaf ⟶ M))
    [Epi (CategoryTheory.Limits.Sigma.desc s)] :
    mapOfFiniteFamily p M hM s ≫ toSpec R I = p :=
  mapOfGeneratingSections_toSpec p M hM (generatingSectionsOfFamily s)

theorem mapOfFiniteFamily_preimage (p : X ⟶ Spec (CommRingCat.of R))
    (M : X.Modules) (hM : IsLocallyRankOne X M) [Finite I]
    (s : I → (SheafOfModules.unit X.ringCatSheaf ⟶ M))
    [Epi (CategoryTheory.Limits.Sigma.desc s)] (i : I) :
    mapOfFiniteFamily p M hM s ⁻¹ᵁ coordinateOpen R I i =
      (framesOfGeneratingSections M hM (generatingSectionsOfFamily s)).nonvanishingOpen i :=
  mapOfGeneratingSections_preimage p M hM (generatingSectionsOfFamily s) i


section PullbackCocycle

variable {Y : Scheme.{u}} {J : Type u} {V : J → Y.Opens}
  (f : X ⟶ Y) (c : UnitCocycle V)

private theorem restrict_appLE {A : Y.Opens} {B C : X.Opens}
    (e : B ≤ f ⁻¹ᵁ A) (h : C ≤ B) (r : Γ(Y, A)) :
    sectionRestrict X h ((f.appLE A B e).hom r) =
      (f.appLE A C (h.trans e)).hom r := by
  change (f.appLE A B e ≫ X.presheaf.map (homOfLE h).op).hom r = _
  rw [Scheme.Hom.appLE_map]

private theorem appLE_restrict {A B : Y.Opens} {C : X.Opens}
    (h : B ≤ A) (e : C ≤ f ⁻¹ᵁ B) (r : Γ(Y, A)) :
    (f.appLE B C e).hom (sectionRestrict Y h r) =
      (f.appLE A C (e.trans (f.preimage_mono h))).hom r := by
  change (Y.presheaf.map (homOfLE h).op ≫ f.appLE B C e).hom r = _
  rw [Scheme.Hom.map_appLE]

private theorem restrict_unit_appLE {A : Y.Opens} {B C : X.Opens}
    (e : B ≤ f ⁻¹ᵁ A) (h : C ≤ B) (r : Γ(Y, A)ˣ) :
    Units.map (sectionRestrict X h).toMonoidHom
        (Units.map (f.appLE A B e).hom.toMonoidHom r) =
      Units.map (f.appLE A C (h.trans e)).hom.toMonoidHom r := by
  apply Units.ext
  exact restrict_appLE f e h r.val

private theorem unit_appLE_restrict {A B : Y.Opens} {C : X.Opens}
    (h : B ≤ A) (e : C ≤ f ⁻¹ᵁ B) (r : Γ(Y, A)ˣ) :
    Units.map (f.appLE B C e).hom.toMonoidHom
        (Units.map (sectionRestrict Y h).toMonoidHom r) =
      Units.map (f.appLE A C (e.trans (f.preimage_mono h))).hom.toMonoidHom r := by
  apply Units.ext
  exact appLE_restrict f h e r.val

/-- Pullback of the actual units of an actual native line-module cocycle. -/
def pullbackCocycle : UnitCocycle (fun i => f ⁻¹ᵁ V i) where
  transition i j := Units.map
    (f.appLE (V i ⊓ V j) ((f ⁻¹ᵁ V i) ⊓ (f ⁻¹ᵁ V j))
      (by rw [Scheme.Hom.preimage_inf])).hom.toMonoidHom (c.transition i j)
  cocycle i j k O hi hj hk := by
    let W := V i ⊓ V j ⊓ V k
    have hi' : W ≤ V i := inf_le_left.trans inf_le_left
    have hj' : W ≤ V j := inf_le_left.trans inf_le_right
    have hk' : W ≤ V k := inf_le_right
    have e : O ≤ f ⁻¹ᵁ W := by
      rw [Scheme.Hom.preimage_inf, Scheme.Hom.preimage_inf]
      exact le_inf (le_inf hi hj) hk
    have h := congrArg (Units.map (f.appLE W O e).hom.toMonoidHom)
      (c.cocycle i j k W hi' hj' hk')
    rw [map_mul, unit_appLE_restrict, unit_appLE_restrict, unit_appLE_restrict] at h
    rw [restrict_unit_appLE, restrict_unit_appLE, restrict_unit_appLE]
    exact h

/-- The pulled transition on any original source subopen is the image of the original
transition on any target common subopen containing its image. -/
theorem pullbackCocycle_transitionOn (i j : J) {O : X.Opens} {W : Y.Opens}
    (hi : O ≤ f ⁻¹ᵁ V i) (hj : O ≤ f ⁻¹ᵁ V j)
    (hi' : W ≤ V i) (hj' : W ≤ V j) (e : O ≤ f ⁻¹ᵁ W) :
    (pullbackCocycle f c).transitionOn i j hi hj =
      Units.map (f.appLE W O e).hom.toMonoidHom (c.transitionOn i j hi' hj') := by
  unfold UnitCocycle.transitionOn
  dsimp only [pullbackCocycle]
  rw [restrict_unit_appLE, unit_appLE_restrict]

theorem pullbackCocycle_transition : UnitCocycle.TransitionPullback f c (pullbackCocycle f c) := by
  intro i j e
  rfl

/-- Actual pullback of a cocycle sheaf, with the original generator maps. -/
def pullbackCocycleIso (hV : iSup V = ⊤) :
    (Scheme.Modules.pullback f).obj c.sheaf ≅ (pullbackCocycle f c).sheaf :=
  c.pullbackIso f (pullbackCocycle f c) (fun _ => rfl) (pullbackCocycle_transition f c) hV

end PullbackCocycle

/-- The actual O(1) transition multiplies the original normalized coordinate functions. -/
theorem coordinateTwistTransition_mul_ratio (R : Type u) [CommRing R] (I : Type u)
    (a i j : I) {W : (ProjectiveSpace R I).Opens}
    (ha : W ≤ coordinateOpen R I a) (hi : W ≤ coordinateOpen R I i)
    (hj : W ≤ coordinateOpen R I j) :
    (((coordinateUnitCocycle R I).zpow (-1)).transitionOn i j hi hj : Γ(ProjectiveSpace R I, W)) *
        sectionRestrict (ProjectiveSpace R I) ha (coordinateRatioSection R I a i) =
      sectionRestrict (ProjectiveSpace R I) ha (coordinateRatioSection R I a j) := by
  let c := (coordinateUnitCocycle R I).zpow (-1)
  have hratio (b : I) (hb : W ≤ coordinateOpen R I b) :
      sectionRestrict (ProjectiveSpace R I) ha (coordinateRatioSection R I a b) =
        (c.transitionOn a b ha hb : Γ(ProjectiveSpace R I, W)) := by
    rw [coordinateRatioSection_transition R I b a b ha hb,
      coordinateRatioSection_self, map_one, mul_one]
    simp only [c, UnitCocycle.zpow_transitionOn, coordinateUnitCocycle_transitionOn, zpow_neg_one]
  rw [hratio i hi, hratio j hj]
  change (c.transitionOn i j hi hj).val * (c.transitionOn a i ha hi).val =
    (c.transitionOn a j ha hj).val
  rw [mul_comm]
  exact congrArg Units.val (c.transitionOn_cocycle a i j ha hi hj)

namespace SectionFrames

variable {M : X.Modules} {s : I → M.sections} (F : SectionFrames M s)
  (p : X ⟶ Spec (CommRingCat.of R))

/-- The actual coordinate transition cocycle on the original inverse-image charts. -/
abbrev coordinatePullbackCocycle :=
  pullbackCocycle (F.map p) ((coordinateUnitCocycle R I).zpow (-1))

theorem originalSections_transition (i j : I) (V : X.Opens)
    (hi : V ≤ F.map p ⁻¹ᵁ coordinateOpen R I i)
    (hj : V ≤ F.map p ⁻¹ᵁ coordinateOpen R I j) :
    (s j).val (op V) =
      ((F.coordinatePullbackCocycle p).transitionOn i j hi hj : Γ(X, V)) •
        (show Γ(M, V) from (s i).val (op V)) := by
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨M.presheaf, M.isSheaf⟩
    (fun k => V ⊓ F.U k) V (fun _ => homOfLE inf_le_left)
    (by rw [← inf_iSup_eq, F.covers, inf_top_eq])
  intro k
  let O := V ⊓ F.U k
  let W := coordinateOpen R I (F.coordinate k) ⊓ coordinateOpen R I i ⊓ coordinateOpen R I j
  have haW : W ≤ coordinateOpen R I (F.coordinate k) := inf_le_left.trans inf_le_left
  have hiW : W ≤ coordinateOpen R I i := inf_le_left.trans inf_le_right
  have hjW : W ≤ coordinateOpen R I j := inf_le_right
  have hk : O ≤ F.U k := inf_le_right
  have hiO : O ≤ F.map p ⁻¹ᵁ coordinateOpen R I i := inf_le_left.trans hi
  have hjO : O ≤ F.map p ⁻¹ᵁ coordinateOpen R I j := inf_le_left.trans hj
  have e : O ≤ F.map p ⁻¹ᵁ W := by
    rw [Scheme.Hom.preimage_inf, Scheme.Hom.preimage_inf]
    exact le_inf (le_inf (F.le_map_preimage_selected p k hk) hiO) hjO
  change M.val.map (homOfLE inf_le_left).op ((s j).val (op V)) =
    M.val.map (homOfLE inf_le_left).op
      (((F.coordinatePullbackCocycle p).transitionOn i j hi hj).val •
        (show Γ(M, V) from (s i).val (op V)))
  rw [PresheafOfModules.sections_property, PresheafOfModules.map_smul,
    PresheafOfModules.sections_property]
  change (s j).val (op O) =
    sectionRestrict X inf_le_left
      ((F.coordinatePullbackCocycle p).transitionOn i j hi hj : Γ(X, V)) •
        (show Γ(M, O) from (s i).val (op O))
  rw [UnitCocycle.sectionRestrict_transitionOn]
  apply (LocalFrames.coefficient F.U M F.frame k hk).injective
  rw [_root_.map_smul, smul_eq_mul]
  have h := congrArg ((F.map p).appLE W O e).hom
    (coordinateTwistTransition_mul_ratio R I (F.coordinate k) i j haW hiW hjW)
  rw [map_mul] at h
  rw [appLE_restrict, appLE_restrict] at h
  rw [F.map_coordinateRatioSection p k hk i, F.map_coordinateRatioSection p k hk j] at h
  have ht := congrArg Units.val
    (pullbackCocycle_transitionOn (F.map p) ((coordinateUnitCocycle R I).zpow (-1))
      i j hiO hjO hiW hjW e)
  change ((F.coordinatePullbackCocycle p).transitionOn i j hiO hjO : Γ(X, O)) =
    ((F.map p).appLE W O e).hom
      (((coordinateUnitCocycle R I).zpow (-1)).transitionOn i j hiW hjW :
        Γ(ProjectiveSpace R I, W)) at ht
  exact ((congrArg (fun z : Γ(X, O) => z * F.coefficientOn k hk i) ht).trans h).symm

end SectionFrames

namespace SectionFrames

variable {M : X.Modules} {s : I → M.sections} (F : SectionFrames M s)
  (p : X ⟶ Spec (CommRingCat.of R))

theorem iSup_coordinatePreimage : (⨆ i, F.map p ⁻¹ᵁ coordinateOpen R I i) = ⊤ := by
  rw [← Scheme.Hom.preimage_iSup, iSup_coordinateOpen_eq_top, Scheme.Hom.preimage_top]

/-- The actual original section family constructs the comparison from the pulled cocycle. -/
def sectionsComparison : (F.coordinatePullbackCocycle p).sheaf ⟶ M :=
  (F.coordinatePullbackCocycle p).homOfLocalSections M (F.iSup_coordinatePreimage p)
    (fun i => (s i).val (op (F.map p ⁻¹ᵁ coordinateOpen R I i))) (by
      intro i j V hi hj
      rw [PresheafOfModules.sections_property, PresheafOfModules.sections_property]
      exact F.originalSections_transition p i j V hi hj)

/-- The comparison sends each actual pulled-cocycle generator to the original section
on every original source subopen of its coordinate preimage. -/
theorem sectionsComparison_generator (i : I) {V : X.Opens}
    (hi : V ≤ F.map p ⁻¹ᵁ coordinateOpen R I i) :
    (F.sectionsComparison p).val.app (op V)
      ((F.coordinatePullbackCocycle p).generator i hi) = (s i).val (op V) := by
  dsimp only [sectionsComparison]
  rw [UnitCocycle.homOfLocalSections_apply, UnitCocycle.localSectionsEquiv_generator,
    one_smul, PresheafOfModules.sections_property]
  exact hi

/-- The comparison is the actual frame isomorphism on every original source chart. -/
theorem sectionsComparison_over (k : F.K) :
    (SheafOfModules.overFunctor X.ringCatSheaf (F.U k)).map (F.sectionsComparison p) =
      (restrictOverUnitIso X (F.coordinatePullbackCocycle p).sheaf
        (homOfLE (F.le_map_preimage_selected p k le_rfl))
        ((F.coordinatePullbackCocycle p).localIso (F.coordinate k))).hom ≫ (F.frame k).inv := by
  apply SheafOfModules.hom_ext
  ext V t
  have hh := (F.coordinatePullbackCocycle p).homOfLocalSections_apply M
    (F.iSup_coordinatePreimage p)
    (fun i => (s i).val (op (F.map p ⁻¹ᵁ coordinateOpen R I i)))
    (by
      intro i j V hi hj
      rw [PresheafOfModules.sections_property, PresheafOfModules.sections_property]
      exact F.originalSections_transition p i j V hi hj)
    (F.coordinate k) V.unop.left
    ((leOfHom V.unop.hom).trans (F.le_map_preimage_selected p k le_rfl)) t
  change (F.sectionsComparison p).val.app (op V.unop.left) t = _
  refine hh.trans ?_
  rw [PresheafOfModules.sections_property, F.selected_eq_generator k (leOfHom V.unop.hom)]
  apply (LocalFrames.coefficient F.U M F.frame k (leOfHom V.unop.hom)).injective
  rw [_root_.map_smul, LocalFrames.coefficient_generator, smul_eq_mul, mul_one]
  exact ((LocalFrames.coefficient F.U M F.frame k (leOfHom V.unop.hom)).apply_symm_apply _).symm

instance sectionsComparison_isIso : IsIso (F.sectionsComparison p) := by
  apply Scheme.Modules.Pullback.OpenRestriction.isIso_of_local_restrict
  intro x
  obtain ⟨k, hk⟩ := Opens.mem_iSup.mp (show x ∈ iSup F.U by rw [F.covers]; trivial)
  refine ⟨F.U k, hk, ?_⟩
  have : IsIso ((SheafOfModules.overFunctor X.ringCatSheaf (F.U k)).map
      (F.sectionsComparison p)) := by
    rw [F.sectionsComparison_over p k]
    infer_instance
  exact (NatIso.isIso_map_iff (overFunctorEquiv (F.U k)) (F.sectionsComparison p)).mp
    (inferInstanceAs (IsIso ((overEquiv (F.U k)).functor.map
      ((SheafOfModules.overFunctor X.ringCatSheaf (F.U k)).map (F.sectionsComparison p)))))

/-- Actual recovery of the original line module as the pullback of native O(1). -/
def twistingPullbackIso :
    (Scheme.Modules.pullback (F.map p)).obj (twistingSheaf R I 1) ≅ M :=
  pullbackCocycleIso (F.map p) ((coordinateUnitCocycle R I).zpow (-1))
      (iSup_coordinateOpen_eq_top R I) ≪≫ asIso (F.sectionsComparison p)

/-- The comparison retains each original selected section on its full coordinate preimage. -/
theorem twistingPullbackIso_hom_generator (i : I) {V : X.Opens}
    (hi : V ≤ F.map p ⁻¹ᵁ coordinateOpen R I i) :
    (F.twistingPullbackIso p).hom.val.app (op V)
      (((coordinateUnitCocycle R I).zpow (-1)).pullbackGenerator (F.map p) i hi) =
        (s i).val (op V) := by
  change (F.sectionsComparison p).val.app (op V)
    ((pullbackCocycleIso (F.map p) ((coordinateUnitCocycle R I).zpow (-1))
      (iSup_coordinateOpen_eq_top R I)).hom.val.app (op V)
        (((coordinateUnitCocycle R I).zpow (-1)).pullbackGenerator (F.map p) i hi)) = _
  rw [pullbackCocycleIso, UnitCocycle.pullbackIso_hom_pullbackGenerator]
  exact F.sectionsComparison_generator p i hi

end SectionFrames

section PulledGlobalSection

variable {Y : Scheme.{u}} {J : Type u} {V : J → Y.Opens}
  (f : X ⟶ Y) (c : UnitCocycle V)

/-- Pullback of an actual global module section by the native pullback adjunction unit. -/
def pulledGlobalSection (t : Γ(c.sheaf, ⊤)) :
    Γ((Scheme.Modules.pullback f).obj c.sheaf, ⊤) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app c.sheaf).val.app (op ⊤) t

/-- In a pulled-back original frame, the global section has its actual pulled coefficient. -/
theorem pulledGlobalSection_restrict (t : Γ(c.sheaf, ⊤)) (i : J)
    {O : X.Opens} (hi : O ≤ f ⁻¹ᵁ V i) :
    ((Scheme.Modules.pullback f).obj c.sheaf).val.map (homOfLE le_top).op
        (pulledGlobalSection f c t) =
      (f.appLE (V i) O hi).hom
          (c.localSectionsEquiv i le_rfl
            (c.sheaf.val.map (homOfLE le_top).op t)) • c.pullbackGenerator f i hi := by
  let N := (Scheme.Modules.pullback f).obj c.sheaf
  let η : c.sheaf ⟶ (Scheme.Modules.pushforward f).obj N :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app c.sheaf
  have h₀ := congrArg (η.val.app (op (V i)))
    ((c.localSectionsEquiv_smul_generator i le_rfl
      (c.sheaf.val.map (homOfLE le_top).op t)).symm)
  have hlin := (η.val.app (op (V i))).hom.map_smul
    (c.localSectionsEquiv i le_rfl (c.sheaf.val.map (homOfLE le_top).op t))
    (c.generator i le_rfl)
  rw [hlin, PresheafOfModules.naturality_apply η.val] at h₀
  change N.val.map (homOfLE le_top).op (pulledGlobalSection f c t) =
    (f.app (V i)).hom
        (c.localSectionsEquiv i le_rfl (c.sheaf.val.map (homOfLE le_top).op t)) •
      (show Γ(N, f ⁻¹ᵁ V i) from
        η.val.app (op (V i)) (c.generator i le_rfl)) at h₀
  have h₁ := congrArg (N.val.map (homOfLE hi).op) h₀
  rw [PresheafOfModules.map_smul, ← PresheafOfModules.map_comp_apply] at h₁
  exact h₁

end PulledGlobalSection

namespace SectionFrames

variable {M : X.Modules} {s : I → M.sections} (F : SectionFrames M s)
  (p : X ⟶ Spec (CommRingCat.of R))

/-- The actual pullback comparison sends every original global coordinate section to
its originally prescribed section, including outside that coordinate's own open. -/
theorem twistingPullbackIso_hom_coordinate (j : I) :
    (F.twistingPullbackIso p).hom.val.app (op ⊤)
      (pulledGlobalSection (F.map p) ((coordinateUnitCocycle R I).zpow (-1))
        (homogeneousSection R I 1 (coordinatePower R I 1 j))) = (s j).val (op ⊤) := by
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨M.presheaf, M.isSheaf⟩
    F.U ⊤ (fun _ => homOfLE le_top) (by rw [F.covers])
  intro k
  change M.val.map (homOfLE (show F.U k ≤ ⊤ from le_top)).op
      ((F.twistingPullbackIso p).hom.val.app (op ⊤)
        (pulledGlobalSection (F.map p) ((coordinateUnitCocycle R I).zpow (-1))
          (homogeneousSection R I 1 (coordinatePower R I 1 j)))) =
    M.val.map (homOfLE (show F.U k ≤ ⊤ from le_top)).op ((s j).val (op ⊤))
  rw [← PresheafOfModules.naturality_apply (F.twistingPullbackIso p).hom.val,
    PresheafOfModules.sections_property]
  have ht := pulledGlobalSection_restrict (F.map p)
    ((coordinateUnitCocycle R I).zpow (-1))
    (homogeneousSection R I 1 (coordinatePower R I 1 j))
    (F.coordinate k) (F.le_map_preimage_selected p k le_rfl)
  have hmap := congrArg ((F.twistingPullbackIso p).hom.val.app (op (F.U k))) ht
  refine hmap.trans ?_
  have hc : ((coordinateUnitCocycle R I).zpow (-1)).localSectionsEquiv (F.coordinate k) le_rfl
      (((coordinateUnitCocycle R I).zpow (-1)).sheaf.val.map (homOfLE le_top).op
        (homogeneousSection R I 1 (coordinatePower R I 1 j))) =
      coordinateRatioSection R I (F.coordinate k) j :=
    (homogeneousSection_local R I 1 (coordinatePower R I 1 j) (F.coordinate k)).trans
      (coordinateRatioSection_eq_homogeneousChartSection R I (F.coordinate k) j).symm
  let a : Γ(X, F.U k) :=
    ((F.map p).appLE (coordinateOpen R I (F.coordinate k)) (F.U k)
      (F.le_map_preimage_selected p k le_rfl)).hom
        (((coordinateUnitCocycle R I).zpow (-1)).localSectionsEquiv (F.coordinate k) le_rfl
          (((coordinateUnitCocycle R I).zpow (-1)).sheaf.val.map (homOfLE le_top).op
            (homogeneousSection R I 1 (coordinatePower R I 1 j))))
  let v : Γ((Scheme.Modules.pullback (F.map p)).obj (twistingSheaf R I 1), F.U k) :=
    ((coordinateUnitCocycle R I).zpow (-1)).pullbackGenerator (F.map p) (F.coordinate k)
      (F.le_map_preimage_selected p k le_rfl)
  let φ := (F.twistingPullbackIso p).hom.val.app (op (F.U k))
  change φ (a • v) = (s j).val (op (F.U k))
  have ha : a = F.coefficientOn k le_rfl j :=
    (congrArg ((F.map p).appLE (coordinateOpen R I (F.coordinate k)) (F.U k)
      (F.le_map_preimage_selected p k le_rfl)).hom hc).trans
        (F.map_coordinateRatioSection p k le_rfl j)
  have hlin : φ (a • v) = a • (show Γ(M, F.U k) from φ v) := φ.hom.map_smul a v
  have hg : (show Γ(M, F.U k) from φ v) = (s (F.coordinate k)).val (op (F.U k)) :=
    F.twistingPullbackIso_hom_generator p (F.coordinate k)
      (F.le_map_preimage_selected p k le_rfl)
  have hs : (show Γ(M, F.U k) from (s (F.coordinate k)).val (op (F.U k))) =
      LocalFrames.generator F.U M F.frame k le_rfl := F.selected_eq_generator k le_rfl
  have hscale := congrArg (fun z : Γ(M, F.U k) => a • z) hg
  have hgen := (congrArg₂ (fun (r : Γ(X, F.U k)) (z : Γ(M, F.U k)) => r • z) ha hs).trans
    (LocalFrames.coefficient_smul_generator F.U M F.frame k le_rfl
      ((s j).val (op (F.U k))))
  exact hlin.trans (hscale.trans hgen)

/-- The actual unit-module map corresponding to the pulled native coordinate section. -/
def pulledCoordinateSectionMap (j : I) :
    SheafOfModules.unit X.ringCatSheaf ⟶
      (Scheme.Modules.pullback (F.map p)).obj (twistingSheaf R I 1) :=
  (unitHomGlobalSectionsEquiv X _).symm
    (pulledGlobalSection (F.map p) ((coordinateUnitCocycle R I).zpow (-1))
      (homogeneousSection R I 1 (coordinatePower R I 1 j)))

/-- The comparison retains the originally prescribed actual section maps. -/
@[reassoc]
theorem pulledCoordinateSectionMap_comp (j : I) :
    F.pulledCoordinateSectionMap p j ≫ (F.twistingPullbackIso p).hom =
      M.unitHomEquiv.symm (s j) := by
  apply (unitHomGlobalSectionsEquiv X M).injective
  rw [unitHomGlobalSectionsEquiv_naturality]
  change (F.twistingPullbackIso p).hom.val.app (op ⊤)
      (unitHomGlobalSectionsEquiv X _ (F.pulledCoordinateSectionMap p j)) = _
  rw [pulledCoordinateSectionMap, Equiv.apply_symm_apply, F.twistingPullbackIso_hom_coordinate p j]
  exact (congrArg (fun t : M.sections => t.val (op ⊤))
    (M.unitHomEquiv.apply_symm_apply (s j))).symm

end SectionFrames

/-- The actual line-module comparison for the original finite globally generating family. -/
def twistingPullbackIsoOfFiniteFamily (p : X ⟶ Spec (CommRingCat.of R))
    (M : X.Modules) (hM : IsLocallyRankOne X M) [Finite I]
    (s : I → (SheafOfModules.unit X.ringCatSheaf ⟶ M))
    [Epi (CategoryTheory.Limits.Sigma.desc s)] :
    (Scheme.Modules.pullback (mapOfFiniteFamily p M hM s)).obj (twistingSheaf R I 1) ≅ M :=
  (framesOfGeneratingSections M hM (generatingSectionsOfFamily s)).twistingPullbackIso p

/-- The actual section map obtained by pulling back the original native homogeneous coordinate. -/
def pulledCoordinateMapOfFiniteFamily (p : X ⟶ Spec (CommRingCat.of R))
    (M : X.Modules) (hM : IsLocallyRankOne X M) [Finite I]
    (s : I → (SheafOfModules.unit X.ringCatSheaf ⟶ M))
    [Epi (CategoryTheory.Limits.Sigma.desc s)] (i : I) :
    SheafOfModules.unit X.ringCatSheaf ⟶
      (Scheme.Modules.pullback (mapOfFiniteFamily p M hM s)).obj (twistingSheaf R I 1) :=
  (framesOfGeneratingSections M hM (generatingSectionsOfFamily s)).pulledCoordinateSectionMap p i

/-- The actual comparison preserves each of the original chosen section morphisms. -/
@[reassoc]
theorem pulledCoordinateMapOfFiniteFamily_comp (p : X ⟶ Spec (CommRingCat.of R))
    (M : X.Modules) (hM : IsLocallyRankOne X M) [Finite I]
    (s : I → (SheafOfModules.unit X.ringCatSheaf ⟶ M))
    [Epi (CategoryTheory.Limits.Sigma.desc s)] (i : I) :
    pulledCoordinateMapOfFiniteFamily p M hM s i ≫
        (twistingPullbackIsoOfFiniteFamily p M hM s).hom = s i := by
  let F := framesOfGeneratingSections M hM (generatingSectionsOfFamily s)
  have h := F.pulledCoordinateSectionMap_comp p i
  rw [generatingSectionsOfFamily_section, Equiv.symm_apply_apply] at h
  exact h

end AlgebraicGeometry.ProjectiveSpace.FromSections
