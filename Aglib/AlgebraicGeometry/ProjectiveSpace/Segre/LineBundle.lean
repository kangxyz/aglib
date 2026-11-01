/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Segre.ClosedImmersion
public import Aglib.AlgebraicGeometry.ProjectiveSpace.FromSections
public import Aglib.AlgebraicGeometry.Modules.Invertible.Gluing.PullbackCocycle
public import Aglib.AlgebraicGeometry.Modules.Invertible.Gluing.Tensor
public import Aglib.AlgebraicGeometry.Modules.Invertible.Nonvanishing.Tensor
public import Aglib.AlgebraicGeometry.Modules.Invertible.PullbackTensor.Local

/-!
# The original Segre map pulls O(1) back to the tensor of the factor O(1)'s

The comparison uses the existing product-coordinate morphism and its actual
common inverse-image chart cover. Its coordinate-ring map evaluates the
product of the original factor ratios. The corresponding pulled generator
is sent to the pure tensor of the original factor generators. These maps
agree on overlaps and are the tensor frame isomorphisms on the same cover.

All constructions work over an arbitrary commutative ring, without finite
coordinate types or an alternative projective embedding.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace MvPolynomial
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveSpace.Segre

variable {R : Type u} [CommRing R] {ι κ : Type u} {Y : Scheme.{u}}
  (f : Y ⟶ ProjectiveSpace R ι) (g : Y ⟶ ProjectiveSpace R κ)

-- The projective chart and its original section-ring map cross the native Proj aliases.
set_option backward.isDefEq.respectTransparency false in
/-- On the original common chart, the native Segre ring map is its original
product-coordinate evaluation. -/
theorem map_chartRingHom (a : ι × κ) :
    Proj.awayToSection (homogeneousSubmodule (ι × κ) R) (MvPolynomial.X a) ≫
        (map f g).appLE (coordinateOpen R (ι × κ) a) (sourceOpen f g a)
          (map_preimage_coordinateOpen f g a).ge =
      CommRingCat.ofHom (sectionChartHom f g a) := by
  let W := coordinateOpen R (ι × κ) a
  let E := Proj.basicOpenIsoSpec (homogeneousSubmodule (ι × κ) R)
    (MvPolynomial.X a) (isHomogeneous_X R a) Nat.zero_lt_one
  have hr : (map f g).resLE W (sourceOpen f g a)
      (map_preimage_coordinateOpen f g a).ge =
      (sourceOpen f g a).toSpecΓ ≫ Spec.map (CommRingCat.ofHom (sectionChartHom f g a)) ≫
        E.inv := by
    apply (cancel_mono W.ι).mp
    rw [Scheme.Hom.resLE_comp_ι]
    simpa only [ChartGluing.localMap, ChartGluing.chartMap, Proj.awayι,
      Category.assoc, E, W, coordinateOpen] using ι_map f g a
  have hr' := congrArg (fun q => q ≫ E.hom) hr
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at hr'
  have hh := congrArg (fun q => q.appTop) hr'
  apply (cancel_epi (Scheme.ΓSpecIso (CommRingCat.of (coordinateRing R (ι × κ) a))).hom).mp
  apply (cancel_mono (sourceOpen f g a).topIso.inv).mp
  simpa only [Scheme.Hom.comp_appTop, Proj.basicOpenIsoSpec_hom,
    Proj.basicOpenToSpec_app_top, Scheme.Hom.resLE_app_top, Scheme.Opens.toSpecΓ_appTop,
    Category.assoc, Iso.inv_hom_id_assoc, Scheme.ΓSpecIso_naturality_assoc,
    E, W, coordinateOpen, coordinateRing] using hh

/-- The original target ratio pulls back to the product of the factor ratios. -/
theorem map_coordinateRatioSection (a b : ι × κ) :
    ratioOn (map f g) a b (sourceOpen f g a) (map_preimage_coordinateOpen f g a).ge =
      sectionValue f g a b := by
  change (Proj.awayToSection (homogeneousSubmodule (ι × κ) R) (MvPolynomial.X a) ≫
    (map f g).appLE (coordinateOpen R (ι × κ) a) (sourceOpen f g a)
      (map_preimage_coordinateOpen f g a).ge).hom (coordinateRatio R (ι × κ) a b) = _
  rw [map_chartRingHom]
  exact sectionChartHom_ratio f g a b

private theorem twist_transition_eq_ratio {α : Type u} (a b : α)
    {W : (ProjectiveSpace R α).Opens} (ha : W ≤ coordinateOpen R α a)
    (hb : W ≤ coordinateOpen R α b) :
    (((coordinateUnitCocycle R α).zpow (-1)).transitionOn a b ha hb :
      Γ(ProjectiveSpace R α, W)) =
      sectionRestrict (ProjectiveSpace R α) ha (coordinateRatioSection R α a b) := by
  simpa only [coordinateRatioSection_self, map_one, mul_one] using
    FromSections.coordinateTwistTransition_mul_ratio R α a a b ha ha hb

private theorem pulled_generator_transition {α : Type u}
    (q : Y ⟶ ProjectiveSpace R α) (a b : α) {V : Y.Opens}
    (ha : V ≤ q ⁻¹ᵁ coordinateOpen R α a) (hb : V ≤ q ⁻¹ᵁ coordinateOpen R α b) :
    ((coordinateUnitCocycle R α).zpow (-1)).pullbackGenerator q b hb =
      ratioOn q a b V ha •
        ((coordinateUnitCocycle R α).zpow (-1)).pullbackGenerator q a ha := by
  have hV : V ≤ q ⁻¹ᵁ (coordinateOpen R α a ⊓ coordinateOpen R α b) := le_inf ha hb
  rw [UnitCocycle.pullbackGenerator_transition q
    ((coordinateUnitCocycle R α).zpow (-1)) a b ha hb hV,
    twist_transition_eq_ratio]
  have h := ConcreteCategory.congr_hom (q.map_appLE hV (homOfLE inf_le_left).op)
    (coordinateRatioSection R α a b)
  exact congrArg (fun r : Γ(Y, V) => r •
    ((coordinateUnitCocycle R α).zpow (-1)).pullbackGenerator q a ha) h

namespace LineBundleComparison

/-- The original tensor of the two pulled-back twisting sheaves. -/
abbrev tensorModule : Y.Modules := tensorSheaf Y
  ((Scheme.Modules.pullback f).obj (twistingSheaf R ι 1))
  ((Scheme.Modules.pullback g).obj (twistingSheaf R κ 1))

/-- The actual tensor generator on an original common source chart. -/
def generator (a : ι × κ) {V : Y.Opens} (ha : V ≤ sourceOpen f g a) :
    Γ(tensorModule f g, V) :=
  moduleTensorSection Y _ _ V
    (((coordinateUnitCocycle R ι).zpow (-1)).pullbackGenerator f a.1
      (ha.trans inf_le_left))
    (((coordinateUnitCocycle R κ).zpow (-1)).pullbackGenerator g a.2
      (ha.trans inf_le_right))

-- Original tensor sections and sheaf restrictions use the two native module presentations.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem generator_restrict (a : ι × κ) {V W : Y.Opens} (h : V ≤ W)
    (ha : W ≤ sourceOpen f g a) :
    (tensorModule f g).val.map (homOfLE h).op (generator f g a ha) =
      generator f g a (h.trans ha) := by
  let L := (Scheme.Modules.pullback f).obj (twistingSheaf R ι 1)
  let M := (Scheme.Modules.pullback g).obj (twistingSheaf R κ 1)
  let s := ((coordinateUnitCocycle R ι).zpow (-1)).pullbackGenerator f a.1
    (ha.trans inf_le_left)
  let t := ((coordinateUnitCocycle R κ).zpow (-1)).pullbackGenerator g a.2
    (ha.trans inf_le_right)
  have ht : (tensorModule f g).val.map (homOfLE h).op (generator f g a ha) =
      moduleTensorSection Y L M V
        (L.val.map (homOfLE h).op s) (M.val.map (homOfLE h).op t) :=
    moduleTensorSection_restrict L M (homOfLE h) s t
  refine ht.trans ?_
  exact congrArg₂ (moduleTensorSection Y L M V)
    (((coordinateUnitCocycle R ι).zpow (-1)).pullbackGenerator_restrict f a.1
      (homOfLE h) (ha.trans inf_le_left))
    (((coordinateUnitCocycle R κ).zpow (-1)).pullbackGenerator_restrict g a.2
      (homOfLE h) (ha.trans inf_le_right))

/-- The original target twisting cocycle pulled to the same common chart cover. -/
abbrev cocycle : UnitCocycle (sourceOpen f g) :=
  ((coordinateUnitCocycle R (ι × κ)).zpow (-1)).pullbackCocycle (map f g)
    (map_preimage_coordinateOpen f g)

theorem cocycle_transition (a b : ι × κ) {V : Y.Opens}
    (ha : V ≤ sourceOpen f g a) (hb : V ≤ sourceOpen f g b) :
    ((cocycle f g).transitionOn a b ha hb : Γ(Y, V)) =
      ratioOn f a.1 b.1 V (ha.trans inf_le_left) *
        ratioOn g a.2 b.2 V (ha.trans inf_le_right) := by
  let W := coordinateOpen R (ι × κ) a ⊓ coordinateOpen R (ι × κ) b
  have hV : V ≤ map f g ⁻¹ᵁ W :=
    le_inf (ha.trans (map_preimage_coordinateOpen f g a).ge)
      (hb.trans (map_preimage_coordinateOpen f g b).ge)
  rw [← UnitCocycle.TransitionPullback.appLE_transitionOn
    (UnitCocycle.transitionPullback_pullbackCocycle (map f g)
      ((coordinateUnitCocycle R (ι × κ)).zpow (-1)) (map_preimage_coordinateOpen f g))
    (map_preimage_coordinateOpen f g) a b inf_le_left inf_le_right ha hb hV,
    twist_transition_eq_ratio]
  have h := ConcreteCategory.congr_hom
    ((map f g).map_appLE hV (homOfLE inf_le_left).op)
    (coordinateRatioSection R (ι × κ) a b)
  refine h.trans ?_
  change ratioOn (map f g) a b V _ = _
  rw [← ratioOn_restrict (map f g) a b ha (map_preimage_coordinateOpen f g a).ge,
    map_coordinateRatioSection, sectionValue, map_mul, ratioOn_restrict, ratioOn_restrict]

-- O(1) is the original power cocycle sheaf; its tensor-section carrier is unchanged.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem generator_transition (a b : ι × κ) {V : Y.Opens}
    (ha : V ≤ sourceOpen f g a) (hb : V ≤ sourceOpen f g b) :
    generator f g b hb =
      ((cocycle f g).transitionOn a b ha hb : Γ(Y, V)) • generator f g a ha := by
  rw [generator, pulled_generator_transition f a.1 b.1 (ha.trans inf_le_left),
    pulled_generator_transition g a.2 b.2 (ha.trans inf_le_right),
    UnitCocycle.moduleTensorSection_smul_smul, cocycle_transition]
  rfl

/-- The pullback frame of one factor restricted to the actual common chart. -/
def factorFrame {α : Type u} (q : Y ⟶ ProjectiveSpace R α) (a : α)
    {U : Y.Opens} (hU : U ≤ q ⁻¹ᵁ coordinateOpen R α a) :
    ((Scheme.Modules.pullback q).obj (twistingSheaf R α 1)).over U ≅
      SheafOfModules.unit (Y.ringCatSheaf.over U) :=
  (SheafOfModules.overFunctor Y.ringCatSheaf U).mapIso
      (FromSections.pullbackCocycleIso q ((coordinateUnitCocycle R α).zpow (-1))
        (iSup_coordinateOpen_eq_top R α)) ≪≫
    restrictOverUnitIso Y _ (homOfLE hU)
      ((FromSections.pullbackCocycle q ((coordinateUnitCocycle R α).zpow (-1))).localIso a)

-- Evaluation crosses the native over-site frame and original section-module aliases.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem factorFrame_coefficient_generator {α : Type u}
    (q : Y ⟶ ProjectiveSpace R α) (a : α) {U V : Y.Opens}
    (hU : U ≤ q ⁻¹ᵁ coordinateOpen R α a) (hV : V ≤ U) :
    chartSectionEquiv Y ((Scheme.Modules.pullback q).obj (twistingSheaf R α 1)) U
      (factorFrame q a hU) V hV
        (((coordinateUnitCocycle R α).zpow (-1)).pullbackGenerator q a (hV.trans hU)) = 1 := by
  let c := FromSections.pullbackCocycle q ((coordinateUnitCocycle R α).zpow (-1))
  change c.localSectionsEquiv a (hV.trans hU)
      ((FromSections.pullbackCocycleIso q ((coordinateUnitCocycle R α).zpow (-1))
        (iSup_coordinateOpen_eq_top R α)).hom.val.app (op V)
          (((coordinateUnitCocycle R α).zpow (-1)).pullbackGenerator q a (hV.trans hU))) = 1
  rw [FromSections.pullbackCocycleIso, UnitCocycle.pullbackIso_hom_pullbackGenerator,
    UnitCocycle.localSectionsEquiv_generator]
  exact hV.trans hU

/-- The actual tensor frame on the common chart. -/
def frame (a : ι × κ) :
    (tensorModule f g).over (sourceOpen f g a) ≅
      SheafOfModules.unit (Y.ringCatSheaf.over (sourceOpen f g a)) :=
  tensorOverTrivialization Y _ _ _ (factorFrame f a.1 inf_le_left)
    (factorFrame g a.2 inf_le_right)

-- The tensor-frame coefficient is evaluated in the same original section-module carrier.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem coefficient_generator (a : ι × κ) {V : Y.Opens} (ha : V ≤ sourceOpen f g a) :
    chartSectionEquiv Y (tensorModule f g) (sourceOpen f g a) (frame f g a) V ha
      (generator f g a ha) = 1 := by
  rw [generator, frame, tensorOverTrivialization_coefficient,
    factorFrame_coefficient_generator, factorFrame_coefficient_generator, mul_one]

/-- The actual tensor generators glue to a morphism from the pulled twisting cocycle. -/
def hom : (cocycle f g).sheaf ⟶ tensorModule f g :=
  (cocycle f g).homOfLocalSections (tensorModule f g) (iSup_sourceOpen_eq_top f g)
    (fun a => generator f g a le_rfl) (by
      intro a b V ha hb
      rw [generator_restrict, generator_restrict]
      exact generator_transition f g a b ha hb)

-- The whole over-site morphism is compared through its native section-module evaluation.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem hom_over (a : ι × κ) :
    (SheafOfModules.overFunctor Y.ringCatSheaf (sourceOpen f g a)).map (hom f g) =
      ((cocycle f g).localIso a).hom ≫ (frame f g a).inv := by
  apply SheafOfModules.hom_ext
  ext V s
  have h := (cocycle f g).homOfLocalSections_apply (tensorModule f g)
    (iSup_sourceOpen_eq_top f g) (fun b => generator f g b le_rfl)
    (by
      intro b c W hb hc
      rw [generator_restrict, generator_restrict]
      exact generator_transition f g b c hb hc)
    a V.unop.left (leOfHom V.unop.hom) s
  change (hom f g).val.app (op V.unop.left) s = _
  refine h.trans ?_
  rw [generator_restrict]
  apply (chartSectionEquiv Y (tensorModule f g) (sourceOpen f g a) (frame f g a)
    V.unop.left (leOfHom V.unop.hom)).injective
  rw [_root_.map_smul, coefficient_generator, smul_eq_mul, mul_one]
  exact ((chartSectionEquiv Y (tensorModule f g) (sourceOpen f g a) (frame f g a)
    V.unop.left (leOfHom V.unop.hom)).apply_symm_apply _).symm

instance hom_isIso : IsIso (hom f g) := by
  apply Scheme.Modules.Pullback.OpenRestriction.isIso_of_local_restrict
  intro x
  obtain ⟨a, ha⟩ := Opens.mem_iSup.mp
    (show x ∈ iSup (sourceOpen f g) by rw [iSup_sourceOpen_eq_top]; trivial)
  refine ⟨sourceOpen f g a, ha, ?_⟩
  have : IsIso ((SheafOfModules.overFunctor Y.ringCatSheaf (sourceOpen f g a)).map
      (hom f g)) := by
    rw [hom_over]
    infer_instance
  exact (NatIso.isIso_map_iff (overFunctorEquiv (sourceOpen f g a)) (hom f g)).mp
    (inferInstanceAs (IsIso ((overEquiv (sourceOpen f g a)).functor.map
      ((SheafOfModules.overFunctor Y.ringCatSheaf (sourceOpen f g a)).map (hom f g)))))

end LineBundleComparison

/-- The original Segre map pulls the original O(1) back to the actual tensor
of the two original pulled-back O(1)'s. -/
def twistingPullbackIso :
    (Scheme.Modules.pullback (map f g)).obj (twistingSheaf R (ι × κ) 1) ≅
      tensorSheaf Y ((Scheme.Modules.pullback f).obj (twistingSheaf R ι 1))
        ((Scheme.Modules.pullback g).obj (twistingSheaf R κ 1)) :=
  ((coordinateUnitCocycle R (ι × κ)).zpow (-1)).pullbackIso (map f g)
    (LineBundleComparison.cocycle f g) (map_preimage_coordinateOpen f g)
    (UnitCocycle.transitionPullback_pullbackCocycle _ _ _)
    (iSup_coordinateOpen_eq_top R (ι × κ)) ≪≫ asIso (LineBundleComparison.hom f g)

/-- The same tensor comparison on native Picard classes. -/
theorem pullbackClass_twisting_one :
    pullbackClass (map f g) (classOf _ (twistingLineBundle R (ι × κ) 1)) =
      pullbackClass f (classOf _ (twistingLineBundle R ι 1)) +
        pullbackClass g (classOf _ (twistingLineBundle R κ 1)) :=
  (class_eq_iff Y _ _).mpr ⟨twistingPullbackIso f g⟩

/-- Arbitrary further pullback retains the same Segre tensor-class law,
including a projection in an actual base-change square. -/
theorem pullbackClass_twisting_one_comp {Z : Scheme.{u}} (q : Z ⟶ Y) :
    pullbackClass (q ≫ map f g) (classOf _ (twistingLineBundle R (ι × κ) 1)) =
      pullbackClass (q ≫ f) (classOf _ (twistingLineBundle R ι 1)) +
        pullbackClass (q ≫ g) (classOf _ (twistingLineBundle R κ 1)) := by
  rw [pullbackClass_comp, pullbackClass_twisting_one, PullbackTensor.Local.pullbackClass_add,
    pullbackClass_comp, pullbackClass_comp]

/-- The universal original Segre closed immersion retains the tensor O(1) law. -/
def embeddingTwistingPullbackIso :
    (Scheme.Modules.pullback (embedding R ι κ)).obj (twistingSheaf R (ι × κ) 1) ≅
      tensorSheaf (product R ι κ)
        ((Scheme.Modules.pullback (first R ι κ)).obj (twistingSheaf R ι 1))
        ((Scheme.Modules.pullback (second R ι κ)).obj (twistingSheaf R κ 1)) :=
  twistingPullbackIso (first R ι κ) (second R ι κ)

end AlgebraicGeometry.ProjectiveSpace.Segre
