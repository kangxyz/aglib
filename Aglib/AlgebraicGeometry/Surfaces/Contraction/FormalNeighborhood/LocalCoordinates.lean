/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Contraction.PointIdeal
public import Aglib.AlgebraicGeometry.Surfaces.Contraction.FormalNeighborhood.Support
public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.Affine
public import Aglib.AlgebraicGeometry.Morphisms.Proper.AffineStein
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.FlatMorphism
public import Aglib.AlgebraicGeometry.Stalk.FlatBaseChange
public import Aglib.RingTheory.MvPolynomial.DegreeOne
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# The original local source and selected exceptional coordinates

The local source is the original local-spectrum pullback. The exceptional lift retains the full
original residue field, ideal and conormal comparison. The selected coordinate sections and their
fibre epimorphy retain the original first-order lift equations.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.Surfaces.Contraction.FormalNeighborhood

universe u v w t

section OriginalConormalPair

open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules.Invertible

variable {A : Type u} [CommRing A] {ι : Type u} {X : Scheme.{u}}
  {p : X ⟶ ProjectiveSpace A ι} {k : Type u} [CommRing k]
  (i : ProjectiveSpace k (ULift.{u} (Fin 2)) ⟶ X) [IsClosedImmersion i]
  (hI : IsLocallyRankOne X (Hom.idealModule i)) (H : LineBundle X)
  {eP : H.val ≅ (Scheme.Modules.pullback p).obj (twistingSheaf A ι 1)} (d : ℕ)
  {n : ℕ} {hn : 1 ≤ n}
  (F : CartierProjectivePresentation p i hI H eP d n hn)
  (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
    twistingSheaf k (ULift.{u} (Fin 2)) 1)
  (eH : (Scheme.Modules.pullback i).obj H.val ≅
    twistingSheaf k (ULift.{u} (Fin 2)) (d : ℤ))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original selected Cartier multiplier identifies the actual conormal
line with the actual first-order O(1) comparison. -/
def conormalComparison (hn2 : 2 ≤ n * d) (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀))) :
    (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
      twistingSheaf k (ULift.{u} (Fin 2)) 1 := by
  let _ : IsIso ((Scheme.Modules.pullback i).map (F.pointCartierMultiply hn2 j₀)) :=
    F.pointCartierMultiply_pullback_isIso eI eH hn2 j₀ h₀
  exact asIso ((Scheme.Modules.pullback i).map (F.pointCartierMultiply hn2 j₀)) ≪≫
    firstOrderRestrictionIso i hI H d eI eH n hn2

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The comparison uses the original pulled multiplier and original restriction
map, with no independently supplied conormal-generation witness. -/
theorem conormalComparison_hom (hn2 : 2 ≤ n * d) (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀))) :
    (conormalComparison i hI H d F eI eH hn2 j₀ h₀).hom =
      (Scheme.Modules.pullback i).map (F.pointCartierMultiply hn2 j₀) ≫
        (firstOrderRestrictionIso i hI H d eI eH n hn2).hom := rfl

end OriginalConormalPair

section OriginalLocalPoint

variable {k : Type u} [Field k] {Z : Scheme.{u}}
  (c : Spec (.of k) ⟶ Z) [IsClosedImmersion c]

/-- The actual image of the original field point. -/
abbrev imagePoint : Z := c (IsLocalRing.closedPoint k)

/-- The original image-local ring, without a chosen replacement or coefficient field. -/
abbrev pointLocalRing : CommRingCat.{u} := Z.presheaf.stalk (imagePoint c)

/-- The original image-local maximal ideal is the formal-neighborhood base ideal. -/
abbrev pointMaximalIdeal : Ideal (pointLocalRing c) :=
  IsLocalRing.maximalIdeal (pointLocalRing c)

/-- The original closed-point stalk map, followed by the native field-stalk comparison. -/
abbrev pointResidueHom : pointLocalRing c →+* k := (Scheme.stalkClosedPointTo c).hom

/-- Original residue coefficients lift through the actual closed-point stalk map. -/
theorem pointResidueHom_surjective : Function.Surjective (pointResidueHom c) := by
  exact (ConcreteCategory.bijective_of_isIso
    (AlgebraicGeometry.stalkClosedPointIso (.of k)).hom).surjective.comp
    (c.stalkMap_surjective (IsLocalRing.closedPoint k))

/-- Its kernel is precisely the original maximal ideal, without a coefficient-field choice. -/
theorem ker_pointResidueHom : RingHom.ker (pointResidueHom c) = pointMaximalIdeal c :=
  IsLocalRing.ker_eq_maximalIdeal _ (pointResidueHom_surjective c)

omit [IsClosedImmersion c] in
/-- The original field point factors through its actual local spectrum. -/
@[reassoc]
theorem pointResidueHom_fromSpecStalk :
    Spec.map (CommRingCat.ofHom (pointResidueHom c)) ≫ Z.fromSpecStalk (imagePoint c) = c :=
  Scheme.Spec_stalkClosedPointTo_fromSpecStalk c

end OriginalLocalPoint

section OriginalLocalSource

variable {X Z : Scheme.{u}} (f : X ⟶ Z) (z : Z)

/-- The actual proper source over the original image-local spectrum. -/
abbrev localSource : Scheme.{u} := pullback f (Z.fromSpecStalk z)

/-- Its original structural map is the second projection of the native pullback. -/
abbrev localSourceMap : localSource f z ⟶ Spec (Z.presheaf.stalk z) :=
  pullback.snd f (Z.fromSpecStalk z)

/-- The literal structural coefficient map on this original local source. -/
abbrev localStructureHom : Z.presheaf.stalk z →+* Γ(localSource f z, ⊤) :=
  affineFormalFunctionsScalar (localSourceMap f z)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Proper H0 finiteness applies to the literal original local structural map. -/
theorem localStructureHom_finite [IsLocallyNoetherian Z] [IsProper f] :
    (localStructureHom f z).Finite := by
  let _ : IsNoetherianRing (Z.presheaf.stalk z) := inferInstance
  exact Scheme.AffineStein.finite_structuralCoefficients
    (Z.presheaf.stalk z) (localSourceMap f z)

/-- Flat local-spectrum base change retains injectivity of the original structural map. -/
theorem localStructureHom_injective [IsSchemeTheoreticallyDominant f]
    [QuasiCompact f] : Function.Injective (localStructureHom f z) := by
  let _ : Flat (Z.fromSpecStalk z) := Scheme.fromSpecStalk_flat Z z
  let _ : IsSchemeTheoreticallyDominant (localSourceMap f z) := inferInstance
  exact ((localSourceMap f z).app_injective ⊤).comp
    (Scheme.ΓSpecIso (Z.presheaf.stalk z)).commRingCatIsoToRingEquiv.symm.injective

end OriginalLocalSource

section OriginalLocalExceptional

open AlgebraicGeometry.Scheme.Modules.Invertible

variable {k : Type u} [Field k] {C X Z : Scheme.{u}}
  (c : Spec (.of k) ⟶ Z) [IsClosedImmersion c]
  (f : X ⟶ Z) (i : C ⟶ X) [IsClosedImmersion i]
  (a : C ⟶ Spec (.of k)) (w : a ≫ c = i ≫ f)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original exceptional scheme maps to the original local-spectrum
source by the native pullback lift, retaining the original residue map. -/
def localExceptional : C ⟶ localSource f (imagePoint c) :=
  pullback.lift i (a ≫ Spec.map (Scheme.stalkClosedPointTo c))
    ((w.symm.trans (congrArg (fun h : Spec (.of k) ⟶ Z => a ≫ h)
      (Scheme.Spec_stalkClosedPointTo_fromSpecStalk c).symm)).trans
        (Category.assoc a (Spec.map (Scheme.stalkClosedPointTo c))
          (Z.fromSpecStalk (imagePoint c))).symm)

omit [IsClosedImmersion c] [IsClosedImmersion i] in
/-- The original exceptional map is exactly the first projection of its local lift. -/
@[reassoc]
theorem localExceptional_fst :
    localExceptional c f i a w ≫ pullback.fst f (Z.fromSpecStalk (imagePoint c)) = i :=
  pullback.lift_fst _ _ _

omit [IsClosedImmersion c] [IsClosedImmersion i] in
/-- The second projection retains the original map to the full residue field. -/
@[reassoc]
theorem localExceptional_snd :
    localExceptional c f i a w ≫ localSourceMap f (imagePoint c) =
      a ≫ Spec.map (Scheme.stalkClosedPointTo c) :=
  pullback.lift_snd _ _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The already-proved original pulled point ideal makes this very same
exceptional scheme the actual closed fibre of the local-spectrum source. -/
theorem localExceptional_isPullback
    (hker : c.ker.comap f = i.ker) :
    IsPullback (localExceptional c f i a w) a (localSourceMap f (imagePoint c))
      (Spec.map (Scheme.stalkClosedPointTo c)) := by
  have h0 : IsPullback i a f c :=
    AlgebraicGeometry.isPullback_of_isClosedImmersion i c a f w.symm hker
  apply IsPullback.of_right (h₁₁ := localExceptional c f i a w)
    (h₁₂ := pullback.fst f (Z.fromSpecStalk (imagePoint c)))
    (h₂₂ := Z.fromSpecStalk (imagePoint c)) ?_
    (localExceptional_snd c f i a w)
    (IsPullback.of_hasPullback f (Z.fromSpecStalk (imagePoint c)))
  have hβ : Spec.map (Scheme.stalkClosedPointTo c) ≫
      Z.fromSpecStalk (imagePoint c) = c := Scheme.Spec_stalkClosedPointTo_fromSpecStalk c
  have h1 : IsPullback i a f (Spec.map (Scheme.stalkClosedPointTo c) ≫
      Z.fromSpecStalk (imagePoint c)) :=
    Eq.mp (congrArg (fun q : Spec (.of k) ⟶ Z => IsPullback i a f q) hβ.symm) h0
  exact Eq.mp (congrArg (fun q : C ⟶ X => IsPullback q a f
    (Spec.map (Scheme.stalkClosedPointTo c) ≫ Z.fromSpecStalk (imagePoint c)))
      (localExceptional_fst c f i a w).symm) h1

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual local exceptional lift remains a closed immersion, through
its original residue-fibre square. -/
theorem localExceptional_isClosedImmersion (hker : c.ker.comap f = i.ker) :
    IsClosedImmersion (localExceptional c f i a w) := by
  let _ : IsClosedImmersion (Spec.map (Scheme.stalkClosedPointTo c)) :=
    IsClosedImmersion.spec_of_surjective _ (pointResidueHom_surjective c)
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (localExceptional_isPullback c f i a w hker).flip inferInstance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The full original local maximal ideal pulls back to this ORIGINAL local
exceptional kernel, without replacing it by the two chosen first-order elements. -/
theorem localExceptional_pointIdeal_comap (hker : c.ker.comap f = i.ker) :
    (Spec.map (Scheme.stalkClosedPointTo c)).ker.comap
        (localSourceMap f (imagePoint c)) =
      (localExceptional c f i a w).ker := by
  let j := localExceptional c f i a w
  let b := localSourceMap f (imagePoint c)
  let q := Spec.map (Scheme.stalkClosedPointTo c)
  let _ : IsClosedImmersion q :=
    IsClosedImmersion.spec_of_surjective _ (pointResidueHom_surjective c)
  let _ : IsClosedImmersion j := localExceptional_isClosedImmersion c f i a w hker
  let hw : a ≫ q = j ≫ b := (localExceptional_snd c f i a w).symm
  let _ : Epi (Hom.idealPullbackMap q j b a hw) :=
    Hom.idealPullbackMap_epi_of_isPullback q j b a hw
      (localExceptional_isPullback c f i a w hker).flip
  exact Hom.ker_comap_eq_of_idealPullbackMap_epi q j b a hw

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original exceptional ideal comparison along the actual flat local
base change is an isomorphism of the original ideal modules. -/
def localExceptionalIdealIso :
    (Scheme.Modules.pullback (pullback.fst f (Z.fromSpecStalk (imagePoint c)))).obj
        (Hom.idealModule i) ≅
      Hom.idealModule (localExceptional c f i a w) := by
  let j := localExceptional c f i a w
  let p := pullback.fst f (Z.fromSpecStalk (imagePoint c))
  let _ : Flat (Z.fromSpecStalk (imagePoint c)) := Scheme.fromSpecStalk_flat Z (imagePoint c)
  let _ : Flat p := inferInstance
  let hw : (𝟙 C) ≫ i = j ≫ p := by
    rw [Category.id_comp, localExceptional_fst]
  have hpb : IsPullback (𝟙 C) j i p :=
    IsPullback.of_horiz_isIso_mono ⟨hw⟩
  let _ : IsIso (Hom.idealPullbackMap i j p (𝟙 C) hw) :=
    Hom.idealPullbackMap_isIso_of_flat i p j (𝟙 C) hw hpb
  exact asIso (Hom.idealPullbackMap i j p (𝟙 C) hw)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [IsClosedImmersion c] in
/-- Local rank one of the original exceptional ideal survives on the
original proper local-spectrum source. -/
theorem localExceptional_locallyRankOne
    (hI : IsLocallyRankOne X (Hom.idealModule i)) :
    IsLocallyRankOne (localSource f (imagePoint c))
      (Hom.idealModule (localExceptional c f i a w)) :=
  isLocallyRankOne_of_iso _ (localExceptionalIdealIso c f i a w)
    (pullback_locallyRankOne _ _ hI)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The local conormal comparison uses the same exceptional scheme and the
original pulled-ideal isomorphism; it introduces no new line-bundle datum. -/
def localExceptionalConormalIso {N : C.Modules}
    (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅ N) :
    (Scheme.Modules.pullback (localExceptional c f i a w)).obj
        (Hom.idealModule (localExceptional c f i a w)) ≅ N :=
  (Scheme.Modules.pullback (localExceptional c f i a w)).mapIso
      (localExceptionalIdealIso c f i a w).symm ≪≫
    (Scheme.Modules.pullbackComp (localExceptional c f i a w)
      (pullback.fst f (Z.fromSpecStalk (imagePoint c)))).app (Hom.idealModule i) ≪≫
    (Scheme.Modules.pullbackCongr (localExceptional_fst c f i a w)).app
      (Hom.idealModule i) ≪≫ eI

end OriginalLocalExceptional

section OriginalSelectedCoordinateRow

open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules.Invertible

variable {A : Type u} [CommRing A] {ι : Type u} {X : Scheme.{u}}
  {p : X ⟶ ProjectiveSpace A ι} {k : Type u} [Field k]
  (i : ProjectiveSpace k (ULift.{u} (Fin 2)) ⟶ X) [IsClosedImmersion i]
  (hI : IsLocallyRankOne X (Hom.idealModule i)) (H : LineBundle X)
  {eP : H.val ≅ (Scheme.Modules.pullback p).obj (twistingSheaf A ι 1)} (d : ℕ)
  {n : ℕ} {hn : 1 ≤ n}
  (F : CartierProjectivePresentation p i hI H eP d n hn)
  (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
    twistingSheaf k (ULift.{u} (Fin 2)) 1)
  (eH : (Scheme.Modules.pullback i).obj H.val ≅
    twistingSheaf k (ULift.{u} (Fin 2)) (d : ℤ))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The ORIGINAL selected image coordinate, as an actual pulled section of
its original exceptional ideal on a source contained in the selected chart. -/
def pulledSelectedIdealCoordinate {Y : Scheme.{u}} (g : Y ⟶ X)
    (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀)))
    (j : F.index)
    (hz : cartierResidueCoefficient i hI H d eI eH n (F.sections j) = 0)
    (hW : g ⁻¹ᵁ (F.toImage ⁻¹ᵁ F.pointChartOpen j₀) = ⊤) :
    SheafOfModules.unit Y.ringCatSheaf ⟶ (Scheme.Modules.pullback g).obj (Hom.idealModule i) :=
  pullbackSectionOn g (Hom.idealModule i) (F.toImage ⁻¹ᵁ F.pointChartOpen j₀) hW
    (F.pointChartExceptionalCoordinate eI eH (Field.toIsField k) j₀ h₀ j hz)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The pulled ORIGINAL coordinate and original Cartier multiplier give
exactly the original pulled first-order lift, with no frame or section oracle. -/
theorem pulledSelectedIdealCoordinate_comp_multiplier {Y : Scheme.{u}} (g : Y ⟶ X)
    (hn2 : 2 ≤ n * d) (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀)))
    (j : F.index)
    (hz : cartierResidueCoefficient i hI H d eI eH n (F.sections j) = 0)
    (hW : g ⁻¹ᵁ (F.toImage ⁻¹ᵁ F.pointChartOpen j₀) = ⊤)
    (t : SheafOfModules.unit X.ringCatSheaf ⟶
      (cartierPowerTwist i hI H n (n * d - 2 + 1)).val)
    (hj : F.sections j = firstOrderCartierImage i hI H d n hn2 t) :
    pulledSelectedIdealCoordinate i hI H d F eI eH g j₀ h₀ j hz hW ≫
        (Scheme.Modules.pullback g).map (F.pointCartierMultiply hn2 j₀) =
      FromSections.pullbackSection g t := by
  let W := F.toImage ⁻¹ᵁ F.pointChartOpen j₀
  let K := F.pointCartierMultiply hn2 j₀
  let v := F.pointChartExceptionalCoordinate eI eH (Field.toIsField k) j₀ h₀ j hz
  change pullbackSectionOn g (Hom.idealModule i) W hW v ≫
    (Scheme.Modules.pullback g).map K = _
  calc
    _ = pullbackSectionOn g (cartierPowerTwist i hI H n (n * d - 2 + 1)).val W hW
        (K.val.app (op W) v) := (pullbackSectionOn_map g K W hW v).symm
    _ = pullbackSectionOn g (cartierPowerTwist i hI H n (n * d - 2 + 1)).val W hW
        (t.val.app (op W) (1 : Γ(X, W))) :=
      congrArg (pullbackSectionOn g _ W hW)
        (F.pointCartierMultiply_coordinate eI eH (Field.toIsField k)
          hn2 j₀ h₀ j t hj hz)
    _ = _ := pullbackSectionOn_global g t W hW

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual selected ideal coordinates generate the ORIGINAL conormal
pullback. This is derived from the original first-order lifts and multiplier. -/
theorem pulledSelectedIdealCoordinates_epi
    (hn2 : 2 ≤ n * d) (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀)))
    (t : ULift.{u} (Fin 2) → (SheafOfModules.unit X.ringCatSheaf ⟶
      (cartierPowerTwist i hI H n (n * d - 2 + 1)).val))
    (ht : ∀ a, t a ≫ (cartierStepSequence i hI
      (cartierPowerTwist i hI H n (n * d - 2))).g =
        firstOrderQuotientCoordinate i hI H d eI eH n hn2 a)
    (q : ULift.{u} (Fin 2) → F.index)
    (hq : ∀ a, F.sections (q a) = firstOrderCartierImage i hI H d n hn2 (t a)) :
    let hz : ∀ a : ULift.{u} (Fin 2),
        cartierResidueCoefficient i hI H d eI eH n (F.sections (q a)) = 0 :=
      fun a => (congrArg (cartierResidueCoefficient i hI H d eI eH n) (hq a)).trans
        (firstOrderCartierImage_residueCoefficient i hI H d eI eH n hn2 (t a))
    let hW := F.exceptional_preimage_pointChart eI eH (Field.toIsField k) j₀ h₀
    Epi (Sigma.desc (fun a =>
      pulledSelectedIdealCoordinate i hI H d F eI eH i j₀ h₀ (q a) (hz a) hW)) := by
  let hz : ∀ a : ULift.{u} (Fin 2),
      cartierResidueCoefficient i hI H d eI eH n (F.sections (q a)) = 0 :=
    fun a => (congrArg (cartierResidueCoefficient i hI H d eI eH n) (hq a)).trans
      (firstOrderCartierImage_residueCoefficient i hI H d eI eH n hn2 (t a))
  let hW := F.exceptional_preimage_pointChart eI eH (Field.toIsField k) j₀ h₀
  let b := fun a => pulledSelectedIdealCoordinate i hI H d F eI eH i j₀ h₀ (q a) (hz a) hW
  let K := (Scheme.Modules.pullback i).map (F.pointCartierMultiply hn2 j₀)
  change Epi (Sigma.desc b)
  have hf : Sigma.desc b ≫ K = Sigma.desc (FromSections.pulledFamily i t) := by
    apply Sigma.hom_ext
    intro a
    simp only [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc]
    exact pulledSelectedIdealCoordinate_comp_multiplier i hI H d F eI eH
      i hn2 j₀ h₀ (q a) (hz a) hW (t a) (hq a)
  let _ : Epi (Sigma.desc (FromSections.pulledFamily i t)) :=
    firstOrder_lifts_pullback_epi i hI H d eI eH n hn2 t ht
  have hc : Epi (Sigma.desc b ≫ K) := by rw [hf]; infer_instance
  let _ : IsIso K := F.pointCartierMultiply_pullback_isIso eI eH hn2 j₀ h₀
  exact (epi_comp_iff_of_isIso (Sigma.desc b) K).mp hc

end OriginalSelectedCoordinateRow

section OriginalSectionComposition

open AlgebraicGeometry.ProjectiveSpace

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pullbackSection_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {M : Z.Modules} (s : SheafOfModules.unit Z.ringCatSheaf ⟶ M) :
    FromSections.pullbackSection f (FromSections.pullbackSection g s) ≫
        (Scheme.Modules.pullbackComp f g).hom.app M =
      FromSections.pullbackSection (f ≫ g) s := by
  have hu : (pullbackUnitIso f).inv ≫
        (Scheme.Modules.pullback f).map (pullbackUnitIso g).inv ≫
          (Scheme.Modules.pullbackComp f g).hom.app
            (SheafOfModules.unit Z.ringCatSheaf) = (pullbackUnitIso (f ≫ g)).inv := by
    apply (cancel_mono (pullbackUnitIso (f ≫ g)).hom).mp
    rw [Category.assoc, Category.assoc, pullbackUnitIso_comp]
    rw [← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
      Category.id_comp, Iso.inv_hom_id, Iso.inv_hom_id]
  calc
    _ = (pullbackUnitIso f).inv ≫
        (Scheme.Modules.pullback f).map (pullbackUnitIso g).inv ≫
        ((Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map s) ≫
          (Scheme.Modules.pullbackComp f g).hom.app M) := by
      simp only [FromSections.pullbackSection, Functor.map_comp, Category.assoc]
    _ = (pullbackUnitIso f).inv ≫
        (Scheme.Modules.pullback f).map (pullbackUnitIso g).inv ≫
        (Scheme.Modules.pullbackComp f g).hom.app (SheafOfModules.unit Z.ringCatSheaf) ≫
          (Scheme.Modules.pullback (f ≫ g)).map s := by
      have hn : (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map s) ≫
          (Scheme.Modules.pullbackComp f g).hom.app M =
        (Scheme.Modules.pullbackComp f g).hom.app (SheafOfModules.unit Z.ringCatSheaf) ≫
          (Scheme.Modules.pullback (f ≫ g)).map s :=
        (Scheme.Modules.pullbackComp f g).hom.naturality s
      exact congrArg (fun q => (pullbackUnitIso f).inv ≫
        (Scheme.Modules.pullback f).map (pullbackUnitIso g).inv ≫ q) hn
    _ = _ := by
      simpa only [Category.assoc, FromSections.pullbackSection] using
        congrArg (fun q => q ≫ (Scheme.Modules.pullback (f ≫ g)).map s) hu

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pullbackSection_comp_eq {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (q : X ⟶ Z) (h : f ≫ g = q)
    {M : Z.Modules} (s : SheafOfModules.unit Z.ringCatSheaf ⟶ M) :
    FromSections.pullbackSection f (FromSections.pullbackSection g s) ≫
      ((Scheme.Modules.pullbackComp f g) ≪≫ Scheme.Modules.pullbackCongr h).hom.app M =
        FromSections.pullbackSection q s := by
  change FromSections.pullbackSection f (FromSections.pullbackSection g s) ≫
    ((Scheme.Modules.pullbackComp f g).hom.app M ≫
      (Scheme.Modules.pullbackCongr h).hom.app M) = _
  rw [← Category.assoc, pullbackSection_comp]
  subst q
  simp [Scheme.Modules.pullbackCongr]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original open-section pullback into the structure module is its actual
section-ring pullback after the canonical unit comparison. -/
theorem pullbackSectionOn_unit_apply {X Y : Scheme.{u}} (f : Y ⟶ X)
    (U : X.Opens) (h : f ⁻¹ᵁ U = ⊤) (m : Γ(X, U)) :
    (pullbackSectionOn f (SheafOfModules.unit X.ringCatSheaf) U h m ≫
      (pullbackUnitIso f).hom).val.app (op ⊤) (1 : Γ(Y, ⊤)) =
        f.appLE U ⊤ h.ge m := by
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let N := (Scheme.Modules.pullback f).obj O
  let u := (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app O
  have hu := pullbackUnitIso_homEquiv f
  rw [Adjunction.homEquiv_unit] at hu
  have hv := congrArg (fun q => q.val.app (op U) m) hu
  change (pullbackUnitIso f).hom.val.app (op (f ⁻¹ᵁ U))
    (u.val.app (op U) m) = f.app U m at hv
  have hn := PresheafOfModules.naturality_apply (pullbackUnitIso f).hom.val
    (eqToHom h.symm).op (u.val.app (op U) m)
  change (pullbackUnitIso f).hom.val.app (op ⊤)
      (N.presheaf.map (eqToHom h.symm).op (u.val.app (op U) m)) =
    (Y.presheaf.map (eqToHom h.symm).op).hom
      ((pullbackUnitIso f).hom.val.app (op (f ⁻¹ᵁ U)) (u.val.app (op U) m)) at hn
  change (pullbackUnitIso f).hom.val.app (op ⊤)
      (unitHomGlobalSectionsEquiv Y N ((unitHomGlobalSectionsEquiv Y N).symm
        (N.presheaf.map (eqToHom h.symm).op (u.val.app (op U) m)))) = _
  rw [Equiv.apply_symm_apply]
  exact hn.trans (congrArg (Y.presheaf.map (eqToHom h.symm).op).hom hv)

end OriginalSectionComposition

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original flat ideal comparison retains the literal inclusion into the
original local source's structure module. -/
theorem localExceptionalIdealIso_hom_inclusion
    {k : Type u} [Field k] {C X Z : Scheme.{u}} (c : Spec (.of k) ⟶ Z)
    (f : X ⟶ Z) (i : C ⟶ X) [IsClosedImmersion i]
    (a : C ⟶ Spec (.of k)) (w : a ≫ c = i ≫ f) :
    (localExceptionalIdealIso c f i a w).hom ≫
        Hom.idealInclusion (localExceptional c f i a w) =
      (Scheme.Modules.pullback (pullback.fst f (Z.fromSpecStalk (imagePoint c)))).map
          (Hom.idealInclusion i) ≫
        (pullbackUnitIso (pullback.fst f (Z.fromSpecStalk (imagePoint c)))).hom := by
  exact Hom.idealPullbackMap_inclusion i (localExceptional c f i a w)
    (pullback.fst f (Z.fromSpecStalk (imagePoint c))) (𝟙 C)
    (by rw [Category.id_comp, localExceptional_fst])

section OriginalLocalSelectedPair

open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules.Invertible

variable {A : Type u} [CommRing A] {ι : Type u} {X : Scheme.{u}}
  {p : X ⟶ ProjectiveSpace A ι} {k : Type u} [Field k]
  (i : ProjectiveSpace k (ULift.{u} (Fin 2)) ⟶ X) [IsClosedImmersion i]
  (hI : IsLocallyRankOne X (Hom.idealModule i)) (H : LineBundle X)
  {eP : H.val ≅ (Scheme.Modules.pullback p).obj (twistingSheaf A ι 1)} (d : ℕ)
  {n : ℕ} {hn : 1 ≤ n}
  (F : CartierProjectivePresentation p i hI H eP d n hn)
  (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
    twistingSheaf k (ULift.{u} (Fin 2)) 1)
  (eH : (Scheme.Modules.pullback i).obj H.val ≅
    twistingSheaf k (ULift.{u} (Fin 2)) (d : ℤ))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- On any original factorization of the exceptional immersion, the actual
selected-coordinate row pulls back epimorphically, by its original multiplier equations. -/
theorem pulledSelectedIdealCoordinates_pullback_epi
    {Y : Scheme.{u}} (g : Y ⟶ X)
    (j : ProjectiveSpace k (ULift.{u} (Fin 2)) ⟶ Y) (hw : j ≫ g = i)
    (hn2 : 2 ≤ n * d) (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀)))
    (hW : g ⁻¹ᵁ (F.toImage ⁻¹ᵁ F.pointChartOpen j₀) = ⊤)
    (t : ULift.{u} (Fin 2) → (SheafOfModules.unit X.ringCatSheaf ⟶
      (cartierPowerTwist i hI H n (n * d - 2 + 1)).val))
    (ht : ∀ a, t a ≫ (cartierStepSequence i hI
      (cartierPowerTwist i hI H n (n * d - 2))).g =
        firstOrderQuotientCoordinate i hI H d eI eH n hn2 a)
    (q : ULift.{u} (Fin 2) → F.index)
    (hq : ∀ a, F.sections (q a) = firstOrderCartierImage i hI H d n hn2 (t a)) :
    let hz : ∀ a : ULift.{u} (Fin 2),
        cartierResidueCoefficient i hI H d eI eH n (F.sections (q a)) = 0 :=
      fun a => (congrArg (cartierResidueCoefficient i hI H d eI eH n) (hq a)).trans
        (firstOrderCartierImage_residueCoefficient i hI H d eI eH n hn2 (t a))
    Epi ((Scheme.Modules.pullback j).map (Sigma.desc (fun a =>
      pulledSelectedIdealCoordinate i hI H d F eI eH g j₀ h₀ (q a) (hz a) hW))) := by
  let hz : ∀ a : ULift.{u} (Fin 2),
      cartierResidueCoefficient i hI H d eI eH n (F.sections (q a)) = 0 :=
    fun a => (congrArg (cartierResidueCoefficient i hI H d eI eH n) (hq a)).trans
      (firstOrderCartierImage_residueCoefficient i hI H d eI eH n hn2 (t a))
  let hE := F.exceptional_preimage_pointChart eI eH (Field.toIsField k) j₀ h₀
  let s := fun a => pulledSelectedIdealCoordinate i hI H d F eI eH g
    j₀ h₀ (q a) (hz a) hW
  let b := fun a => pulledSelectedIdealCoordinate i hI H d F eI eH i
    j₀ h₀ (q a) (hz a) hE
  let e := (Scheme.Modules.pullbackComp j g) ≪≫ Scheme.Modules.pullbackCongr hw
  let K := F.pointCartierMultiply hn2 j₀
  let Ki := (Scheme.Modules.pullback i).map K
  let _ : IsIso Ki := F.pointCartierMultiply_pullback_isIso eI eH hn2 j₀ h₀
  have he (a : ULift.{u} (Fin 2)) :
      FromSections.pullbackSection j (s a) ≫ e.hom.app (Hom.idealModule i) = b a := by
    apply (cancel_mono Ki).mp
    calc
      _ = FromSections.pullbackSection j (s a) ≫
          (Scheme.Modules.pullback j).map ((Scheme.Modules.pullback g).map K) ≫
            e.hom.app _ := by
        rw [Category.assoc, ← e.hom.naturality K]
        rfl
      _ = FromSections.pullbackSection j (s a ≫ (Scheme.Modules.pullback g).map K) ≫
          e.hom.app _ := by
        simp only [FromSections.pullbackSection, Functor.map_comp, Category.assoc]
      _ = FromSections.pullbackSection j (FromSections.pullbackSection g (t a)) ≫
          e.hom.app _ := by
        rw [pulledSelectedIdealCoordinate_comp_multiplier i hI H d F eI eH
          g hn2 j₀ h₀ (q a) (hz a) hW (t a) (hq a)]
      _ = FromSections.pullbackSection i (t a) := pullbackSection_comp_eq j g i hw (t a)
      _ = b a ≫ Ki := (pulledSelectedIdealCoordinate_comp_multiplier i hI H d F eI eH
        i hn2 j₀ h₀ (q a) (hz a) hE (t a) (hq a)).symm
  have hdesc : Sigma.desc (FromSections.pulledFamily j s) ≫
      e.hom.app (Hom.idealModule i) = Sigma.desc b := by
    apply Sigma.hom_ext
    intro a
    simpa only [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc, FromSections.pulledFamily] using he a
  let _ : Epi (Sigma.desc b) :=
    pulledSelectedIdealCoordinates_epi i hI H d F eI eH hn2 j₀ h₀ t ht q hq
  let _ : Epi (Sigma.desc (FromSections.pulledFamily j s)) := by
    apply (epi_comp_iff_of_isIso _ (e.hom.app (Hom.idealModule i))).mp
    rw [hdesc]
    infer_instance
  change Epi ((Scheme.Modules.pullback j).map (Sigma.desc s))
  exact epi_of_epi_fac (f := (pullbackFreeIso j (ULift.{u} (Fin 2))).inv)
    (h := Sigma.desc (FromSections.pulledFamily j s))
    (FromSections.pulledFamily_desc j s).symm

/-- The original closed image point belongs to the original selected affine chart. -/
theorem imagePoint_mem_pointChart (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀))) :
    imagePoint (F.residueToImage eI eH j₀ h₀) ∈ F.pointChartOpen j₀ := by
  change IsLocalRing.closedPoint k ∈
    F.residueToImage eI eH j₀ h₀ ⁻¹ᵁ F.pointChartOpen j₀
  rw [F.residueToImage_preimage_pointChart eI eH (Field.toIsField k) j₀ h₀]
  trivial

/-- The actual image-local source lies wholly over the original selected chart. -/
theorem localSource_preimage_pointChart (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀))) :
    let c := F.residueToImage eI eH j₀ h₀
    (pullback.fst F.toImage (F.image.fromSpecStalk (imagePoint c))) ⁻¹ᵁ
      (F.toImage ⁻¹ᵁ F.pointChartOpen j₀) = ⊤ := by
  let c := F.residueToImage eI eH j₀ h₀
  have hg : F.image.fromSpecStalk (imagePoint c) ⁻¹ᵁ F.pointChartOpen j₀ = ⊤ :=
    Scheme.preimage_eq_top_of_closedPoint_mem _ (by
      simpa only [Scheme.fromSpecStalk_closedPoint] using
        imagePoint_mem_pointChart i hI H d F eI eH j₀ h₀)
  change (pullback.fst F.toImage (F.image.fromSpecStalk (imagePoint c))) ⁻¹ᵁ
    (F.toImage ⁻¹ᵁ F.pointChartOpen j₀) = ⊤
  rw [← Scheme.Hom.comp_preimage, pullback.condition, Scheme.Hom.comp_preimage,
    hg, Scheme.Hom.preimage_top]

/-- The original selected coordinate viewed in the original image-local ring. -/
def selectedLocalCoordinate (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀)))
    (j : F.index) : pointLocalRing (F.residueToImage eI eH j₀ h₀) :=
  F.image.presheaf.germ (F.pointChartOpen j₀) _
    (imagePoint_mem_pointChart i hI H d F eI eH j₀ h₀) (F.pointChartCoordinate j₀ j)

/-- The actual local exceptional immersion for the same original image and field point. -/
abbrev selectedLocalExceptional (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀))) :=
  localExceptional (F.residueToImage eI eH j₀ h₀) F.toImage i
    (toSpec k (ULift.{u} (Fin 2))) (F.exceptional_toImage_eq eI eH j₀ h₀).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original selected kernel section on the local source, transported by the
actual flat ideal comparison to the original local exceptional ideal. -/
def selectedLocalIdealCoordinate (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀)))
    (j : F.index)
    (hz : cartierResidueCoefficient i hI H d eI eH n (F.sections j) = 0) :
    SheafOfModules.unit (localSource F.toImage
      (imagePoint (F.residueToImage eI eH j₀ h₀))).ringCatSheaf ⟶
        Hom.idealModule (selectedLocalExceptional i hI H d F eI eH j₀ h₀) :=
  pulledSelectedIdealCoordinate i hI H d F eI eH
    (pullback.fst F.toImage (F.image.fromSpecStalk
      (imagePoint (F.residueToImage eI eH j₀ h₀))))
    j₀ h₀ j hz (localSource_preimage_pointChart i hI H d F eI eH j₀ h₀) ≫
      (localExceptionalIdealIso (F.residueToImage eI eH j₀ h₀) F.toImage i
        (toSpec k (ULift.{u} (Fin 2))) (F.exceptional_toImage_eq eI eH j₀ h₀).symm).hom

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Proper closed support upgrades the original selected pair to generators of
the original local exceptional ideal. Fibre generation and finiteness are derived. -/
theorem selectedLocalIdealCoordinates_epi
    [IsLocallyNoetherian F.image] [IsProper F.toImage]
    (hn2 : 2 ≤ n * d) (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀)))
    [IsClosedImmersion (F.residueToImage eI eH j₀ h₀)]
    (hker : (F.residueToImage eI eH j₀ h₀).ker.comap F.toImage = i.ker)
    (t : ULift.{u} (Fin 2) → (SheafOfModules.unit X.ringCatSheaf ⟶
      (cartierPowerTwist i hI H n (n * d - 2 + 1)).val))
    (ht : ∀ a, t a ≫ (cartierStepSequence i hI
      (cartierPowerTwist i hI H n (n * d - 2))).g =
        firstOrderQuotientCoordinate i hI H d eI eH n hn2 a)
    (q : ULift.{u} (Fin 2) → F.index)
    (hq : ∀ a, F.sections (q a) = firstOrderCartierImage i hI H d n hn2 (t a)) :
    let hz : ∀ a : ULift.{u} (Fin 2),
        cartierResidueCoefficient i hI H d eI eH n (F.sections (q a)) = 0 :=
      fun a => (congrArg (cartierResidueCoefficient i hI H d eI eH n) (hq a)).trans
        (firstOrderCartierImage_residueCoefficient i hI H d eI eH n hn2 (t a))
    Epi (Sigma.desc (fun a =>
      selectedLocalIdealCoordinate i hI H d F eI eH j₀ h₀ (q a) (hz a))) := by
  let c := F.residueToImage eI eH j₀ h₀
  let a := toSpec k (ULift.{u} (Fin 2))
  let w := (F.exceptional_toImage_eq eI eH j₀ h₀).symm
  let j := localExceptional c F.toImage i a w
  let g := pullback.fst F.toImage (F.image.fromSpecStalk (imagePoint c))
  let b := localSourceMap F.toImage (imagePoint c)
  let e := localExceptionalIdealIso c F.toImage i a w
  let hz : ∀ x : ULift.{u} (Fin 2),
      cartierResidueCoefficient i hI H d eI eH n (F.sections (q x)) = 0 :=
    fun x => (congrArg (cartierResidueCoefficient i hI H d eI eH n) (hq x)).trans
      (firstOrderCartierImage_residueCoefficient i hI H d eI eH n hn2 (t x))
  let hW := localSource_preimage_pointChart i hI H d F eI eH j₀ h₀
  let s₀ := fun x => pulledSelectedIdealCoordinate i hI H d F eI eH g
    j₀ h₀ (q x) (hz x) hW
  let s := fun x => selectedLocalIdealCoordinate i hI H d F eI eH j₀ h₀ (q x) (hz x)
  let _ : IsClosedImmersion j := localExceptional_isClosedImmersion c F.toImage i a w hker
  let hJ := localExceptional_locallyRankOne c F.toImage i a w hI
  let L := cartierIdealLineBundle j hJ
  have hs : Sigma.desc s = Sigma.desc s₀ ≫ e.hom := by
    apply Sigma.hom_ext
    intro x
    simp only [Sigma.ι_comp_desc, Sigma.ι_comp_desc_assoc]
    rfl
  let _ : Epi ((Scheme.Modules.pullback j).map (Sigma.desc s₀)) :=
    pulledSelectedIdealCoordinates_pullback_epi i hI H d F eI eH g j
      (localExceptional_fst c F.toImage i a w) hn2 j₀ h₀ hW t ht q hq
  let hEpi : Epi ((Scheme.Modules.pullback j).map (Sigma.desc s)) := by
    rw [hs, Functor.map_comp]
    infer_instance
  change Epi (Sigma.desc s)
  exact @properLocal_twoSections_epi _ _ _ _ _ _ (pointResidueHom c) _ _ _ b _ j _ a
    (localExceptional_isPullback c F.toImage i a w hker) L s hEpi

end OriginalLocalSelectedPair

section OriginalConormalBasis

open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules.Invertible

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual original exceptional coordinate sections form the native homogeneous
degree-one basis, transported through the original global-section equivalence. -/
def exceptionalCoordinateBasis (k : Type u) [CommRing k] :
    letI := Module.compHom Γ(twistingSheaf k (ULift.{u} (Fin 2)) 1, ⊤)
      (affineFormalFunctionsScalar (toSpec k (ULift.{u} (Fin 2))))
    Module.Basis (ULift.{u} (Fin 2)) k Γ(twistingSheaf k (ULift.{u} (Fin 2)) 1, ⊤) := by
  letI := Module.compHom Γ(twistingSheaf k (ULift.{u} (Fin 2)) 1, ⊤)
    (affineFormalFunctionsScalar (toSpec k (ULift.{u} (Fin 2))))
  exact (MvPolynomial.homogeneousDegreeOneBasis k (ULift.{u} (Fin 2))).map
    (homogeneousSectionLinearEquiv k (ULift.{u} (Fin 2)) ⟨0⟩ 1)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The transported basis vector is the original exceptional coordinate, with its
original coefficient field and actual section, rather than a replacement basis. -/
theorem exceptionalCoordinateBasis_apply (k : Type u) [CommRing k]
    (a : ULift.{u} (Fin 2)) :
    exceptionalCoordinateBasis k a =
      unitHomGlobalSectionsEquiv (ProjectiveSpace k (ULift.{u} (Fin 2))) _
        (exceptionalCoordinate (k := k) a) := by
  let := Module.compHom Γ(twistingSheaf k (ULift.{u} (Fin 2)) 1, ⊤)
    (affineFormalFunctionsScalar (toSpec k (ULift.{u} (Fin 2))))
  rw [exceptionalCoordinateBasis, Module.Basis.map_apply]
  refine (homogeneousSectionLinearEquiv_apply k (ULift.{u} (Fin 2)) ⟨0⟩ 1 _).trans ?_
  have ha : MvPolynomial.homogeneousDegreeOneBasis k (ULift.{u} (Fin 2)) a =
      coordinatePower k (ULift.{u} (Fin 2)) 1 a := by
    apply Subtype.ext
    simp only [MvPolynomial.homogeneousDegreeOneBasis_val, coordinatePower, pow_one]
  exact (congrArg (homogeneousSection k (ULift.{u} (Fin 2)) 1) ha).trans
    ((unitHomGlobalSectionsEquiv (ProjectiveSpace k (ULift.{u} (Fin 2)))
      (twistingSheaf k (ULift.{u} (Fin 2)) 1)).apply_symm_apply _).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The two original exceptional coordinate sections are independent before any
dimension or regularity conclusion about a contraction image. -/
theorem exceptionalCoordinate_sections_linearIndependent (k : Type u) [CommRing k] :
    letI := Module.compHom Γ(twistingSheaf k (ULift.{u} (Fin 2)) 1, ⊤)
      (affineFormalFunctionsScalar (toSpec k (ULift.{u} (Fin 2))))
    LinearIndependent k (fun a =>
      unitHomGlobalSectionsEquiv (ProjectiveSpace k (ULift.{u} (Fin 2))) _
        (exceptionalCoordinate (k := k) a)) := by
  let := Module.compHom Γ(twistingSheaf k (ULift.{u} (Fin 2)) 1, ⊤)
    (affineFormalFunctionsScalar (toSpec k (ULift.{u} (Fin 2))))
  have h : (fun a => exceptionalCoordinateBasis k a) =
      (fun a => unitHomGlobalSectionsEquiv (ProjectiveSpace k (ULift.{u} (Fin 2))) _
        (exceptionalCoordinate (k := k) a)) := by
    funext a
    exact exceptionalCoordinateBasis_apply k a
  rw [← h]
  exact (exceptionalCoordinateBasis k).linearIndependent

variable {A : Type u} [CommRing A] {ι : Type u} {X : Scheme.{u}}
  {p : X ⟶ ProjectiveSpace A ι} {k : Type u} [Field k]
  (i : ProjectiveSpace k (ULift.{u} (Fin 2)) ⟶ X) [IsClosedImmersion i]
  (hI : IsLocallyRankOne X (Hom.idealModule i)) (H : LineBundle X)
  {eP : H.val ≅ (Scheme.Modules.pullback p).obj (twistingSheaf A ι 1)} (d : ℕ)
  {n : ℕ} {hn : 1 ≤ n}
  (F : CartierProjectivePresentation p i hI H eP d n hn)
  (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
    twistingSheaf k (ULift.{u} (Fin 2)) 1)
  (eH : (Scheme.Modules.pullback i).obj H.val ≅
    twistingSheaf k (ULift.{u} (Fin 2)) (d : ℤ))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pulledSelectedIdealCoordinate_firstOrder
    {Y : Scheme.{u}} (g : Y ⟶ X)
    (j : ProjectiveSpace k (ULift.{u} (Fin 2)) ⟶ Y) (hw : j ≫ g = i)
    (hn2 : 2 ≤ n * d) (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀)))
    (hW : g ⁻¹ᵁ (F.toImage ⁻¹ᵁ F.pointChartOpen j₀) = ⊤)
    (a : ULift.{u} (Fin 2))
    (t : SheafOfModules.unit X.ringCatSheaf ⟶
      (cartierPowerTwist i hI H n (n * d - 2 + 1)).val)
    (ht : t ≫ (cartierStepSequence i hI
      (cartierPowerTwist i hI H n (n * d - 2))).g =
        firstOrderQuotientCoordinate i hI H d eI eH n hn2 a)
    (q : F.index) (hq : F.sections q = firstOrderCartierImage i hI H d n hn2 t)
    (hz : cartierResidueCoefficient i hI H d eI eH n (F.sections q) = 0) :
    FromSections.pullbackSection j
        (pulledSelectedIdealCoordinate i hI H d F eI eH g j₀ h₀ q hz hW) ≫
      ((Scheme.Modules.pullbackComp j g) ≪≫ Scheme.Modules.pullbackCongr hw).hom.app
        (Hom.idealModule i) ≫
      (conormalComparison i hI H d F eI eH hn2 j₀ h₀).hom =
        exceptionalCoordinate (k := k) a := by
  let e := (Scheme.Modules.pullbackComp j g) ≪≫ Scheme.Modules.pullbackCongr hw
  let K := F.pointCartierMultiply hn2 j₀
  let s := pulledSelectedIdealCoordinate i hI H d F eI eH g j₀ h₀ q hz hW
  have hn : e.hom.app (Hom.idealModule i) ≫ (Scheme.Modules.pullback i).map K =
      (Scheme.Modules.pullback j).map ((Scheme.Modules.pullback g).map K) ≫ e.hom.app _ :=
    (e.hom.naturality K).symm
  have hs : FromSections.pullbackSection j s ≫ e.hom.app (Hom.idealModule i) ≫
      (Scheme.Modules.pullback i).map K = FromSections.pullbackSection i t := by
    calc
      _ = FromSections.pullbackSection j s ≫
          (Scheme.Modules.pullback j).map ((Scheme.Modules.pullback g).map K) ≫
            e.hom.app _ := congrArg (fun q => FromSections.pullbackSection j s ≫ q) hn
      _ = FromSections.pullbackSection j (s ≫ (Scheme.Modules.pullback g).map K) ≫
          e.hom.app _ := by
        simp only [FromSections.pullbackSection, Functor.map_comp, Category.assoc]
      _ = FromSections.pullbackSection j (FromSections.pullbackSection g t) ≫
          e.hom.app _ := by
        rw [pulledSelectedIdealCoordinate_comp_multiplier i hI H d F eI eH
          g hn2 j₀ h₀ q hz hW t hq]
      _ = _ := pullbackSection_comp_eq j g i hw t
  change FromSections.pullbackSection j s ≫ e.hom.app (Hom.idealModule i) ≫
    ((Scheme.Modules.pullback i).map K ≫
      (firstOrderRestrictionIso i hI H d eI eH n hn2).hom) = _
  have hh := congrArg (fun q => q ≫ (firstOrderRestrictionIso i hI H d eI eH n hn2).hom) hs
  have hh' : FromSections.pullbackSection j s ≫ e.hom.app (Hom.idealModule i) ≫
      (Scheme.Modules.pullback i).map K ≫
        (firstOrderRestrictionIso i hI H d eI eH n hn2).hom =
      FromSections.pullbackSection i t ≫
        (firstOrderRestrictionIso i hI H d eI eH n hn2).hom := by
    simpa only [Category.assoc] using hh
  exact hh'.trans
    (firstOrder_lift_pullback i hI H d eI eH n hn2 a t ht)

/-- The actual local conormal comparison inherited from the original selected
Cartier multiplier and original first-order restriction isomorphism. -/
def selectedLocalConormalIso (hn2 : 2 ≤ n * d) (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀))) :
    (Scheme.Modules.pullback (selectedLocalExceptional i hI H d F eI eH j₀ h₀)).obj
        (Hom.idealModule (selectedLocalExceptional i hI H d F eI eH j₀ h₀)) ≅
      twistingSheaf k (ULift.{u} (Fin 2)) 1 :=
  localExceptionalConormalIso (F.residueToImage eI eH j₀ h₀) F.toImage i
    (toSpec k (ULift.{u} (Fin 2))) (F.exceptional_toImage_eq eI eH j₀ h₀).symm
    (conormalComparison i hI H d F eI eH hn2 j₀ h₀)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Each original selected local ideal section has exactly its original
degree-one conormal coordinate, before any regularity or dimension conclusion. -/
theorem selectedLocalIdealCoordinate_firstOrder
    (hn2 : 2 ≤ n * d) (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀)))
    (a : ULift.{u} (Fin 2))
    (t : SheafOfModules.unit X.ringCatSheaf ⟶
      (cartierPowerTwist i hI H n (n * d - 2 + 1)).val)
    (ht : t ≫ (cartierStepSequence i hI
      (cartierPowerTwist i hI H n (n * d - 2))).g =
        firstOrderQuotientCoordinate i hI H d eI eH n hn2 a)
    (q : F.index) (hq : F.sections q = firstOrderCartierImage i hI H d n hn2 t) :
    let hz := (congrArg (cartierResidueCoefficient i hI H d eI eH n) hq).trans
      (firstOrderCartierImage_residueCoefficient i hI H d eI eH n hn2 t)
    FromSections.pullbackSection (selectedLocalExceptional i hI H d F eI eH j₀ h₀)
        (selectedLocalIdealCoordinate i hI H d F eI eH j₀ h₀ q hz) ≫
      (selectedLocalConormalIso i hI H d F eI eH hn2 j₀ h₀).hom =
        exceptionalCoordinate (k := k) a := by
  let c := F.residueToImage eI eH j₀ h₀
  let z := imagePoint c
  let j := selectedLocalExceptional i hI H d F eI eH j₀ h₀
  let g := pullback.fst F.toImage (F.image.fromSpecStalk z)
  let w := (F.exceptional_toImage_eq eI eH j₀ h₀).symm
  let e := localExceptionalIdealIso c F.toImage i (toSpec k (ULift.{u} (Fin 2))) w
  let hw := localExceptional_fst c F.toImage i (toSpec k (ULift.{u} (Fin 2))) w
  let hW := localSource_preimage_pointChart i hI H d F eI eH j₀ h₀
  let hz := (congrArg (cartierResidueCoefficient i hI H d eI eH n) hq).trans
    (firstOrderCartierImage_residueCoefficient i hI H d eI eH n hn2 t)
  let s := pulledSelectedIdealCoordinate i hI H d F eI eH g j₀ h₀ q hz hW
  let E := (Scheme.Modules.pullbackComp j g) ≪≫ Scheme.Modules.pullbackCongr hw
  let C := conormalComparison i hI H d F eI eH hn2 j₀ h₀
  have he : (Scheme.Modules.pullback j).map e.hom ≫
      (Scheme.Modules.pullback j).map e.inv = 𝟙 _ := by
    rw [← Functor.map_comp, e.hom_inv_id, CategoryTheory.Functor.map_id]
  change FromSections.pullbackSection j (s ≫ e.hom) ≫
    ((Scheme.Modules.pullback j).map e.inv ≫ E.hom.app (Hom.idealModule i) ≫ C.hom) = _
  have hp : FromSections.pullbackSection j (s ≫ e.hom) =
      FromSections.pullbackSection j s ≫ (Scheme.Modules.pullback j).map e.hom := by
    simp only [FromSections.pullbackSection, Functor.map_comp, Category.assoc]
  rw [hp, Category.assoc, ← Category.assoc ((Scheme.Modules.pullback j).map e.hom), he,
    Category.id_comp]
  exact pulledSelectedIdealCoordinate_firstOrder i hI H d F eI eH
    g j hw hn2 j₀ h₀ hW a t ht q hq hz

end OriginalConormalBasis

end AlgebraicGeometry.Scheme.Surfaces.Contraction.FormalNeighborhood
