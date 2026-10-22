/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Contraction.Complement
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.Map
public import Aglib.AlgebraicGeometry.IdealSheaf.LocallyClosed
public import Aglib.AlgebraicGeometry.Modules.ClosedImmersion.Stalk
public import Aglib.AlgebraicGeometry.Modules.Stalk.Reflection
public import Aglib.AlgebraicGeometry.Modules.Locality.Sections
public import Aglib.AlgebraicGeometry.Modules.Coherent.StalkFinite
public import Aglib.AlgebraicGeometry.Modules.ClosedImmersion.Nakayama
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.Detection

/-!
# The original image-point ideal and exceptional Cartier ideal

The same actual image point gives the original canonical ideal comparison.
Its pulled ideal is contained in the original exceptional ideal. Both ideals
restrict to the unit ideal on the original complement. Original first-order
lifts retain their actual restriction maps and the original restricted line.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible

namespace AlgebraicGeometry.Scheme.Surfaces.Contraction

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  {ι : Type u} {X : Scheme.{u}}
  (p : X ⟶ ProjectiveSpace A ι) [IsClosedImmersion p]
  {k : Type u} [CommRing k]
  (i : ProjectiveSpace k (ULift.{u} (Fin 2)) ⟶ X) [IsClosedImmersion i]
  (hI : IsLocallyRankOne X (Hom.idealModule i)) (H : LineBundle X)
  (eP : H.val ≅ (Scheme.Modules.pullback p).obj (twistingSheaf A ι 1)) (d : ℕ)

namespace CartierProjectivePresentation

variable {p i hI H eP d} {n : ℕ} {hn : 1 ≤ n}
  (F : CartierProjectivePresentation p i hI H eP d n hn)
  (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
    twistingSheaf k (ULift.{u} (Fin 2)) 1)
  (eH : (Scheme.Modules.pullback i).obj H.val ≅
    twistingSheaf k (ULift.{u} (Fin 2)) (d : ℤ))

omit [IsNoetherianRing A] [IsClosedImmersion p] in
/-- The literal native kernel ideal of the same original Spec k image point. -/
def pointIdeal (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀))) :
    F.image.IdealSheafData := (F.residueToImage eI eH j₀ h₀).ker

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original exceptional triangle gives the canonical ideal-module comparison. -/
def pointIdealPullback (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀))) :
    (Scheme.Modules.pullback F.toImage).obj
        (Hom.idealModule (F.residueToImage eI eH j₀ h₀)) ⟶ Hom.idealModule i :=
  Hom.idealPullbackMap (F.residueToImage eI eH j₀ h₀) i F.toImage
    (toSpec k (ULift.{u} (Fin 2))) (F.exceptional_toImage_eq eI eH j₀ h₀).symm

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original comparison retains literal kernel inclusions and the native unit map. -/
theorem pointIdealPullback_inclusion (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀))) :
    F.pointIdealPullback eI eH j₀ h₀ ≫ Hom.idealInclusion i =
      (Scheme.Modules.pullback F.toImage).map
        (Hom.idealInclusion (F.residueToImage eI eH j₀ h₀)) ≫
          (pullbackUnitIso F.toImage).hom :=
  Hom.idealPullbackMap_inclusion _ _ _ _ _

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The pulled original point ideal is contained in the original Cartier ideal. -/
theorem pointIdeal_comap_le (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀))) :
    (F.pointIdeal eI eH j₀ h₀).comap F.toImage ≤ i.ker := by
  apply Scheme.IdealSheafData.le_map_iff_comap_le.mp
  rw [Scheme.IdealSheafData.map_ker, F.exceptional_toImage_eq eI eH j₀ h₀]
  exact Hom.le_ker_comp _ _

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The pulled original point ideal is the unit ideal on the actual complement. -/
theorem pointIdeal_comap_complement (hk : IsField k) (hnd : 1 ≤ n * d) (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀)))
    (hρ : Function.Surjective ((cartierResidueMap i hI H d eI eH n).val.app (op ⊤))) :
    ((F.pointIdeal eI eH j₀ h₀).comap F.toImage).comap
      (exceptionalComplement i).ι = ⊤ := by
  let c := F.residueToImage eI eH j₀ h₀
  let _ : IsClosedImmersion c := F.residueToImage_isClosedImmersion eI eH hk j₀ h₀ hρ
  apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
  ext x
  constructor
  · intro hx
    rw [Scheme.IdealSheafData.support_comap, Scheme.IdealSheafData.support_comap] at hx
    change F.toImage ((exceptionalComplement i).ι x) ∈ (c.ker.support : Set F.image) at hx
    rw [Hom.support_ker] at hx
    rw [c.isClosedEmbedding.isClosed_range.closure_eq] at hx
    obtain ⟨z, hz⟩ := hx
    have hV : F.toImage ((exceptionalComplement i).ι x) ∈ F.imageComplementOpen := by
      change (exceptionalComplement i).ι x ∈ F.toImage ⁻¹ᵁ F.imageComplementOpen
      rw [F.toImage_preimage_imageComplement eI eH hnd j₀ h₀]
      exact x.property
    have hzV : z ∈ c ⁻¹ᵁ F.imageComplementOpen := by
      change c z ∈ F.imageComplementOpen
      rw [hz]
      exact hV
    rw [F.residueToImage_preimage_imageComplement eI eH hnd j₀ h₀] at hzV
    exact hzV
  · exact False.elim

end CartierProjectivePresentation

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original exceptional ideal is the unit ideal on its literal complement. -/
theorem exceptionalIdeal_comap_complement : i.ker.comap (exceptionalComplement i).ι = ⊤ := by
  apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
  ext x
  constructor
  · intro hx
    rw [Scheme.IdealSheafData.support_comap] at hx
    change (exceptionalComplement i).ι x ∈ (i.ker.support : Set X) at hx
    rw [Hom.support_ker] at hx
    rw [i.isClosedEmbedding.isClosed_range.closure_eq] at hx
    exact (x.property hx).elim
  · exact False.elim

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem idealInclusion_stalk_isIso_of_not_mem {C Y : Scheme.{u}}
    (j : C ⟶ Y) [IsClosedImmersion j] (y : Y) (hy : y ∉ Set.range j) :
    IsIso ((moduleStalk Y y).map (Hom.idealInclusion j)) := by
  let S := Hom.idealSequence j
  have hBase := Hom.idealSequence_shortExact j
  let _ : Mono S.f := hBase.mono_f
  let _ : Epi S.g := hBase.epi_g
  have hS := hBase.map (moduleStalk Y y)
  exact hS.isIso_f_iff.mpr
    (isZero_closedImmersion_moduleStalk_of_not_mem j y hy
      (SheafOfModules.unit C.ringCatSheaf))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pullback_stalk_isIso_of_stalk_isIso {Y Z : Scheme.{u}}
    (f : Y ⟶ Z) (y : Y) {M N : Z.Modules} (α : M ⟶ N)
    [IsIso ((moduleStalk Z (f y)).map α)] :
    IsIso ((moduleStalk Y y).map ((Scheme.Modules.pullback f).map α)) := by
  let e := pullbackModuleStalkIso f y
  have h : IsIso (((Scheme.Modules.pullback f ⋙ moduleStalk Y y).map α) ≫ e.hom.app N) := by
    rw [e.hom.naturality]
    change IsIso (e.hom.app M ≫
      (ModuleCat.extendScalars (f.stalkMap y).hom).map ((moduleStalk Z (f y)).map α))
    infer_instance
  exact (isIso_comp_right_iff _ (e.hom.app N)).mp h

namespace CartierProjectivePresentation

variable {p i hI H eP d} {n : ℕ} {hn : 1 ≤ n}
  (F : CartierProjectivePresentation p i hI H eP d n hn)
  (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
    twistingSheaf k (ULift.{u} (Fin 2)) 1)
  (eH : (Scheme.Modules.pullback i).obj H.val ≅
    twistingSheaf k (ULift.{u} (Fin 2)) (d : ℤ))

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Off E, the original canonical ideal comparison is an actual stalk isomorphism. -/
theorem pointIdealPullback_stalk_isIso_offExceptional
    (hk : IsField k) (hnd : 1 ≤ n * d) (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀)))
    (hρ : Function.Surjective ((cartierResidueMap i hI H d eI eH n).val.app (op ⊤)))
    (x : X) (hx : x ∉ Set.range i) :
    IsIso ((moduleStalk X x).map (F.pointIdealPullback eI eH j₀ h₀)) := by
  let f := F.toImage
  let c := F.residueToImage eI eH j₀ h₀
  let _ : IsClosedImmersion c := F.residueToImage_isClosedImmersion eI eH hk j₀ h₀ hρ
  have hnot : f x ∉ Set.range c := by
    rintro ⟨z, hz⟩
    have hV : f x ∈ F.imageComplementOpen := by
      change x ∈ F.toImage ⁻¹ᵁ F.imageComplementOpen
      rw [F.toImage_preimage_imageComplement eI eH hnd j₀ h₀]
      exact hx
    have hzV : z ∈ c ⁻¹ᵁ F.imageComplementOpen := by
      change c z ∈ F.imageComplementOpen
      rw [hz]
      exact hV
    rw [F.residueToImage_preimage_imageComplement eI eH hnd j₀ h₀] at hzV
    exact hzV
  let _ : IsIso ((moduleStalk F.image (f x)).map (Hom.idealInclusion c)) :=
    idealInclusion_stalk_isIso_of_not_mem c (f x) hnot
  let _ : IsIso ((moduleStalk X x).map
      ((Scheme.Modules.pullback f).map (Hom.idealInclusion c))) :=
    pullback_stalk_isIso_of_stalk_isIso f x (Hom.idealInclusion c)
  let _ : IsIso ((moduleStalk X x).map (Hom.idealInclusion i)) :=
    idealInclusion_stalk_isIso_of_not_mem i x hx
  have hcomp := congrArg (fun α => (moduleStalk X x).map α)
    (F.pointIdealPullback_inclusion eI eH j₀ h₀)
  simp only [Functor.map_comp] at hcomp
  have hiso : IsIso ((moduleStalk X x).map (F.pointIdealPullback eI eH j₀ h₀) ≫
      (moduleStalk X x).map (Hom.idealInclusion i)) := by
    rw [hcomp]
    infer_instance
  exact (isIso_comp_right_iff _ ((moduleStalk X x).map (Hom.idealInclusion i))).mp hiso

end CartierProjectivePresentation

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Each original exceptional coordinate is the actual generator on its own native chart. -/
theorem exceptionalCoordinate_generator (a : ULift.{u} (Fin 2)) :
    (exceptionalCoordinate (k := k) a).val.app
      (op (coordinateOpen k (ULift.{u} (Fin 2)) a))
      (1 : Γ(ProjectiveSpace k (ULift.{u} (Fin 2)),
        coordinateOpen k (ULift.{u} (Fin 2)) a)) =
      twistingGenerator k (ULift.{u} (Fin 2)) 1 a le_rfl := by
  let E := ProjectiveSpace k (ULift.{u} (Fin 2))
  let V := coordinateOpen k (ULift.{u} (Fin 2)) a
  let s := homogeneousSection k (ULift.{u} (Fin 2)) 1
    (coordinatePower k (ULift.{u} (Fin 2)) 1 a)
  have hs : (exceptionalCoordinate (k := k) a).val.app (op V) (1 : Γ(E, V)) =
      (twistingSheaf k (ULift.{u} (Fin 2)) 1).val.map (homOfLE le_top).op s :=
    (unitHomGlobalSectionsEquiv_symm_app E
      (twistingSheaf k (ULift.{u} (Fin 2)) 1) s V 1).trans (one_smul _ _)
  apply (twistingSectionsEquiv k (ULift.{u} (Fin 2)) 1 a le_rfl).injective
  rw [twistingSectionsEquiv_generator]
  exact (congrArg (twistingSectionsEquiv k (ULift.{u} (Fin 2)) 1 a le_rfl) hs).trans
    (homogeneousSection_coordinatePower_local k (ULift.{u} (Fin 2)) 1 a)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original two exceptional coordinate maps genuinely generate O_E(1). -/
theorem exceptionalCoordinate_epi : Epi (Sigma.desc (exceptionalCoordinate (k := k))) := by
  constructor
  intro N f g h
  apply twistingHom_ext_of_generator k (ULift.{u} (Fin 2))
  intro a
  have ha : exceptionalCoordinate (k := k) a ≫ f = exceptionalCoordinate (k := k) a ≫ g := by
    simpa only [Sigma.ι_comp_desc_assoc] using
      congrArg (fun q => Sigma.ι _ a ≫ q) h
  have hv := congrArg (fun q => q.val.app
    (op (coordinateOpen k (ULift.{u} (Fin 2)) a))
    (1 : Γ(ProjectiveSpace k (ULift.{u} (Fin 2)),
      coordinateOpen k (ULift.{u} (Fin 2)) a))) ha
  have hv' : f.val.app (op (coordinateOpen k (ULift.{u} (Fin 2)) a))
      ((exceptionalCoordinate (k := k) a).val.app
        (op (coordinateOpen k (ULift.{u} (Fin 2)) a))
        (1 : Γ(ProjectiveSpace k (ULift.{u} (Fin 2)),
          coordinateOpen k (ULift.{u} (Fin 2)) a))) =
      g.val.app (op (coordinateOpen k (ULift.{u} (Fin 2)) a))
        ((exceptionalCoordinate (k := k) a).val.app
          (op (coordinateOpen k (ULift.{u} (Fin 2)) a))
          (1 : Γ(ProjectiveSpace k (ULift.{u} (Fin 2)),
            coordinateOpen k (ULift.{u} (Fin 2)) a))) := hv
  exact (congrArg (f.val.app (op (coordinateOpen k (ULift.{u} (Fin 2)) a)))
    (exceptionalCoordinate_generator (k := k) a)).symm.trans
      (hv'.trans (congrArg (g.val.app (op (coordinateOpen k (ULift.{u} (Fin 2)) a)))
        (exceptionalCoordinate_generator (k := k) a)))

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Recover the actual restriction isomorphism from its original closed direct image. -/
def firstOrderRestrictionIso
    (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
      twistingSheaf k (ULift.{u} (Fin 2)) 1)
    (eH : (Scheme.Modules.pullback i).obj H.val ≅
      twistingSheaf k (ULift.{u} (Fin 2)) (d : ℤ))
    (n : ℕ) (hn2 : 2 ≤ n * d) :
    (Scheme.Modules.pullback i).obj
      (cartierPowerTwist i hI H n (n * d - 2 + 1)).val ≅
        twistingSheaf k (ULift.{u} (Fin 2)) 1 :=
  (fullyFaithfulPushforwardOfClosedImmersion i).preimageIso
    (firstOrderQuotientIso i hI H d eI eH n hn2)

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem firstOrderRestrictionIso_pushforward_hom
    (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
      twistingSheaf k (ULift.{u} (Fin 2)) 1)
    (eH : (Scheme.Modules.pullback i).obj H.val ≅
      twistingSheaf k (ULift.{u} (Fin 2)) (d : ℤ))
    (n : ℕ) (hn2 : 2 ≤ n * d) :
    (Scheme.Modules.pushforward i).map
        (firstOrderRestrictionIso i hI H d eI eH n hn2).hom =
      (firstOrderQuotientIso i hI H d eI eH n hn2).hom :=
  (fullyFaithfulPushforwardOfClosedImmersion i).map_preimage _

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Each original quotient equation identifies the actual restricted lift with
its original exceptional coordinate through the original restriction isomorphism. -/
theorem firstOrder_lift_pullback
    (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
      twistingSheaf k (ULift.{u} (Fin 2)) 1)
    (eH : (Scheme.Modules.pullback i).obj H.val ≅
      twistingSheaf k (ULift.{u} (Fin 2)) (d : ℤ))
    (n : ℕ) (hn2 : 2 ≤ n * d) (a : ULift.{u} (Fin 2))
    (t : SheafOfModules.unit X.ringCatSheaf ⟶
      (cartierPowerTwist i hI H n (n * d - 2 + 1)).val)
    (ht : t ≫ (cartierStepSequence i hI (cartierPowerTwist i hI H n (n * d - 2))).g =
      firstOrderQuotientCoordinate i hI H d eI eH n hn2 a) :
    FromSections.pullbackSection i t ≫
      (firstOrderRestrictionIso i hI H d eI eH n hn2).hom =
        exceptionalCoordinate (k := k) a := by
  let S := cartierStepSequence i hI (cartierPowerTwist i hI H n (n * d - 2))
  let N := cartierPowerTwist i hI H n (n * d - 2 + 1)
  let adj := Scheme.Modules.pullbackPushforwardAdjunction i
  let eN := firstOrderRestrictionIso i hI H d eI eH n hn2
  let eQ := firstOrderQuotientIso i hI H d eI eH n hn2
  have hu : S.g = adj.unit.app N.val :=
    cartierStepSequence_g_eq_unit i hI (cartierPowerTwist i hI H n (n * d - 2))
  have hm : (Scheme.Modules.pushforward i).map eN.hom = eQ.hom :=
    firstOrderRestrictionIso_pushforward_hom i hI H d eI eH n hn2
  have h : t ≫ adj.unit.app N.val ≫ (Scheme.Modules.pushforward i).map eN.hom =
      Hom.structureModuleMap i ≫
        (Scheme.Modules.pushforward i).map (exceptionalCoordinate (k := k) a) := by
    calc
      _ = (t ≫ S.g) ≫ eQ.hom := by
        simpa only [Category.assoc] using
          (congrArg (fun g => t ≫ g ≫ (Scheme.Modules.pushforward i).map eN.hom) hu.symm).trans
            (congrArg (fun g => t ≫ S.g ≫ g) hm)
      _ = firstOrderQuotientCoordinate i hI H d eI eH n hn2 a ≫ eQ.hom :=
        congrArg (fun g => g ≫ eQ.hom) ht
      _ = _ := by
        simpa only [firstOrderQuotientCoordinate, Category.assoc, Category.comp_id] using
          congrArg (fun f => Hom.structureModuleMap i ≫
            (Scheme.Modules.pushforward i).map (exceptionalCoordinate (k := k) a) ≫ f)
              eQ.inv_hom_id
  have hβ : (Scheme.Modules.pullback i).map t ≫ eN.hom =
      (pullbackUnitIso i).hom ≫ exceptionalCoordinate (k := k) a := by
    apply (adj.homEquiv _ _).injective
    calc
      _ = t ≫ adj.unit.app N.val ≫ (Scheme.Modules.pushforward i).map eN.hom := by
        rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_unit]
      _ = _ := h
      _ = _ := by
        rw [Adjunction.homEquiv_naturality_right, pullbackUnitIso_homEquiv]
        rfl
  simpa only [FromSections.pullbackSection, Category.assoc, Iso.inv_hom_id_assoc] using
    congrArg (fun f => (pullbackUnitIso i).inv ≫ f) hβ

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The two proved original quotient lifts generate the actual restricted line module. -/
theorem firstOrder_lifts_pullback_epi
    (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
      twistingSheaf k (ULift.{u} (Fin 2)) 1)
    (eH : (Scheme.Modules.pullback i).obj H.val ≅
      twistingSheaf k (ULift.{u} (Fin 2)) (d : ℤ))
    (n : ℕ) (hn2 : 2 ≤ n * d)
    (t : ULift.{u} (Fin 2) → (SheafOfModules.unit X.ringCatSheaf ⟶
      (cartierPowerTwist i hI H n (n * d - 2 + 1)).val))
    (ht : ∀ a, t a ≫
      (cartierStepSequence i hI (cartierPowerTwist i hI H n (n * d - 2))).g =
        firstOrderQuotientCoordinate i hI H d eI eH n hn2 a) :
    Epi (Sigma.desc (FromSections.pulledFamily i t)) := by
  let eN := firstOrderRestrictionIso i hI H d eI eH n hn2
  have hfac : Sigma.desc (FromSections.pulledFamily i t) ≫ eN.hom =
      Sigma.desc (exceptionalCoordinate (k := k)) := by
    apply Sigma.hom_ext
    intro a
    simp only [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc]
    change FromSections.pullbackSection i (t a) ≫
      (firstOrderRestrictionIso i hI H d eI eH n hn2).hom = _
    exact firstOrder_lift_pullback i hI H d eI eH n hn2 a (t a) (ht a)
  let _ : Epi (Sigma.desc (exceptionalCoordinate (k := k))) := exceptionalCoordinate_epi
  let _ : Epi (Sigma.desc (FromSections.pulledFamily i t) ≫ eN.hom) := by
    rw [hfac]
    infer_instance
  have hc : Epi ((Sigma.desc (FromSections.pulledFamily i t) ≫ eN.hom) ≫ eN.inv) :=
    inferInstance
  have hcancel : (Sigma.desc (FromSections.pulledFamily i t) ≫ eN.hom) ≫ eN.inv =
      Sigma.desc (FromSections.pulledFamily i t) := by
    simpa only [Category.assoc, Category.comp_id] using
      congrArg (fun f => Sigma.desc (FromSections.pulledFamily i t) ≫ f) eN.hom_inv_id
  exact hcancel ▸ hc

namespace CartierProjectivePresentation

variable {p i hI H eP d} {n : ℕ} {hn : 1 ≤ n}
  (F : CartierProjectivePresentation p i hI H eP d n hn)
  (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
    twistingSheaf k (ULift.{u} (Fin 2)) 1)
  (eH : (Scheme.Modules.pullback i).obj H.val ≅
    twistingSheaf k (ULift.{u} (Fin 2)) (d : ℤ))

omit [IsNoetherianRing A] [IsClosedImmersion p] in
/-- The original image open where the selected original coordinate is nonvanishing. -/
def pointChartOpen (j₀ : F.index) : F.image.Opens :=
  F.imageInclusion ⁻¹ᵁ coordinateOpen A F.index j₀

omit [IsNoetherianRing A] [IsClosedImmersion p] in
/-- This is an actual affine open of the same native kernel image. -/
theorem pointChartOpen_isAffine (j₀ : F.index) : IsAffineOpen (F.pointChartOpen j₀) :=
  (isAffineOpen_coordinateOpen A F.index j₀).preimage F.imageInclusion

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Evaluate the original chart ratios at the original field coefficients. -/
def pointChartHom (hk : IsField k) (j₀ : F.index) :
    coordinateRing A F.index j₀ →+* k := by
  let _ : Field k := hk.toField
  exact (MvPolynomial.eval₂Hom (exceptionalBaseHom p i)
    (fun j => cartierResidueCoefficient i hI H d eI eH n (F.sections j.1) *
      (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀))⁻¹)).comp
        (coordinateRingToPolynomial A F.index j₀)

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[simp]
theorem pointChartHom_coefficient (hk : IsField k) (j₀ : F.index) (r : A) :
    F.pointChartHom eI eH hk j₀ (coordinateRingCoefficient A F.index j₀ r) =
      exceptionalBaseHom p i r := by
  simp [pointChartHom]

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every original point-chart ratio has the original normalized coefficient. -/
theorem pointChartHom_ratio (hk : IsField k) (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀))) (j : F.index) :
    let _ : Field k := hk.toField
    F.pointChartHom eI eH hk j₀ (coordinateRatio A F.index j₀ j) =
      cartierResidueCoefficient i hI H d eI eH n (F.sections j) *
        (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀))⁻¹ := by
  let _ : Field k := hk.toField
  classical
  by_cases hj : j = j₀
  · subst j
    rw [coordinateRatio_self, map_one]
    exact (mul_inv_cancel₀ h₀.ne_zero).symm
  · change (MvPolynomial.eval₂Hom _ _)
      (coordinateRingToPolynomial A F.index j₀
        (coordinateRatio A F.index j₀ (⟨j, hj⟩ : {j : F.index // j ≠ j₀}).1)) = _
    rw [coordinateRingToPolynomial_ratio, MvPolynomial.eval₂Hom_X']

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The same original projective point is the literal map of this original chart homomorphism. -/
theorem residuePoint_eq_pointChart (hk : IsField k) (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀))) :
    F.residuePoint eI eH j₀ h₀ =
      Spec.map (CommRingCat.ofHom (F.pointChartHom eI eH hk j₀)) ≫
        Proj.awayι (MvPolynomial.homogeneousSubmodule F.index A) (MvPolynomial.X j₀)
          (MvPolynomial.isHomogeneous_X A j₀) Nat.zero_lt_one := by
  let _ : Field k := hk.toField
  let _ : Finite F.index := F.finiteIndex
  let a := fun j => cartierResidueCoefficient i hI H d eI eH n (F.sections j)
  have h := FromSections.FieldSpan.mapOfFiniteFamily_eq_chart_of_ratios
    (exceptionalBaseHom p i) a j₀ h₀.ne_zero (F.pointChartHom eI eH hk j₀)
    (F.pointChartHom_coefficient eI eH hk j₀)
    (F.pointChartHom_ratio eI eH hk j₀ h₀)
  change F.residuePoint eI eH j₀ h₀ = _ at h
  exact h

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual original image point lies wholly in the selected original image chart. -/
theorem residueToImage_preimage_pointChart (hk : IsField k) (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀))) :
    F.residueToImage eI eH j₀ h₀ ⁻¹ᵁ F.pointChartOpen j₀ = ⊤ := by
  let D := coordinateOpen A F.index j₀
  let a := Proj.awayι (MvPolynomial.homogeneousSubmodule F.index A) (MvPolynomial.X j₀)
    (MvPolynomial.isHomogeneous_X A j₀) Nat.zero_lt_one
  have hD : a.opensRange = D :=
    Proj.opensRange_awayι (MvPolynomial.homogeneousSubmodule F.index A)
      (MvPolynomial.X j₀) (MvPolynomial.isHomogeneous_X A j₀) Nat.zero_lt_one
  have ha : a ⁻¹ᵁ D = ⊤ :=
    (congrArg (fun U => a ⁻¹ᵁ U) hD.symm).trans a.preimage_opensRange
  rw [pointChartOpen, ← Scheme.Hom.comp_preimage, F.residueToImage_imageInclusion,
    F.residuePoint_eq_pointChart eI eH hk j₀ h₀, Scheme.Hom.comp_preimage, ha,
    Scheme.Hom.preimage_top]

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The preimage of the original selected image chart contains the entire original E. -/
theorem exceptional_preimage_pointChart (hk : IsField k) (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀))) :
    i ⁻¹ᵁ (F.toImage ⁻¹ᵁ F.pointChartOpen j₀) = ⊤ := by
  rw [← Scheme.Hom.comp_preimage, F.exceptional_toImage_eq eI eH j₀ h₀,
    Scheme.Hom.comp_preimage, F.residueToImage_preimage_pointChart eI eH hk j₀ h₀,
    Scheme.Hom.preimage_top]

end CartierProjectivePresentation

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem appLE_eq_of_hom_eq {Y Z : Scheme.{u}} {f g : Y ⟶ Z} (e : f = g)
    (U : Z.Opens) (V : Y.Opens) (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) :
    f.appLE U V hf = g.appLE U V hg := by
  subst g
  rfl

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pointChart_ringMap {B τ : Type u} [CommRing B]
    (j₀ : τ) (φ : coordinateRing A τ j₀ →+* B)
    (q : Spec (.of B) ⟶ ProjectiveSpace A τ)
    (hq : q = Spec.map (CommRingCat.ofHom φ) ≫
      Proj.awayι (MvPolynomial.homogeneousSubmodule τ A) (MvPolynomial.X j₀)
        (MvPolynomial.isHomogeneous_X A j₀) Nat.zero_lt_one)
    (ht : (⊤ : (Spec (.of B)).Opens) ≤ q ⁻¹ᵁ coordinateOpen A τ j₀) :
    Proj.awayToSection (MvPolynomial.homogeneousSubmodule τ A) (MvPolynomial.X j₀) ≫
        q.appLE (coordinateOpen A τ j₀) ⊤ ht =
      CommRingCat.ofHom ((Scheme.ΓSpecIso (.of B)).inv.hom.comp φ) := by
  let Y := Spec (.of B)
  let D := coordinateOpen A τ j₀
  let E := Proj.basicOpenIsoSpec (MvPolynomial.homogeneousSubmodule τ A)
    (MvPolynomial.X j₀) (MvPolynomial.isHomogeneous_X A j₀) Nat.zero_lt_one
  let ψ := (Scheme.ΓSpecIso (.of B)).inv.hom.comp φ
  have hspec : (⊤ : Y.Opens).toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ) =
      (⊤ : Y.Opens).ι ≫ Spec.map (CommRingCat.ofHom φ) := by
    change (⊤ : Y.Opens).toSpecΓ ≫
      Spec.map (CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (.of B)).inv) = _
    rw [Spec.map_comp, Scheme.Opens.toSpecΓ_top]
    simp only [Category.assoc]
    rw [toSpecΓ_SpecMap_ΓSpecIso_inv_assoc]
  have hr : q.resLE D ⊤ ht =
      (⊤ : Y.Opens).toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ) ≫ E.inv := by
    apply (cancel_mono D.ι).mp
    calc
      _ = (⊤ : Y.Opens).ι ≫ q := Scheme.Hom.resLE_comp_ι q ht
      _ = (⊤ : Y.Opens).ι ≫ Spec.map (CommRingCat.ofHom φ) ≫ E.inv ≫ D.ι :=
        congrArg (fun f => (⊤ : Y.Opens).ι ≫ f) hq
      _ = _ := by
        simpa only [Category.assoc] using
          congrArg (fun f => f ≫ E.inv ≫ D.ι) hspec.symm
  have hr' : q.resLE D ⊤ ht ≫ E.hom =
      (⊤ : Y.Opens).toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ) := by
    refine (congrArg (fun f => f ≫ E.hom) hr).trans ?_
    simpa only [Category.assoc, Category.comp_id] using
      congrArg (fun f => (⊤ : Y.Opens).toSpecΓ ≫
        Spec.map (CommRingCat.ofHom ψ) ≫ f) E.inv_hom_id
  have hh := congrArg (fun f => f.appTop) hr'
  apply (cancel_epi (Scheme.ΓSpecIso (CommRingCat.of (coordinateRing A τ j₀))).hom).mp
  apply (cancel_mono (⊤ : Y.Opens).topIso.inv).mp
  simpa only [Scheme.Hom.comp_appTop, Proj.basicOpenIsoSpec_hom,
    Proj.basicOpenToSpec_app_top, Scheme.Hom.resLE_app_top, Scheme.Opens.toSpecΓ_appTop,
    Category.assoc, Iso.inv_hom_id_assoc, Scheme.ΓSpecIso_naturality_assoc,
    E, D, coordinateOpen, coordinateRing] using hh

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pointChart_coordinate_pullback {B τ : Type u} [CommRing B]
    {Z : Scheme.{u}} (c : Spec (.of B) ⟶ Z) (g : Z ⟶ ProjectiveSpace A τ)
    (q : Spec (.of B) ⟶ ProjectiveSpace A τ) (j₀ : τ)
    (φ : coordinateRing A τ j₀ →+* B) (htri : c ≫ g = q)
    (hq : q = Spec.map (CommRingCat.ofHom φ) ≫
      Proj.awayι (MvPolynomial.homogeneousSubmodule τ A) (MvPolynomial.X j₀)
        (MvPolynomial.isHomogeneous_X A j₀) Nat.zero_lt_one)
    (ht : (⊤ : (Spec (.of B)).Opens) ≤ c ⁻¹ᵁ (g ⁻¹ᵁ coordinateOpen A τ j₀)) (j : τ) :
    (c.appLE (g ⁻¹ᵁ coordinateOpen A τ j₀) ⊤ ht).hom
        ((g.app (coordinateOpen A τ j₀)).hom (coordinateRatioSection A τ j₀ j)) =
      (Scheme.ΓSpecIso (.of B)).inv.hom (φ (coordinateRatio A τ j₀ j)) := by
  let D := coordinateOpen A τ j₀
  have hpre : c ⁻¹ᵁ (g ⁻¹ᵁ D) = q ⁻¹ᵁ D :=
    congrArg (fun f => f ⁻¹ᵁ D) htri
  have htq : (⊤ : (Spec (.of B)).Opens) ≤ q ⁻¹ᵁ D := hpre ▸ ht
  have hcomp : g.app D ≫ c.appLE (g ⁻¹ᵁ D) ⊤ ht = q.appLE D ⊤ htq :=
    (Scheme.Hom.comp_appLE c g D ⊤ ht).symm.trans
      (appLE_eq_of_hom_eq htri D ⊤ ht htq)
  have hring := pointChart_ringMap j₀ φ q hq htq
  calc
    _ = (q.appLE D ⊤ htq).hom (coordinateRatioSection A τ j₀ j) :=
      congrArg (fun f : Γ(ProjectiveSpace A τ, D) ⟶ Γ(Spec (.of B), ⊤) =>
        f.hom (coordinateRatioSection A τ j₀ j)) hcomp
    _ = _ := congrArg
      (fun f : CommRingCat.of (coordinateRing A τ j₀) ⟶ Γ(Spec (.of B), ⊤) =>
        f.hom (coordinateRatio A τ j₀ j)) hring

namespace CartierProjectivePresentation

variable {p i hI H eP d} {n : ℕ} {hn : 1 ≤ n}
  (F : CartierProjectivePresentation p i hI H eP d n hn)
  (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
    twistingSheaf k (ULift.{u} (Fin 2)) 1)
  (eH : (Scheme.Modules.pullback i).obj H.val ≅
    twistingSheaf k (ULift.{u} (Fin 2)) (d : ℤ))

omit [IsNoetherianRing A] [IsClosedImmersion p] in
/-- The literal original target coordinate ratio on the original selected image chart. -/
def pointChartCoordinate (j₀ j : F.index) : Γ(F.image, F.pointChartOpen j₀) :=
  (F.imageInclusion.app (coordinateOpen A F.index j₀)).hom
    (coordinateRatioSection A F.index j₀ j)

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Its actual value on the original point is the original normalized coefficient. -/
theorem residueToImage_appLE_pointChartCoordinate (hk : IsField k) (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀))) (j : F.index) :
    ((F.residueToImage eI eH j₀ h₀).appLE (F.pointChartOpen j₀) ⊤
      (F.residueToImage_preimage_pointChart eI eH hk j₀ h₀).ge).hom
        (F.pointChartCoordinate j₀ j) =
      (Scheme.ΓSpecIso (.of k)).inv.hom
        (F.pointChartHom eI eH hk j₀ (coordinateRatio A F.index j₀ j)) := by
  exact pointChart_coordinate_pullback (F.residueToImage eI eH j₀ h₀)
    F.imageInclusion (F.residuePoint eI eH j₀ h₀) j₀ (F.pointChartHom eI eH hk j₀)
    (F.residueToImage_imageInclusion eI eH j₀ h₀)
    (F.residuePoint_eq_pointChart eI eH hk j₀ h₀)
    (F.residueToImage_preimage_pointChart eI eH hk j₀ h₀).ge j

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A zero original residue coefficient places the original coordinate in the point ideal. -/
theorem pointChartCoordinate_mem_pointIdeal (hk : IsField k) (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀))) (j : F.index)
    (hj : cartierResidueCoefficient i hI H d eI eH n (F.sections j) = 0) :
    F.pointChartCoordinate j₀ j ∈ (F.pointIdeal eI eH j₀ h₀).ideal
      ⟨F.pointChartOpen j₀, F.pointChartOpen_isAffine j₀⟩ := by
  let _ : Field k := hk.toField
  let c := F.residueToImage eI eH j₀ h₀
  let U := F.pointChartOpen j₀
  have he : c ⁻¹ᵁ U = ⊤ := F.residueToImage_preimage_pointChart eI eH hk j₀ h₀
  have ht : (⊤ : (Spec (.of k)).Opens) ≤ c ⁻¹ᵁ U := he.ge
  have hz : (c.appLE U ⊤ ht).hom (F.pointChartCoordinate j₀ j) = 0 := by
    calc
      _ = (Scheme.ΓSpecIso (.of k)).inv.hom
          (F.pointChartHom eI eH hk j₀ (coordinateRatio A F.index j₀ j)) :=
        F.residueToImage_appLE_pointChartCoordinate eI eH hk j₀ h₀ j
      _ = (Scheme.ΓSpecIso (.of k)).inv.hom
          (cartierResidueCoefficient i hI H d eI eH n (F.sections j) *
            (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀))⁻¹) :=
        congrArg (Scheme.ΓSpecIso (.of k)).inv.hom
          (F.pointChartHom_ratio eI eH hk j₀ h₀ j)
      _ = 0 := by rw [hj, zero_mul, map_zero]
  have hh : (homOfLE ht : (⊤ : (Spec (.of k)).Opens) ⟶ c ⁻¹ᵁ U) = eqToHom he.symm :=
    Subsingleton.elim _ _
  let _ : IsIso (homOfLE ht) := by rw [hh]; infer_instance
  let r := (Spec (.of k)).presheaf.map (homOfLE ht).op
  have hinj := (ConcreteCategory.bijective_of_isIso r).injective
  rw [pointIdeal, Hom.ker_apply]
  change (c.app U).hom (F.pointChartCoordinate j₀ j) = 0
  apply hinj
  change (c.appLE U ⊤ ht).hom (F.pointChartCoordinate j₀ j) = r.hom 0
  exact hz.trans (map_zero r.hom).symm

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The literal coordinate section of the actual kernel ideal module. -/
def pointChartIdealCoordinate (hk : IsField k) (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀))) (j : F.index)
    (hj : cartierResidueCoefficient i hI H d eI eH n (F.sections j) = 0) :
    Γ(Hom.idealModule (F.residueToImage eI eH j₀ h₀), F.pointChartOpen j₀) := by
  let _ : Field k := hk.toField
  exact (Hom.idealSectionsEquiv (F.residueToImage eI eH j₀ h₀) (F.pointChartOpen j₀)).symm
    ⟨F.pointChartCoordinate j₀ j, by
      have h := F.pointChartCoordinate_mem_pointIdeal eI eH hk j₀ h₀ j hj
      rwa [pointIdeal, Hom.ker_apply] at h⟩

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Its actual kernel inclusion is exactly the original target coordinate function. -/
theorem pointChartIdealCoordinate_inclusion (hk : IsField k) (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀))) (j : F.index)
    (hj : cartierResidueCoefficient i hI H d eI eH n (F.sections j) = 0) :
    (Hom.idealInclusion (F.residueToImage eI eH j₀ h₀)).val.app (op (F.pointChartOpen j₀))
      (F.pointChartIdealCoordinate eI eH hk j₀ h₀ j hj) = F.pointChartCoordinate j₀ j := by
  let _ : Field k := hk.toField
  rw [← Hom.idealSectionsEquiv_val]
  exact congrArg Subtype.val
    ((Hom.idealSectionsEquiv (F.residueToImage eI eH j₀ h₀) (F.pointChartOpen j₀)).apply_symm_apply
      ⟨F.pointChartCoordinate j₀ j, by
        have h := F.pointChartCoordinate_mem_pointIdeal eI eH hk j₀ h₀ j hj
        rwa [pointIdeal, Hom.ker_apply] at h⟩)

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual adjoint ideal comparison carries that original coordinate into I_E. -/
def pointChartExceptionalCoordinate (hk : IsField k) (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀))) (j : F.index)
    (hj : cartierResidueCoefficient i hI H d eI eH n (F.sections j) = 0) :
    Γ(Hom.idealModule i, F.toImage ⁻¹ᵁ F.pointChartOpen j₀) :=
  (Hom.idealPushforwardMap (F.residueToImage eI eH j₀ h₀) i F.toImage
    (toSpec k (ULift.{u} (Fin 2))) (F.exceptional_toImage_eq eI eH j₀ h₀).symm).val.app
      (op (F.pointChartOpen j₀)) (F.pointChartIdealCoordinate eI eH hk j₀ h₀ j hj)

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original exceptional kernel inclusion gives the original pulled coordinate function. -/
theorem pointChartExceptionalCoordinate_inclusion (hk : IsField k) (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀))) (j : F.index)
    (hj : cartierResidueCoefficient i hI H d eI eH n (F.sections j) = 0) :
    (Hom.idealInclusion i).val.app (op (F.toImage ⁻¹ᵁ F.pointChartOpen j₀))
        (F.pointChartExceptionalCoordinate eI eH hk j₀ h₀ j hj) =
      (F.toImage.app (F.pointChartOpen j₀)).hom (F.pointChartCoordinate j₀ j) := by
  have h := congrArg (fun α => α.val.app (op (F.pointChartOpen j₀))
      (F.pointChartIdealCoordinate eI eH hk j₀ h₀ j hj))
    (Hom.idealPushforwardMap_inclusion (F.residueToImage eI eH j₀ h₀) i F.toImage
      (toSpec k (ULift.{u} (Fin 2))) (F.exceptional_toImage_eq eI eH j₀ h₀).symm)
  change (Hom.idealInclusion i).val.app (op (F.toImage ⁻¹ᵁ F.pointChartOpen j₀))
        (F.pointChartExceptionalCoordinate eI eH hk j₀ h₀ j hj) =
      (F.toImage.app (F.pointChartOpen j₀)).hom
        ((Hom.idealInclusion (F.residueToImage eI eH j₀ h₀)).val.app
          (op (F.pointChartOpen j₀)) (F.pointChartIdealCoordinate eI eH hk j₀ h₀ j hj)) at h
  exact h.trans (congrArg (F.toImage.app (F.pointChartOpen j₀)).hom
    (F.pointChartIdealCoordinate_inclusion eI eH hk j₀ h₀ j hj))

end CartierProjectivePresentation

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every original first-order Cartier image has zero original residue coefficient. -/
theorem firstOrderCartierImage_residueCoefficient
    (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
      twistingSheaf k (ULift.{u} (Fin 2)) 1)
    (eH : (Scheme.Modules.pullback i).obj H.val ≅
      twistingSheaf k (ULift.{u} (Fin 2)) (d : ℤ))
    (n : ℕ) (hn2 : 2 ≤ n * d)
    (t : SheafOfModules.unit X.ringCatSheaf ⟶
      (cartierPowerTwist i hI H n (n * d - 2 + 1)).val) :
    cartierResidueCoefficient i hI H d eI eH n
      (firstOrderCartierImage i hI H d n hn2 t) = 0 := by
  let E := ProjectiveSpace k (ULift.{u} (Fin 2))
  let N := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit E.ringCatSheaf)
  let γ := globalFunctionsRingEquiv k (ULift.{u} (Fin 2))
  calc
    _ = γ.symm (unitHomGlobalSectionsEquiv X N
        (firstOrderCartierImage i hI H d n hn2 t ≫
          cartierResidueMap i hI H d eI eH n)) :=
      cartierResidueCoefficient_eq i hI H d eI eH n _
    _ = γ.symm (unitHomGlobalSectionsEquiv X N 0) :=
      congrArg (fun s => γ.symm (unitHomGlobalSectionsEquiv X N s))
        (firstOrderCartierImage_residueMap i hI H d eI eH n hn2 t)
    _ = 0 := by
      change γ.symm (0 : Γ(E, ⊤)) = 0
      exact map_zero γ.symm

namespace CartierProjectivePresentation

variable {p i hI H eP d} {n : ℕ} {hn : 1 ≤ n}
  (F : CartierProjectivePresentation p i hI H eP d n hn)
  (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
    twistingSheaf k (ULift.{u} (Fin 2)) 1)
  (eH : (Scheme.Modules.pullback i).obj H.val ≅
    twistingSheaf k (ULift.{u} (Fin 2)) (d : ℤ))

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Each retained first-order coordinate gives an actual section of the same point ideal. -/
theorem pointChartCoordinate_firstOrder_mem (hk : IsField k) (hn2 : 2 ≤ n * d)
    (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀)))
    (j : F.index) (t : SheafOfModules.unit X.ringCatSheaf ⟶
      (cartierPowerTwist i hI H n (n * d - 2 + 1)).val)
    (hj : F.sections j = firstOrderCartierImage i hI H d n hn2 t) :
    F.pointChartCoordinate j₀ j ∈ (F.pointIdeal eI eH j₀ h₀).ideal
      ⟨F.pointChartOpen j₀, F.pointChartOpen_isAffine j₀⟩ := by
  apply F.pointChartCoordinate_mem_pointIdeal eI eH hk j₀ h₀ j
  exact (congrArg (cartierResidueCoefficient i hI H d eI eH n) hj).trans
    (firstOrderCartierImage_residueCoefficient i hI H d eI eH n hn2 t)

end CartierProjectivePresentation

section CartierKernelMultiply

variable {C : Scheme.{u}} (j : C ⟶ X) [IsClosedImmersion j]
  (hJ : IsLocallyRankOne X (Hom.idealModule j)) (M : LineBundle X)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual Cartier multiplier uses the original tensor maps, braiding and cancellation. -/
def cartierKernelMultiply
    (s : SheafOfModules.unit X.ringCatSheaf ⟶
      (tensorLineBundle X (dualLineBundle X (cartierIdealLineBundle j hJ)) M).val) :
    Hom.idealModule j ⟶ M.val := by
  let I : X.Modules := (cartierIdealLineBundle j hJ).val
  let P := tensorLineBundle X (dualLineBundle X (cartierIdealLineBundle j hJ)) M
  exact (rightUnitor (C := X.Modules) I).inv ≫ tensorSheafMap X (𝟙 I) s ≫
    (tensorSheafBraiding X I P.val).hom ≫
      (cartierCancellationIso (cartierIdealLineBundle j hJ) M).hom

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem cartierKernelMultiply_comp
    (s : SheafOfModules.unit X.ringCatSheaf ⟶
      (tensorLineBundle X (dualLineBundle X (cartierIdealLineBundle j hJ)) M).val) :
    cartierKernelMultiply j hJ M s ≫ (cartierStepSequence j hJ M).f =
      Hom.idealInclusion j ≫ s := by
  let I : X.Modules := (cartierIdealLineBundle j hJ).val
  let P := tensorLineBundle X (dualLineBundle X (cartierIdealLineBundle j hJ)) M
  let c := cartierCancellationIso (cartierIdealLineBundle j hJ) M
  change (rightUnitor (C := X.Modules) I).inv ≫ tensorSheafMap X (𝟙 I) s ≫
      (tensorSheafBraiding X I P.val).hom ≫ c.hom ≫
      c.inv ≫ tensorSheafMap X (𝟙 P.val) (Hom.idealInclusion j) ≫
      (rightUnitor (C := X.Modules) P.val).hom =
        Hom.idealInclusion j ≫ s
  apply (cancel_epi (rightUnitor (C := X.Modules) I).hom).mp
  simp only [Iso.hom_inv_id_assoc]
  apply moduleTensor_hom_ext
  intro U m r
  change Γ(X, U) at r
  change (rightUnitor (C := X.Modules) P.val).hom.val.app (op U)
      ((tensorSheafMap X (𝟙 P.val) (Hom.idealInclusion j)).val.app (op U)
        ((tensorSheafBraiding X I P.val).hom.val.app (op U)
          ((tensorSheafMap X (𝟙 I) s).val.app (op U)
            (moduleTensorSection X I (SheafOfModules.unit X.ringCatSheaf) U m r)))) =
    s.val.app (op U) ((Hom.idealInclusion j).val.app (op U)
      ((rightUnitor (C := X.Modules) I).hom.val.app (op U)
        (moduleTensorSection X I (SheafOfModules.unit X.ringCatSheaf) U m r)))
  have h₁ : (tensorSheafMap X (𝟙 I) s).val.app (op U)
      (moduleTensorSection X I (SheafOfModules.unit X.ringCatSheaf) U m r) =
        moduleTensorSection X I P.val U m (s.val.app (op U) r) :=
    moduleTensorLeftFunctor_map_section I s U m r
  have h₂ : (tensorSheafBraiding X I P.val).hom.val.app (op U)
      (moduleTensorSection X I P.val U m (s.val.app (op U) r)) =
        moduleTensorSection X P.val I U (s.val.app (op U) r) m :=
    braiding_hom_moduleTensorSection I P.val U m (s.val.app (op U) r)
  have h₃ : (tensorSheafMap X (𝟙 P.val) (Hom.idealInclusion j)).val.app (op U)
      (moduleTensorSection X P.val I U (s.val.app (op U) r) m) =
        moduleTensorSection X P.val (SheafOfModules.unit X.ringCatSheaf) U
          (s.val.app (op U) r) ((Hom.idealInclusion j).val.app (op U) m) :=
    moduleTensorLeftFunctor_map_section P.val (Hom.idealInclusion j) U _ m
  have h₄ : (rightUnitor (C := X.Modules) P.val).hom.val.app (op U)
      (moduleTensorSection X P.val (SheafOfModules.unit X.ringCatSheaf) U
        (s.val.app (op U) r) ((Hom.idealInclusion j).val.app (op U) m)) =
          (show Γ(X, U) from (Hom.idealInclusion j).val.app (op U) m) •
            s.val.app (op U) r :=
    tensorRightUnitIso_hom_section X P.val U (s.val.app (op U) r) _
  have h₅ : (rightUnitor (C := X.Modules) I).hom.val.app (op U)
      (moduleTensorSection X I (SheafOfModules.unit X.ringCatSheaf) U m r) = r • m :=
    tensorRightUnitIso_hom_section X I U m r
  rw [h₁, h₂, h₃, h₄, h₅]
  let a : Γ(X, U) := (Hom.idealInclusion j).val.app (op U) m
  have hs := (s.val.app (op U)).hom.map_smul a r
  have hm := ((Hom.idealInclusion j).val.app (op U)).hom.map_smul r m
  change s.val.app (op U) (a * r) = a • s.val.app (op U) r at hs
  change (Hom.idealInclusion j).val.app (op U) (r • m) = r * a at hm
  exact hs.symm.trans ((congrArg (s.val.app (op U)) (mul_comm a r)).trans
    (congrArg (s.val.app (op U)) hm.symm))

end CartierKernelMultiply

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pullback_tensorMap_isIso_of_maps_isIso {Y Z : Scheme.{u}}
    (f : Y ⟶ Z) {M M' N N' : Z.Modules} (a : M ⟶ M') (b : N ⟶ N')
    [IsIso ((Scheme.Modules.pullback f).map a)] [IsIso ((Scheme.Modules.pullback f).map b)] :
    IsIso ((Scheme.Modules.pullback f).map (tensorSheafMap Z a b)) := by
  let _ : IsIso (pullbackTensorMap f M N) :=
    Pullback.Tensor.pullbackTensorMap_isIso f M N
  let _ : IsIso (pullbackTensorMap f M' N') :=
    Pullback.Tensor.pullbackTensorMap_isIso f M' N'
  let e := tensorSheafIso Y (asIso ((Scheme.Modules.pullback f).map a))
    (asIso ((Scheme.Modules.pullback f).map b))
  let _ : IsIso (tensorSheafMap Y ((Scheme.Modules.pullback f).map a)
      ((Scheme.Modules.pullback f).map b)) := e.isIso_hom
  have h : IsIso ((Scheme.Modules.pullback f).map (tensorSheafMap Z a b) ≫
      pullbackTensorMap f M' N') := by
    rw [pullbackTensorMap_naturality]
    infer_instance
  exact (isIso_comp_right_iff _ (pullbackTensorMap f M' N')).mp h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem cartierKernelMultiply_pullback_isIso {C : Scheme.{u}}
    (j : C ⟶ X)
    (hJ : IsLocallyRankOne X (Hom.idealModule j)) (M : LineBundle X)
    (s : SheafOfModules.unit X.ringCatSheaf ⟶
      (tensorLineBundle X (dualLineBundle X (cartierIdealLineBundle j hJ)) M).val)
    [IsIso ((Scheme.Modules.pullback j).map s)] :
    IsIso ((Scheme.Modules.pullback j).map (cartierKernelMultiply j hJ M s)) := by
  let _ : IsIso ((Scheme.Modules.pullback j).map
      (tensorSheafMap X (𝟙 (Hom.idealModule j)) s)) :=
    pullback_tensorMap_isIso_of_maps_isIso j (𝟙 (Hom.idealModule j)) s
  dsimp only [cartierKernelMultiply]
  simp only [Functor.map_comp]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem unitMul_isIso_of_isUnit (Y : Scheme.{u}) (r : Γ(Y, ⊤)) (hr : IsUnit r) :
    IsIso (unitMul Y r) := by
  obtain ⟨v, rfl⟩ := hr
  exact (unitMulIso Y v).isIso_hom

namespace CartierProjectivePresentation

variable {p i hI H eP d} {n : ℕ} {hn : 1 ≤ n}
  (F : CartierProjectivePresentation p i hI H eP d n hn)
  (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
    twistingSheaf k (ULift.{u} (Fin 2)) 1)
  (eH : (Scheme.Modules.pullback i).obj H.val ≅
    twistingSheaf k (ULift.{u} (Fin 2)) (d : ℤ))

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original selected section is genuinely invertible after its original restriction to E. -/
theorem pullback_selectedSection_isIso (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀))) :
    IsIso ((Scheme.Modules.pullback i).map (F.sections j₀)) := by
  let E := ProjectiveSpace k (ULift.{u} (Fin 2))
  let γ := globalFunctionsRingEquiv k (ULift.{u} (Fin 2))
  let a := cartierResidueCoefficient i hI H d eI eH n (F.sections j₀)
  let e := cartierFinalRestrictionIso i hI H d eI eH n
  have hr : FromSections.pullbackSection i (F.sections j₀) ≫ e.hom = unitMul E (γ a) := by
    apply (unitHomGlobalSectionsEquiv E (SheafOfModules.unit E.ringCatSheaf)).injective
    rw [unitHomGlobalSectionsEquiv_unitMul]
    exact (γ.apply_symm_apply _).symm
  let _ : IsIso (unitMul E (γ a)) := unitMul_isIso_of_isUnit E (γ a) (h₀.map γ.toRingHom)
  have hcomp : IsIso (FromSections.pullbackSection i (F.sections j₀) ≫ e.hom) := by
    rw [hr]
    infer_instance
  have hsection : IsIso (FromSections.pullbackSection i (F.sections j₀)) :=
    (isIso_comp_right_iff _ e.hom).mp hcomp
  change IsIso ((pullbackUnitIso i).inv ≫
    (Scheme.Modules.pullback i).map (F.sections j₀)) at hsection
  exact (isIso_comp_left_iff (pullbackUnitIso i).inv _).mp hsection

end CartierProjectivePresentation

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem unitHomGlobalSections_comp {Y : Scheme.{u}} {M N : Y.Modules}
    (s : SheafOfModules.unit Y.ringCatSheaf ⟶ M) (α : M ⟶ N) :
    unitHomGlobalSectionsEquiv Y N (s ≫ α) =
      α.val.app (op ⊤) (unitHomGlobalSectionsEquiv Y M s) := by
  rw [unitHomGlobalSectionsEquiv_apply, unitHomGlobalSectionsEquiv_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def pullbackSectionOn {Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules)
    (U : X.Opens) (h : f ⁻¹ᵁ U = ⊤) (m : Γ(M, U)) :
    SheafOfModules.unit Y.ringCatSheaf ⟶ (Scheme.Modules.pullback f).obj M :=
  (unitHomGlobalSectionsEquiv Y _).symm
    (((Scheme.Modules.pullback f).obj M).presheaf.map (eqToHom h.symm).op
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app (op U) m))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pullbackSectionOn_map {Y : Scheme.{u}} (f : Y ⟶ X) {M N : X.Modules}
    (α : M ⟶ N) (U : X.Opens) (h : f ⁻¹ᵁ U = ⊤) (m : Γ(M, U)) :
    pullbackSectionOn f N U h (α.val.app (op U) m) =
      pullbackSectionOn f M U h m ≫ (Scheme.Modules.pullback f).map α := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  let β := (Scheme.Modules.pullback f).map α
  have hu := congrArg (fun q => q.val.app (op U) m) (adj.unit.naturality α)
  change (adj.unit.app N).val.app (op U) (α.val.app (op U) m) =
    β.val.app (op (f ⁻¹ᵁ U)) ((adj.unit.app M).val.app (op U) m) at hu
  apply (unitHomGlobalSectionsEquiv Y _).injective
  rw [unitHomGlobalSections_comp]
  simp only [pullbackSectionOn, Equiv.apply_symm_apply]
  exact (congrArg (((Scheme.Modules.pullback f).obj N).presheaf.map
      (eqToHom h.symm).op) hu).trans
    (PresheafOfModules.naturality_apply β.val (eqToHom h.symm).op
      ((adj.unit.app M).val.app (op U) m)).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pullbackSectionOn_global {Y : Scheme.{u}} (f : Y ⟶ X) {M : X.Modules}
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ M) (U : X.Opens)
    (h : f ⁻¹ᵁ U = ⊤) :
    pullbackSectionOn f M U h (s.val.app (op U) (1 : Γ(X, U))) =
      FromSections.pullbackSection f s := by
  let t := unitHomGlobalSectionsEquiv X M s
  let u := (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M
  let N := (Scheme.Modules.pullback f).obj M
  let r : U ⟶ ⊤ := homOfLE le_top
  have hs : s.val.app (op U) (1 : Γ(X, U)) = M.presheaf.map r.op t := by
    have hs' := unitHomGlobalSectionsEquiv_symm_app X M t U 1
    have ht : (unitHomGlobalSectionsEquiv X M).symm t = s :=
      (unitHomGlobalSectionsEquiv X M).symm_apply_apply s
    rw [ht] at hs'
    exact hs'.trans (one_smul _ _)
  have hu := PresheafOfModules.naturality_apply u.val r.op t
  change u.val.app (op U) (M.presheaf.map r.op t) =
    N.presheaf.map ((TopologicalSpace.Opens.map f.base).map r).op (u.val.app (op ⊤) t) at hu
  have hpos : eqToHom h.symm ≫ (TopologicalSpace.Opens.map f.base).map r = 𝟙 (⊤ : Y.Opens) :=
    Subsingleton.elim _ _
  have hm : N.presheaf.map ((TopologicalSpace.Opens.map f.base).map r).op ≫
      N.presheaf.map (eqToHom h.symm).op = 𝟙 _ := by
    rw [← Functor.map_comp]
    exact (congrArg (fun g : (⊤ : Y.Opens) ⟶ ⊤ => N.presheaf.map g.op) hpos).trans
      (N.presheaf.map_id (op (⊤ : Y.Opens)))
  apply (unitHomGlobalSectionsEquiv Y _).injective
  rw [FromSections.pullbackSection_global]
  simp only [pullbackSectionOn, Equiv.apply_symm_apply]
  change N.presheaf.map (eqToHom h.symm).op
    (u.val.app (op U) (s.val.app (op U) (1 : Γ(X, U)))) = u.val.app (op ⊤) t
  rw [hs, hu]
  exact (congrArg (fun q => q (u.val.app (op ⊤) t)) hm)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def nativeCoordinateSection (R : Type u) [CommRing R] (J : Type u) (j : J) :
    SheafOfModules.unit (ProjectiveSpace R J).ringCatSheaf ⟶ twistingSheaf R J 1 :=
  (unitHomGlobalSectionsEquiv (ProjectiveSpace R J) _).symm
    (homogeneousSection R J 1 (coordinatePower R J 1 j))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem nativeCoordinateSection_local (R : Type u) [CommRing R] (J : Type u)
    (j₀ j : J) :
    ((coordinateUnitCocycle R J).zpow (-1)).localSectionsEquiv j₀ le_rfl
      ((nativeCoordinateSection R J j).val.app (op (coordinateOpen R J j₀))
        (1 : Γ(ProjectiveSpace R J, coordinateOpen R J j₀))) =
      coordinateRatioSection R J j₀ j := by
  have hs := (unitHomGlobalSectionsEquiv_symm_app (ProjectiveSpace R J)
    (twistingSheaf R J 1) (homogeneousSection R J 1 (coordinatePower R J 1 j))
    (coordinateOpen R J j₀) 1).trans (one_smul _ _)
  change ((coordinateUnitCocycle R J).zpow (-1)).localSectionsEquiv j₀ le_rfl _ = _
  rw [show (nativeCoordinateSection R J j).val.app (op (coordinateOpen R J j₀))
      (1 : Γ(ProjectiveSpace R J, coordinateOpen R J j₀)) = _ from hs]
  exact (homogeneousSection_local R J 1 (coordinatePower R J 1 j) j₀).trans
    (coordinateRatioSection_eq_homogeneousChartSection R J j₀ j).symm

namespace CartierProjectivePresentation

variable {p i hI H eP d} {n : ℕ} {hn : 1 ≤ n}
  (F : CartierProjectivePresentation p i hI H eP d n hn)

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coordinateMap_eq_pullbackSection (j : F.index) :
    F.coordinateMap j = FromSections.pullbackSection F.toProjective
      (nativeCoordinateSection A F.index j) := by
  let _ : Finite F.index := F.finiteIndex
  let _ : Epi (Sigma.desc F.sections) := F.epiSections
  let C := (coordinateUnitCocycle A F.index).zpow (-1)
  let t := homogeneousSection A F.index 1 (coordinatePower A F.index 1 j)
  let η := (Scheme.Modules.pullbackPushforwardAdjunction F.toProjective).unit.app C.sheaf
  have hL : unitHomGlobalSectionsEquiv X _ (F.coordinateMap j) =
      FromSections.pulledGlobalSection F.toProjective C t :=
    (unitHomGlobalSectionsEquiv X _).apply_symm_apply _
  have hR := FromSections.pullbackSection_global F.toProjective
    (nativeCoordinateSection A F.index j)
  have hγ : unitHomGlobalSectionsEquiv (ProjectiveSpace A F.index) C.sheaf
      (nativeCoordinateSection A F.index j) = t :=
    (unitHomGlobalSectionsEquiv (ProjectiveSpace A F.index) C.sheaf).apply_symm_apply t
  apply (unitHomGlobalSectionsEquiv X _).injective
  exact hL.trans (hR.trans (congrArg (η.val.app (op ⊤)) hγ)).symm

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem sections_ratio_on (j₀ j : F.index) (O : X.Opens)
    (hO : O ≤ F.toProjective ⁻¹ᵁ coordinateOpen A F.index j₀) :
    (F.sections j).val.app (op O) (1 : Γ(X, O)) =
      (F.toProjective.appLE (coordinateOpen A F.index j₀) O hO).hom
          (coordinateRatioSection A F.index j₀ j) •
        (F.sections j₀).val.app (op O) (1 : Γ(X, O)) := by
  let C := (coordinateUnitCocycle A F.index).zpow (-1)
  let D := FromSections.pullbackCocycle F.toProjective C
  let e := F.twistingPullbackIso.symm ≪≫
    FromSections.pullbackCocycleIso F.toProjective C (iSup_coordinateOpen_eq_top A F.index)
  have hs (b : F.index) : F.sections b ≫ e.hom =
      FromSections.pullbackSection F.toProjective (nativeCoordinateSection A F.index b) ≫
        (FromSections.pullbackCocycleIso F.toProjective C
          (iSup_coordinateOpen_eq_top A F.index)).hom := by
    calc
      _ = (F.coordinateMap b ≫ F.twistingPullbackIso.hom) ≫ e.hom :=
        congrArg (fun s => s ≫ e.hom) (F.coordinateMap_comp b).symm
      _ = _ := by
        simp only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
        rw [F.coordinateMap_eq_pullbackSection]
  have hc (b : F.index) : D.localSectionsEquiv j₀ hO
      (e.hom.val.app (op O) ((F.sections b).val.app (op O) (1 : Γ(X, O)))) =
        (F.toProjective.appLE (coordinateOpen A F.index j₀) O hO).hom
          (coordinateRatioSection A F.index j₀ b) := by
    have hv := congrArg (fun s : SheafOfModules.unit X.ringCatSheaf ⟶ D.sheaf =>
      s.val.app (op O) (1 : Γ(X, O))) (hs b)
    exact (congrArg (D.localSectionsEquiv j₀ hO) hv).trans
      ((FromSections.pullbackCocycleIso_section_coefficient F.toProjective C
        (iSup_coordinateOpen_eq_top A F.index) (nativeCoordinateSection A F.index b) j₀ hO).trans
          (congrArg (F.toProjective.appLE (coordinateOpen A F.index j₀) O hO).hom
            (nativeCoordinateSection_local A F.index j₀ b)))
  apply moduleHom_app_injective e.hom O
  let r := (F.toProjective.appLE (coordinateOpen A F.index j₀) O hO).hom
    (coordinateRatioSection A F.index j₀ j)
  have hlin := (e.hom.val.app (op O)).hom.map_smul r
    ((F.sections j₀).val.app (op O) (1 : Γ(X, O)))
  refine Eq.trans ?_ hlin.symm
  apply (D.localSectionsEquiv j₀ hO).injective
  have h₀ : D.localSectionsEquiv j₀ hO
      (e.hom.val.app (op O) ((F.sections j₀).val.app (op O) (1 : Γ(X, O)))) = 1 :=
    (hc j₀).trans ((congrArg
      (F.toProjective.appLE (coordinateOpen A F.index j₀) O hO).hom
      (coordinateRatioSection_self A F.index j₀)).trans (map_one _))
  have hscale := (D.localSectionsEquiv j₀ hO).map_smul r
    (e.hom.val.app (op O) ((F.sections j₀).val.app (op O) (1 : Γ(X, O))))
  exact (hc j).trans ((hscale.trans
    ((congrArg (fun a => r • a) h₀).trans (mul_one r))).symm)

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Original section ratios on the actual original selected image chart. -/
theorem pointChart_sections_ratio (j₀ j : F.index) :
    (F.sections j).val.app (op (F.toImage ⁻¹ᵁ F.pointChartOpen j₀))
        (1 : Γ(X, F.toImage ⁻¹ᵁ F.pointChartOpen j₀)) =
      (F.toImage.app (F.pointChartOpen j₀)).hom (F.pointChartCoordinate j₀ j) •
        (F.sections j₀).val.app (op (F.toImage ⁻¹ᵁ F.pointChartOpen j₀))
          (1 : Γ(X, F.toImage ⁻¹ᵁ F.pointChartOpen j₀)) := by
  let D := coordinateOpen A F.index j₀
  let W := F.toImage ⁻¹ᵁ F.pointChartOpen j₀
  have hpre : W ≤ F.toProjective ⁻¹ᵁ D := by
    rw [← F.toImage_imageInclusion]
    exact le_rfl
  have hcomp : F.imageInclusion.app D ≫ F.toImage.app (F.pointChartOpen j₀) =
      F.toProjective.appLE D W hpre := by
    calc
      _ = F.imageInclusion.app D ≫ F.toImage.appLE (F.pointChartOpen j₀) W le_rfl :=
        congrArg (fun f => F.imageInclusion.app D ≫ f)
          (F.toImage.app_eq_appLE (U := F.pointChartOpen j₀))
      _ = (F.toImage ≫ F.imageInclusion).appLE D W le_rfl :=
        (Scheme.Hom.comp_appLE F.toImage F.imageInclusion D W le_rfl).symm
      _ = _ := appLE_eq_of_hom_eq F.toImage_imageInclusion D W le_rfl hpre
  have hr := F.sections_ratio_on j₀ j W hpre
  have he := congrArg (fun f : Γ(ProjectiveSpace A F.index, D) ⟶ Γ(X, W) =>
    f.hom (coordinateRatioSection A F.index j₀ j)) hcomp
  exact hr.trans (congrArg (fun a => a • (F.sections j₀).val.app (op W) (1 : Γ(X, W)))
    he.symm)

end CartierProjectivePresentation

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem cartierKernelMultiply_of_ratio {C : Scheme.{u}} (j : C ⟶ X)
    [IsClosedImmersion j] (hJ : IsLocallyRankOne X (Hom.idealModule j))
    (M : LineBundle X)
    (s : SheafOfModules.unit X.ringCatSheaf ⟶
      (tensorLineBundle X (dualLineBundle X (cartierIdealLineBundle j hJ)) M).val)
    (U : X.Opens) (m : Γ(Hom.idealModule j, U))
    (t : SheafOfModules.unit X.ringCatSheaf ⟶ M.val) (r : Γ(X, U))
    (hm : (Hom.idealInclusion j).val.app (op U) m = r)
    (hr : (t ≫ (cartierStepSequence j hJ M).f).val.app (op U) (1 : Γ(X, U)) =
      r • s.val.app (op U) (1 : Γ(X, U))) :
    (cartierKernelMultiply j hJ M s).val.app (op U) m =
      t.val.app (op U) (1 : Γ(X, U)) := by
  let S := cartierStepSequence j hJ M
  let _ : Mono S.f := (cartierStepSequence_shortExact j hJ M).mono_f
  apply moduleHom_app_injective S.f U
  have hf := congrArg (fun f => f.val.app (op U) m)
    (cartierKernelMultiply_comp j hJ M s)
  change S.f.val.app (op U) ((cartierKernelMultiply j hJ M s).val.app (op U) m) =
    s.val.app (op U) ((Hom.idealInclusion j).val.app (op U) m) at hf
  rw [hm] at hf
  have hs := (s.val.app (op U)).hom.map_smul r (1 : Γ(X, U))
  change s.val.app (op U) (r * (1 : Γ(X, U))) =
    r • s.val.app (op U) (1 : Γ(X, U)) at hs
  rw [mul_one] at hs
  exact hf.trans (hs.trans hr.symm)

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original natural-number index equality identifies the last Cartier line with L_n. -/
def firstOrderTargetIso (n : ℕ) (hn2 : 2 ≤ n * d) :
    (tensorLineBundle X (dualLineBundle X (cartierIdealLineBundle i hI))
      (cartierPowerTwist i hI H n (n * d - 2 + 1))).val ≅
        (cartierPowerTwist i hI H n (n * d)).val :=
  eqToIso (congrArg (fun j => (cartierPowerTwist i hI H n j).val)
    (show n * d - 2 + 1 + 1 = n * d by omega))

namespace CartierProjectivePresentation

variable {p i hI H eP d} {n : ℕ} {hn : 1 ≤ n}
  (F : CartierProjectivePresentation p i hI H eP d n hn)
  (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
    twistingSheaf k (ULift.{u} (Fin 2)) 1)
  (eH : (Scheme.Modules.pullback i).obj H.val ≅
    twistingSheaf k (ULift.{u} (Fin 2)) (d : ℤ))

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original selected section defines multiplication from the actual exceptional ideal. -/
def pointCartierMultiply (hn2 : 2 ≤ n * d) (j₀ : F.index) :
    Hom.idealModule i ⟶ (cartierPowerTwist i hI H n (n * d - 2 + 1)).val :=
  cartierKernelMultiply i hI (cartierPowerTwist i hI H n (n * d - 2 + 1))
    (F.sections j₀ ≫ (firstOrderTargetIso i hI H d n hn2).inv)

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original multiplier is invertible after the actual restriction to the exceptional curve. -/
theorem pointCartierMultiply_pullback_isIso (hn2 : 2 ≤ n * d) (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀))) :
    IsIso ((Scheme.Modules.pullback i).map (F.pointCartierMultiply hn2 j₀)) := by
  let _ : IsIso ((Scheme.Modules.pullback i).map (F.sections j₀)) :=
    F.pullback_selectedSection_isIso eI eH j₀ h₀
  let _ : IsIso ((Scheme.Modules.pullback i).map
      (F.sections j₀ ≫ (firstOrderTargetIso i hI H d n hn2).inv)) := by
    rw [CategoryTheory.Functor.map_comp]
    infer_instance
  exact cartierKernelMultiply_pullback_isIso i hI
    (cartierPowerTwist i hI H n (n * d - 2 + 1)) _

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- On the original selected chart, the actual kernel-coordinate product
is the original first-order lift. -/
theorem pointCartierMultiply_coordinate (hk : IsField k)
    (hn2 : 2 ≤ n * d) (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀)))
    (j : F.index) (t : SheafOfModules.unit X.ringCatSheaf ⟶
      (cartierPowerTwist i hI H n (n * d - 2 + 1)).val)
    (hj : F.sections j = firstOrderCartierImage i hI H d n hn2 t)
    (hz : cartierResidueCoefficient i hI H d eI eH n (F.sections j) = 0) :
    (F.pointCartierMultiply hn2 j₀).val.app (op (F.toImage ⁻¹ᵁ F.pointChartOpen j₀))
        (F.pointChartExceptionalCoordinate eI eH hk j₀ h₀ j hz) =
      t.val.app (op (F.toImage ⁻¹ᵁ F.pointChartOpen j₀))
        (1 : Γ(X, F.toImage ⁻¹ᵁ F.pointChartOpen j₀)) := by
  let W := F.toImage ⁻¹ᵁ F.pointChartOpen j₀
  let N := cartierPowerTwist i hI H n (n * d - 2 + 1)
  let e := firstOrderTargetIso i hI H d n hn2
  let s := F.sections j₀ ≫ e.inv
  let r := (F.toImage.app (F.pointChartOpen j₀)).hom (F.pointChartCoordinate j₀ j)
  have hje : F.sections j ≫ e.inv = t ≫ (cartierStepSequence i hI N).f := by
    rw [hj]
    change (t ≫ (cartierStepSequence i hI N).f ≫ e.hom) ≫ e.inv = _
    calc
      _ = ((t ≫ (cartierStepSequence i hI N).f) ≫ e.hom) ≫ e.inv :=
        congrArg (fun g => g ≫ e.inv)
          (Category.assoc t (cartierStepSequence i hI N).f e.hom).symm
      _ = (t ≫ (cartierStepSequence i hI N).f) ≫ (e.hom ≫ e.inv) :=
        Category.assoc _ _ _
      _ = (t ≫ (cartierStepSequence i hI N).f) ≫ 𝟙 _ :=
        congrArg (fun g => (t ≫ (cartierStepSequence i hI N).f) ≫ g) e.hom_inv_id
      _ = _ := Category.comp_id _
  have hv := congrArg (fun s => s.val.app (op W) (1 : Γ(X, W))) hje
  have hr := congrArg (e.inv.val.app (op W)) (F.pointChart_sections_ratio j₀ j)
  have hlin := (e.inv.val.app (op W)).hom.map_smul r
    ((F.sections j₀).val.app (op W) (1 : Γ(X, W)))
  have hratio : (t ≫ (cartierStepSequence i hI N).f).val.app (op W) (1 : Γ(X, W)) =
      r • s.val.app (op W) (1 : Γ(X, W)) :=
    hv.symm.trans (hr.trans hlin)
  exact cartierKernelMultiply_of_ratio i hI N s W _ t r
    (F.pointChartExceptionalCoordinate_inclusion eI eH hk j₀ h₀ j hz) hratio

end CartierProjectivePresentation

namespace CartierProjectivePresentation

variable {p i hI H eP d} {n : ℕ} {hn : 1 ≤ n}
  (F : CartierProjectivePresentation p i hI H eP d n hn)
  (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
    twistingSheaf k (ULift.{u} (Fin 2)) 1)
  (eH : (Scheme.Modules.pullback i).obj H.val ≅
    twistingSheaf k (ULift.{u} (Fin 2)) (d : ℤ))

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual first-order coordinates generate the pullback of the original canonical map. -/
theorem pointIdealPullback_pullback_epi (hk : IsField k) (hn2 : 2 ≤ n * d)
    (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀)))
    (t : ULift.{u} (Fin 2) → (SheafOfModules.unit X.ringCatSheaf ⟶
      (cartierPowerTwist i hI H n (n * d - 2 + 1)).val))
    (ht : ∀ a, t a ≫ (cartierStepSequence i hI
      (cartierPowerTwist i hI H n (n * d - 2))).g =
        firstOrderQuotientCoordinate i hI H d eI eH n hn2 a)
    (q : ULift.{u} (Fin 2) → F.index)
    (hq : ∀ a, F.sections (q a) = firstOrderCartierImage i hI H d n hn2 (t a)) :
    Epi ((Scheme.Modules.pullback i).map (F.pointIdealPullback eI eH j₀ h₀)) := by
  let U := F.pointChartOpen j₀
  let W := F.toImage ⁻¹ᵁ U
  let hW : i ⁻¹ᵁ W = ⊤ := F.exceptional_preimage_pointChart eI eH hk j₀ h₀
  let c := F.residueToImage eI eH j₀ h₀
  let M : X.Modules := (Scheme.Modules.pullback F.toImage).obj (Hom.idealModule c)
  let φ := F.pointIdealPullback eI eH j₀ h₀
  let K := F.pointCartierMultiply hn2 j₀
  let adj := Scheme.Modules.pullbackPushforwardAdjunction F.toImage
  have hz (a : ULift.{u} (Fin 2)) :
      cartierResidueCoefficient i hI H d eI eH n (F.sections (q a)) = 0 :=
    (congrArg (cartierResidueCoefficient i hI H d eI eH n) (hq a)).trans
      (firstOrderCartierImage_residueCoefficient i hI H d eI eH n hn2 (t a))
  let m (a : ULift.{u} (Fin 2)) := F.pointChartIdealCoordinate eI eH hk j₀ h₀ (q a) (hz a)
  let z (a : ULift.{u} (Fin 2)) : Γ(M, W) :=
    (adj.unit.app (Hom.idealModule c)).val.app (op U) (m a)
  let b (a : ULift.{u} (Fin 2)) := pullbackSectionOn i M W hW (z a)
  have hφ : adj.unit.app (Hom.idealModule c) ≫ (Scheme.Modules.pushforward F.toImage).map φ =
      Hom.idealPushforwardMap c i F.toImage (toSpec k (ULift.{u} (Fin 2)))
        (F.exceptional_toImage_eq eI eH j₀ h₀).symm := by
    change adj.homEquiv _ _ φ = _
    exact Hom.idealPullbackMap_adjoint _ _ _ _ _
  have hn' (a : ULift.{u} (Fin 2)) : φ.val.app (op W) (z a) =
      F.pointChartExceptionalCoordinate eI eH hk j₀ h₀ (q a) (hz a) :=
    congrArg (fun f => f.val.app (op U) (m a)) hφ
  have hrow (a : ULift.{u} (Fin 2)) :
      b a ≫ (Scheme.Modules.pullback i).map φ ≫ (Scheme.Modules.pullback i).map K =
        FromSections.pullbackSection i (t a) := by
    calc
      _ = pullbackSectionOn i (Hom.idealModule i) W hW
          (F.pointChartExceptionalCoordinate eI eH hk j₀ h₀ (q a) (hz a)) ≫
            (Scheme.Modules.pullback i).map K := by
        have hb : b a ≫ (Scheme.Modules.pullback i).map φ =
            pullbackSectionOn i (Hom.idealModule i) W hW
              (F.pointChartExceptionalCoordinate eI eH hk j₀ h₀ (q a) (hz a)) :=
          (pullbackSectionOn_map i φ W hW (z a)).symm.trans
            (congrArg (pullbackSectionOn i (Hom.idealModule i) W hW) (hn' a))
        exact (Category.assoc _ _ _).symm.trans
          (congrArg (fun g => g ≫ (Scheme.Modules.pullback i).map K) hb)
      _ = pullbackSectionOn i (cartierPowerTwist i hI H n (n * d - 2 + 1)).val W hW
          (K.val.app (op W)
            (F.pointChartExceptionalCoordinate eI eH hk j₀ h₀ (q a) (hz a))) :=
        (pullbackSectionOn_map i K W hW _).symm
      _ = pullbackSectionOn i (cartierPowerTwist i hI H n (n * d - 2 + 1)).val
          W hW ((t a).val.app (op W) (1 : Γ(X, W))) :=
        congrArg (pullbackSectionOn i
          (cartierPowerTwist i hI H n (n * d - 2 + 1)).val W hW)
          (F.pointCartierMultiply_coordinate eI eH hk hn2 j₀ h₀ (q a) (t a) (hq a) (hz a))
      _ = _ := pullbackSectionOn_global i (t a) W hW
  have hfac : Sigma.desc b ≫ (Scheme.Modules.pullback i).map φ ≫
      (Scheme.Modules.pullback i).map K = Sigma.desc (FromSections.pulledFamily i t) := by
    apply Sigma.hom_ext
    intro a
    simp only [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc]
    exact hrow a
  let _ : Epi (Sigma.desc (FromSections.pulledFamily i t)) :=
    firstOrder_lifts_pullback_epi i hI H d eI eH n hn2 t ht
  have hepi : Epi (Sigma.desc b ≫ (Scheme.Modules.pullback i).map φ ≫
      (Scheme.Modules.pullback i).map K) := by
    rw [hfac]
    infer_instance
  let _ : Epi ((Scheme.Modules.pullback i).map φ ≫ (Scheme.Modules.pullback i).map K) :=
    epi_of_epi (Sigma.desc b) _
  let _ : IsIso ((Scheme.Modules.pullback i).map K) :=
    F.pointCartierMultiply_pullback_isIso eI eH hn2 j₀ h₀
  exact (epi_comp_iff_of_isIso ((Scheme.Modules.pullback i).map φ)
    ((Scheme.Modules.pullback i).map K)).mp inferInstance

end CartierProjectivePresentation

namespace CartierProjectivePresentation

variable {p i hI H eP d} {n : ℕ} {hn : 1 ≤ n}
  (F : CartierProjectivePresentation p i hI H eP d n hn)
  (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
    twistingSheaf k (ULift.{u} (Fin 2)) 1)
  (eH : (Scheme.Modules.pullback i).obj H.val ≅
    twistingSheaf k (ULift.{u} (Fin 2)) (d : ℤ))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Nakayama for the original canonical map, using actual first-order lifts
and the original off-E maps. -/
theorem pointIdealPullback_epi (r : ℕ) (e : ι ≃ Fin (r + 1))
    (hk : IsField k) (hn2 : 2 ≤ n * d) (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀)))
    (hρ : Function.Surjective ((cartierResidueMap i hI H d eI eH n).val.app (op ⊤)))
    (t : ULift.{u} (Fin 2) → (SheafOfModules.unit X.ringCatSheaf ⟶
      (cartierPowerTwist i hI H n (n * d - 2 + 1)).val))
    (ht : ∀ a, t a ≫ (cartierStepSequence i hI
      (cartierPowerTwist i hI H n (n * d - 2))).g =
        firstOrderQuotientCoordinate i hI H d eI eH n hn2 a)
    (q : ULift.{u} (Fin 2) → F.index)
    (hq : ∀ a, F.sections (q a) = firstOrderCartierImage i hI H d n hn2 (t a)) :
    Epi (F.pointIdealPullback eI eH j₀ h₀) := by
  let _ : Finite ι := Finite.of_equiv (Fin (r + 1)) e.symm
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let _ : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (p ≫ toSpec A ι)
  let _ : IsNoetherian X :=
    { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }
  let L := cartierIdealLineBundle i hI
  let _ : L.val.IsFinitePresentation := lineBundle_isFinitePresentation X L
  let M : QuasiCoherent.FiniteTypeSheaves X :=
    ⟨L.val, QuasiCoherent.affineLocallyFiniteType_of_finitePresentation L.val⟩
  let _ : Epi ((Scheme.Modules.pullback i).map (F.pointIdealPullback eI eH j₀ h₀)) :=
    F.pointIdealPullback_pullback_epi eI eH hk hn2 j₀ h₀ t ht q hq
  apply epi_of_pullback_closedImmersion_of_stalkFinite i
    (F.pointIdealPullback eI eH j₀ h₀)
  · intro y
    exact Stalk.coherent_stalk_finite X M (i y)
  · intro x hx
    let _ : IsIso ((moduleStalk X x).map (F.pointIdealPullback eI eH j₀ h₀)) :=
      F.pointIdealPullback_stalk_isIso_offExceptional eI eH hk (by omega) j₀ h₀ hρ x hx
    infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The same original image-point ideal pulls back to the original exceptional Cartier ideal. -/
theorem pointIdeal_comap_eq (r : ℕ) (e : ι ≃ Fin (r + 1))
    (hk : IsField k) (hn2 : 2 ≤ n * d) (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀)))
    (hρ : Function.Surjective ((cartierResidueMap i hI H d eI eH n).val.app (op ⊤)))
    (t : ULift.{u} (Fin 2) → (SheafOfModules.unit X.ringCatSheaf ⟶
      (cartierPowerTwist i hI H n (n * d - 2 + 1)).val))
    (ht : ∀ a, t a ≫ (cartierStepSequence i hI
      (cartierPowerTwist i hI H n (n * d - 2))).g =
        firstOrderQuotientCoordinate i hI H d eI eH n hn2 a)
    (q : ULift.{u} (Fin 2) → F.index)
    (hq : ∀ a, F.sections (q a) = firstOrderCartierImage i hI H d n hn2 (t a)) :
    (F.pointIdeal eI eH j₀ h₀).comap F.toImage = i.ker := by
  let c := F.residueToImage eI eH j₀ h₀
  let _ : IsClosedImmersion c := F.residueToImage_isClosedImmersion eI eH hk j₀ h₀ hρ
  let _ : Epi (Hom.idealPullbackMap c i F.toImage
      (toSpec k (ULift.{u} (Fin 2))) (F.exceptional_toImage_eq eI eH j₀ h₀).symm) :=
    F.pointIdealPullback_epi eI eH r e hk hn2 j₀ h₀ hρ t ht q hq
  exact Hom.ker_comap_eq_of_idealPullbackMap_epi c i F.toImage
    (toSpec k (ULift.{u} (Fin 2))) (F.exceptional_toImage_eq eI eH j₀ h₀).symm

end CartierProjectivePresentation

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- For every sufficiently large n, the actual constructed image has the original
exceptional ideal as the pullback of its same original residue-point ideal. -/
theorem exists_cartier_projective_pointIdeal
    (r : ℕ) (e : ι ≃ Fin (r + 1))
    (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
      twistingSheaf k (ULift.{u} (Fin 2)) 1)
    (eH : (Scheme.Modules.pullback i).obj H.val ≅
      twistingSheaf k (ULift.{u} (Fin 2)) (d : ℤ))
    (hk : IsField k) (hd : 0 < d) :
    ∃ (B : ℕ) (hB : 1 ≤ B), ∀ (n : ℕ) (hn : B ≤ n),
      ∃ (_hn2 : 2 ≤ n * d)
        (F : CartierProjectivePresentation p i hI H eP d n (hB.trans hn))
        (j₀ : F.index)
        (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀)))
        (ε : (exceptionalComplement i).toScheme ≅ F.imageComplementOpen.toScheme),
        IsClosedImmersion (F.residueToImage eI eH j₀ h₀) ∧
        ε.hom ≫ F.imageComplementOpen.ι = (exceptionalComplement i).ι ≫ F.toImage ∧
        (F.imageComplementOpen : Set F.image) =
          (Set.range (F.residueToImage eI eH j₀ h₀))ᶜ ∧
        i ≫ F.toImage =
          toSpec k (ULift.{u} (Fin 2)) ≫ F.residueToImage eI eH j₀ h₀ ∧
        (F.pointIdeal eI eH j₀ h₀).comap F.toImage = i.ker := by
  obtain ⟨B, hB, h⟩ := exists_cartier_projective_complement p i hI H eP d r e eI eH hk hd
  refine ⟨B, hB, fun n hn => ?_⟩
  obtain ⟨hn2, F, t, q, j₀, h₀, ε, ht, hq, hρ, hc, hε, hcomp, htri⟩ := h n hn
  exact ⟨hn2, F, j₀, h₀, ε, hc, hε, hcomp, htri,
    F.pointIdeal_comap_eq eI eH r e hk hn2 j₀ h₀ hρ t ht q hq⟩

end AlgebraicGeometry.Scheme.Surfaces.Contraction
