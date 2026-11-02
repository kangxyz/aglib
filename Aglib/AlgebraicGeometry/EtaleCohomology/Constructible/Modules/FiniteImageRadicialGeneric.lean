/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.FiniteImageRadicialAffineChart
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.FiniteImageRadicialChartCoefficients
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.GenericTrivializationConstructible
public import Aglib.AlgebraicGeometry.Morphisms.Finite.GenericPreimageOpen

/-! # Actual generic finite radicial image local constancy

A known constructible source coefficient is trivialized on an actual finite
etale chart of a dense source open. Finite radicial topology permits shrinking
the target so that its entire source inverse image lies in that open. Actual
geometric chart descent and the original finite-image comparisons then give
local constancy of the original direct image on a nonempty affine target open.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable (R : Type r) [CommRing R]

/-- Generic constructibility for an actual finite surjective radicial map of
integral schemes with Noetherian target and genuine constructible source modules. -/
theorem exists_nonempty_open_finiteRadicialImage_locallyConstant
    {Y X : Scheme.{u}} [IsIntegral Y] [IsIntegral X]
    [IsNoetherian X] (f : Y ⟶ X) [IsFinite f] [Surjective f] [UniversallyInjective f]
    (F : ModuleSheaf R Y) (hF : IsConstructible F) :
    ∃ (B : Scheme.{u}) (b : B ⟶ X), IsAffine B ∧ IsOpenImmersion b ∧ Nonempty B ∧
      IsFiniteTypeLocallyConstant
        ((moduleInverseImage R b).obj ((moduleDirectImage R f).obj F)) := by
  classical
  let t := denseGaloisConstantTrivializationOfConstructible F hF
  let : IsOpenImmersion t.inclusion := t.open_inclusion
  let : ConnectedSpace t.base := t.connected_base
  let : Surjective t.cover.obj.hom := t.surjective_cover
  let : Module.Finite R t.value := t.finite_value
  have ht : genericPoint Y ∈ t.inclusion.opensRange := by
    let x : t.base := Classical.choice inferInstance
    exact (genericPoint_specializes (t.inclusion x)).mem_open
      t.inclusion.opensRange.isOpen ⟨x, rfl⟩
  obtain ⟨U, hUa, hU, -, hUV⟩ := Scheme.exists_affine_open_generic_preimage_subset
    f f.injective t.inclusion.opensRange ht ⊤ (by trivial)
  let : IsAffine U.toScheme := hUa
  let : Nonempty U.toScheme := ⟨⟨genericPoint X, hU⟩⟩
  let : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  let : IsLocallyNoetherian U.toScheme := LocallyOfFiniteType.isLocallyNoetherian U.ι
  let : IsNoetherian U.toScheme := ⟨⟩
  let fU := f ∣_ U
  let : Surjective fU := by
    let H := isPullback_morphismRestrict f U
    have : Surjective (H.isoPullback.hom ≫ pullback.fst U.ι f) := inferInstance
    simpa only [IsPullback.isoPullback_hom_fst] using this
  let : Nonempty (f ⁻¹ᵁ U).toScheme :=
    ⟨Classical.choose (fU.surjective ⟨genericPoint X, hU⟩)⟩
  let : IsIntegral (f ⁻¹ᵁ U).toScheme := isIntegral_of_isOpenImmersion (f ⁻¹ᵁ U).ι
  let : IsAffine (f ⁻¹ᵁ U).toScheme := isAffine_of_isAffineHom fU
  let : MorphismProperty.IsStableUnderBaseChange (@UniversallyInjective.{u}) :=
    UniversallyInjective.isStableUnderBaseChange
  let : UniversallyInjective fU :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @UniversallyInjective.{u}) (isPullback_morphismRestrict f U).flip
      ‹UniversallyInjective f›
  let μ := IsOpenImmersion.lift t.inclusion (f ⁻¹ᵁ U).ι
    (by rw [Opens.range_ι]; exact hUV)
  have hμ : μ ≫ t.inclusion = (f ⁻¹ᵁ U).ι := IsOpenImmersion.lift_fac _ _ _
  let W := (Scheme.FiniteEtale.baseChange μ).obj t.cover
  have : Surjective W.obj.hom :=
    inferInstanceAs (Surjective (pullback.snd t.cover.obj.hom μ))
  let p : W.obj.left ⟶ t.cover.obj.left := pullback.fst t.cover.obj.hom μ
  let FU := (moduleInverseImage R (f ⁻¹ᵁ U).ι).obj F
  have hw : W.obj.hom ≫ (f ⁻¹ᵁ U).ι = p ≫ (t.cover.obj.hom ≫ t.inclusion) := by
    have hp : W.obj.hom ≫ μ = p ≫ t.cover.obj.hom := pullback.condition.symm
    exact (congrArg (fun z => W.obj.hom ≫ z) hμ.symm).trans
      ((Category.assoc W.obj.hom μ t.inclusion).symm.trans
        ((congrArg (fun z => z ≫ t.inclusion) hp).trans
          (Category.assoc p t.cover.obj.hom t.inclusion)))
  let eW : (moduleInverseImage R W.obj.hom).obj FU ≅
      (constantSheaf W.obj.left.smallEtaleTopology (ModuleCat.{u + 1} R)).obj t.value :=
    ((moduleInverseImageComp R (f ⁻¹ᵁ U).ι W.obj.hom).app F).symm ≪≫
      eqToIso (congrArg (fun a => (moduleInverseImage R a).obj F) hw) ≪≫
      (moduleInverseImageComp R (t.cover.obj.hom ≫ t.inclusion) p).app F ≪≫
      (moduleInverseImage R p).mapIso t.iso ≪≫ (moduleInverseImageConstantIso R p).app t.value
  obtain ⟨B, b, hBa, hb, hB, T, hT, a, ha⟩ :=
    exists_affine_radicial_chart_factorization fU W
  let : IsOpenImmersion b := hb
  let : Surjective T.obj.hom := hT
  have hLC := isFiniteTypeLocallyConstant_radicialImage_restrict_of_chart R fU b T.obj.hom
    W.obj.hom a ha FU t.value eW
  let eBC := (finiteImageBaseChangeIso R f fU U.ι (f ⁻¹ᵁ U).ι
    (isPullback_morphismRestrict f U).flip).app F
  let e := (moduleInverseImageComp R U.ι b).app ((moduleDirectImage R f).obj F) ≪≫
    (moduleInverseImage R b).mapIso eBC
  exact ⟨B, b ≫ U.ι, hBa, inferInstance, hB,
    (isFiniteTypeLocallyConstant_iff_of_iso e).mpr hLC⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
