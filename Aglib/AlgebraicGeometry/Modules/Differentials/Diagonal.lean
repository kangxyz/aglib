/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Differentials.Diagonal.Affine
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.Restriction
public import Aglib.AlgebraicGeometry.Modules.BaseChange.OpenImmersion.Pullback
public import Aglib.AlgebraicGeometry.Modules.Locality.Exactness

/-!
# The actual diagonal conormal and native relative differentials

`Aglib.AlgebraicGeometry.Modules.Differentials.Diagonal` proves that the
canonical coordinate-difference map is an isomorphism over every affine base.
The original ideal pullback maps and original differential maps commute with
source-open restriction; their affine comparison therefore glues on the
actual source cover.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Modules.Differentials.Diagonal

variable {X Y S : Scheme.{u}}

/-- Comparison of iterated pullback on the original restricted sections. -/
theorem pullbackComp_inv_section (f : X ⟶ Y) (g : Y ⟶ S) (M : S.Modules)
    (U : S.Opens) (V : Y.Opens) (W : X.Opens)
    (hg : V ≤ g ⁻¹ᵁ U) (hf : W ≤ f ⁻¹ᵁ V)
    (hfg : W ≤ (f ≫ g) ⁻¹ᵁ U) (m : Γ(M, U)) :
    ((Scheme.Modules.pullbackComp f g).inv.app M).val.app (op W)
      (pullbackSection (f ≫ g) M U W hfg m) =
    pullbackSection f ((Scheme.Modules.pullback g).obj M) V W hf
      (pullbackSection g M U V hg m) := by
  have hn := PresheafOfModules.naturality_apply
    ((Scheme.Modules.pullbackComp f g).inv.app M).val (homOfLE hfg).op
    (((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app M).val.app (op U) m)
  change ((Scheme.Modules.pullbackComp f g).inv.app M).val.app (op W)
    (pullbackSection (f ≫ g) M U W hfg m) =
    ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M)).val.map
      (homOfLE hfg).op
      (((Scheme.Modules.pullbackComp f g).inv.app M).val.app (op ((f ≫ g) ⁻¹ᵁ U))
        (((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app M).val.app
          (op U) m)) at hn
  rw [pullbackComp_inv_unit_apply] at hn
  refine hn.trans ?_
  have h := pullbackSection_naturality f ((Scheme.Modules.pullback g).obj M) hg le_rfl
    hfg hf (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).val.app (op U) m)
  change ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M)).presheaf.map
    (𝟙 (op W)) _ = _ at h
  rw [((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M)).presheaf.map_id]
    at h
  exact h

/-- A coefficient map commutes with pullback of the same actual section. -/
theorem pullback_map_section (f : X ⟶ Y) {M N : Y.Modules} (φ : M ⟶ N)
    (U : Y.Opens) (V : X.Opens) (h : V ≤ f ⁻¹ᵁ U) (m : Γ(M, U)) :
    ((Scheme.Modules.pullback f).map φ).val.app (op V)
      (pullbackSection f M U V h m) =
    pullbackSection f N U V h (φ.val.app (op U) m) := by
  have hn := PresheafOfModules.naturality_apply ((Scheme.Modules.pullback f).map φ).val
    (homOfLE h).op
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app (op U) m)
  have hu := congrArg (fun q => q.val.app (op U) m)
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality φ)
  exact hn.trans (congrArg (((Scheme.Modules.pullback f).obj N).val.map (homOfLE h).op)
    hu.symm)

/-- Equality transport of pullbacks retains the original restricted section. -/
theorem pullbackCongr_section {f g : X ⟶ Y} (hfg : f = g) (M : Y.Modules)
    (U : Y.Opens) (V : X.Opens) (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U)
    (m : Γ(M, U)) :
    ((Scheme.Modules.pullbackCongr hfg).hom.app M).val.app (op V)
      (pullbackSection f M U V hf m) = pullbackSection g M U V hg m := by
  subst g
  rfl

/-- The ideal pullback mate on original sections of an arbitrary open. -/
theorem idealPullbackMap_unit_apply {D D' : Scheme.{u}} (i : D ⟶ X) (i' : D' ⟶ Y)
    (b : Y ⟶ X) (a : D' ⟶ D) (h : a ≫ i = i' ≫ b) (U : X.Opens)
    (m : Γ(idealModule i, U)) :
    (idealPullbackMap i i' b a h).val.app (op (b ⁻¹ᵁ U))
      (((Scheme.Modules.pullbackPushforwardAdjunction b).unit.app (idealModule i)).val.app
        (op U) m) = (idealPushforwardMap i i' b a h).val.app (op U) m := by
  have he := idealPullbackMap_adjoint i i' b a h
  rw [Adjunction.homEquiv_unit] at he
  exact congrArg (fun q => q.val.app (op U) m) he

/-- The square of source projections preserves their simultaneous section domain. -/
theorem squareMap_preimage_squareOpen (p : X ⟶ S) (j : Y ⟶ X) (U : X.Opens) :
    squareMap p j ⁻¹ᵁ squareOpen p U = squareOpen (j ≫ p) (j ⁻¹ᵁ U) := by
  simp only [squareOpen, Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage]
  simp [squareMap]


theorem module_iso_hom_inv_apply {M N : X.Modules} (e : M ≅ N)
    (U : X.Opens) (n : Γ(N, U)) :
    e.hom.val.app (op U) (e.inv.val.app (op U) n) = n :=
  congrArg (fun q : N ⟶ N => q.val.app (op U) n) e.inv_hom_id

theorem pullbackComp_hom_section (f : X ⟶ Y) (g : Y ⟶ S) (M : S.Modules)
    (U : S.Opens) (V : Y.Opens) (W : X.Opens)
    (hg : V ≤ g ⁻¹ᵁ U) (hf : W ≤ f ⁻¹ᵁ V)
    (hfg : W ≤ (f ≫ g) ⁻¹ᵁ U) (m : Γ(M, U)) :
    ((Scheme.Modules.pullbackComp f g).hom.app M).val.app (op W)
      (pullbackSection f ((Scheme.Modules.pullback g).obj M) V W hf
        (pullbackSection g M U V hg m)) =
    pullbackSection (f ≫ g) M U W hfg m := by
  rw [← pullbackComp_inv_section f g M U V W hg hf hfg m]
  exact module_iso_hom_inv_apply ((Scheme.Modules.pullbackComp f g).app M) W _

theorem conormalPullbackIso_hom (p : X ⟶ S) (j : Y ⟶ X) [IsOpenImmersion j] :
    (conormalPullbackIso p j).hom =
    (Scheme.Modules.pullbackComp j (pullback.diagonal p)).hom.app
      (idealModule (pullback.diagonal p)) ≫
    (Scheme.Modules.pullbackCongr (diagonal_squareMap p j)).hom.app
      (idealModule (pullback.diagonal p)) ≫
    (Scheme.Modules.pullbackComp (pullback.diagonal (j ≫ p)) (squareMap p j)).inv.app
      (idealModule (pullback.diagonal p)) ≫
    (Scheme.Modules.pullback (pullback.diagonal (j ≫ p))).map
      (idealPullbackMap (pullback.diagonal p) (pullback.diagonal (j ≫ p))
        (squareMap p j) j (diagonal_squareMap p j)) := by
  simp only [conormalPullbackIso, Iso.trans_hom, Functor.mapIso_hom, asIso_hom, Iso.symm_hom]
  rfl


/-- A commuting square transports the same actual section under the canonical pullback mate. -/
theorem pullbackSquare_section {D D' : Scheme.{u}} (i : D ⟶ X) (i' : D' ⟶ Y)
    (b : Y ⟶ X) (a : D' ⟶ D) (h : a ≫ i = i' ≫ b)
    (M : X.Modules) (N : Y.Modules) (φ : (Scheme.Modules.pullback b).obj M ⟶ N)
    (W : X.Opens) (U : D.Opens) (V : D'.Opens)
    (hi : U ≤ i ⁻¹ᵁ W) (ha : V ≤ a ⁻¹ᵁ U) (h' : V ≤ i' ⁻¹ᵁ b ⁻¹ᵁ W)
    (m : Γ(M, W)) :
    ((Scheme.Modules.pullbackComp a i).hom.app M ≫
      (Scheme.Modules.pullbackCongr h).hom.app M ≫
      (Scheme.Modules.pullbackComp i' b).inv.app M ≫
      (Scheme.Modules.pullback i').map φ).val.app (op V)
      (pullbackSection a ((Scheme.Modules.pullback i).obj M) U V ha
        (pullbackSection i M W U hi m)) =
    pullbackSection i' N (b ⁻¹ᵁ W) V h'
      (((Scheme.Modules.pullbackPushforwardAdjunction b).homEquiv M N φ).val.app (op W) m) := by
  have h0 : V ≤ (a ≫ i) ⁻¹ᵁ W := ha.trans (a.preimage_mono hi)
  rw [module_comp_apply, module_comp_apply, module_comp_apply,
    pullbackComp_hom_section a i M W U V hi ha h0,
    pullbackCongr_section h M W V h0 h',
    pullbackComp_inv_section i' b M W (b ⁻¹ᵁ W) V le_rfl h' h']
  erw [pullback_map_section i' φ (b ⁻¹ᵁ W) V h']
  rw [pullbackSection_full, Adjunction.homEquiv_unit]
  rfl

/-- The actual conormal restriction carries a section through its original ideal map. -/
theorem conormalPullbackIso_section (p : X ⟶ S) (j : Y ⟶ X) [IsOpenImmersion j]
    (W : (Limits.pullback p p).Opens) (U : X.Opens) (V : Y.Opens)
    (hd : U ≤ (pullback.diagonal p) ⁻¹ᵁ W) (hj : V ≤ j ⁻¹ᵁ U)
    (h' : V ≤ (pullback.diagonal (j ≫ p)) ⁻¹ᵁ (squareMap p j) ⁻¹ᵁ W)
    (m : Γ(idealModule (pullback.diagonal p), W)) :
    (conormalPullbackIso p j).hom.val.app (op V)
      (pullbackSection j (conormal p) U V hj
        (pullbackSection (pullback.diagonal p) (idealModule (pullback.diagonal p))
          W U hd m)) =
    pullbackSection (pullback.diagonal (j ≫ p)) (idealModule (pullback.diagonal (j ≫ p)))
      ((squareMap p j) ⁻¹ᵁ W) V h'
      ((idealPushforwardMap (pullback.diagonal p) (pullback.diagonal (j ≫ p))
        (squareMap p j) j (diagonal_squareMap p j)).val.app (op W) m) := by
  rw [conormalPullbackIso_hom]
  have hs := pullbackSquare_section (pullback.diagonal p) (pullback.diagonal (j ≫ p))
    (squareMap p j) j (diagonal_squareMap p j)
    (idealModule (pullback.diagonal p)) (idealModule (pullback.diagonal (j ≫ p)))
    (idealPullbackMap (pullback.diagonal p) (pullback.diagonal (j ≫ p))
      (squareMap p j) j (diagonal_squareMap p j)) W U V hd hj h' m
  rw [idealPullbackMap_adjoint] at hs
  exact hs

theorem idealPushforwardMap_inclusion_apply {D D' : Scheme.{u}}
    (i : D ⟶ X) (i' : D' ⟶ Y) (b : Y ⟶ X) (a : D' ⟶ D)
    (h : a ≫ i = i' ≫ b) (U : X.Opens) (m : Γ(idealModule i, U)) :
    (idealInclusion i').val.app (op (b ⁻¹ᵁ U))
      ((idealPushforwardMap i i' b a h).val.app (op U) m) =
      b.app U ((idealInclusion i).val.app (op U) m) :=
  congrArg (fun q => q.val.app (op U) m) (idealPushforwardMap_inclusion i i' b a h)

theorem squareMap_first_section (p : X ⟶ S) (j : Y ⟶ X) (U : X.Opens) (a : Γ(X, U)) :
    (squareMap p j).appLE (squareOpen p U) (squareOpen (j ≫ p) (j ⁻¹ᵁ U))
      (squareMap_preimage_squareOpen p j U).ge
      ((pullback.fst p p).appLE U (squareOpen p U) inf_le_left a) =
    (pullback.fst (j ≫ p) (j ≫ p)).appLE (j ⁻¹ᵁ U)
      (squareOpen (j ≫ p) (j ⁻¹ᵁ U)) inf_le_left (j.app U a) := by
  have he : (pullback.fst p p).appLE U (squareOpen p U) inf_le_left ≫
      (squareMap p j).appLE (squareOpen p U) (squareOpen (j ≫ p) (j ⁻¹ᵁ U))
        (squareMap_preimage_squareOpen p j U).ge =
      j.app U ≫ (pullback.fst (j ≫ p) (j ≫ p)).appLE (j ⁻¹ᵁ U)
        (squareOpen (j ≫ p) (j ⁻¹ᵁ U)) inf_le_left := by
    rw [Scheme.Hom.appLE_comp_appLE, ← Scheme.Hom.comp_appLE]
    apply appLE_congr
    simp [squareMap]
  exact congrArg (fun q => q a) he

theorem squareMap_second_section (p : X ⟶ S) (j : Y ⟶ X) (U : X.Opens) (a : Γ(X, U)) :
    (squareMap p j).appLE (squareOpen p U) (squareOpen (j ≫ p) (j ⁻¹ᵁ U))
      (squareMap_preimage_squareOpen p j U).ge
      ((pullback.snd p p).appLE U (squareOpen p U) inf_le_right a) =
    (pullback.snd (j ≫ p) (j ≫ p)).appLE (j ⁻¹ᵁ U)
      (squareOpen (j ≫ p) (j ⁻¹ᵁ U)) inf_le_right (j.app U a) := by
  have he : (pullback.snd p p).appLE U (squareOpen p U) inf_le_right ≫
      (squareMap p j).appLE (squareOpen p U) (squareOpen (j ≫ p) (j ⁻¹ᵁ U))
        (squareMap_preimage_squareOpen p j U).ge =
      j.app U ≫ (pullback.snd (j ≫ p) (j ≫ p)).appLE (j ⁻¹ᵁ U)
        (squareOpen (j ≫ p) (j ⁻¹ᵁ U)) inf_le_right := by
    rw [Scheme.Hom.appLE_comp_appLE, ← Scheme.Hom.comp_appLE]
    apply appLE_congr
    simp [squareMap]
  exact congrArg (fun q => q a) he


/-- The original ideal section is natural under the actual product-square map. -/
theorem idealDifferenceSection_squareMap (p : X ⟶ S) (j : Y ⟶ X)
    (U : X.Opens) (a : Γ(X, U)) :
    (idealModule (pullback.diagonal (j ≫ p))).val.map
      (homOfLE (squareMap_preimage_squareOpen p j U).ge).op
      ((idealPushforwardMap (pullback.diagonal p) (pullback.diagonal (j ≫ p))
        (squareMap p j) j (diagonal_squareMap p j)).val.app (op (squareOpen p U))
        (idealDifferenceSection p U a)) =
    idealDifferenceSection (j ≫ p) (j ⁻¹ᵁ U) (j.app U a) := by
  apply (idealSectionsEquiv (pullback.diagonal (j ≫ p))
    (squareOpen (j ≫ p) (j ⁻¹ᵁ U))).injective
  apply Subtype.ext
  simp only [idealSectionsEquiv_val, PresheafOfModules.naturality_apply,
    idealPushforwardMap_inclusion_apply, idealDifferenceSection_inclusion]
  change (squareMap p j).appLE (squareOpen p U) (squareOpen (j ≫ p) (j ⁻¹ᵁ U))
    (squareMap_preimage_squareOpen p j U).ge
      ((pullback.snd p p).appLE U (squareOpen p U) inf_le_right a -
        (pullback.fst p p).appLE U (squareOpen p U) inf_le_left a) = _
  rw [map_sub, squareMap_first_section, squareMap_second_section]

/-- Pulling back the canonical coordinate difference gives the canonical difference
for the restricted source, under the same original conormal isomorphism. -/
theorem conormalPullbackIso_unit_difference (p : X ⟶ S) (j : Y ⟶ X) [IsOpenImmersion j]
    (U : X.Opens) (a : Γ(X, U)) :
    (conormalPullbackIso p j).hom.val.app (op (j ⁻¹ᵁ U))
      (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app (conormal p)).val.app
        (op U) (difference p U a)) =
    difference (j ≫ p) (j ⁻¹ᵁ U) (j.app U a) := by
  have h' : j ⁻¹ᵁ U ≤ (pullback.diagonal (j ≫ p)) ⁻¹ᵁ
      (squareMap p j) ⁻¹ᵁ squareOpen p U := by
    rw [squareMap_preimage_squareOpen]
    exact squareOpenAlongDiagonal (j ≫ p) (j ⁻¹ᵁ U)
  rw [← pullbackSection_full j (conormal p) U (difference p U a)]
  change (conormalPullbackIso p j).hom.val.app (op (j ⁻¹ᵁ U))
    (pullbackSection j (conormal p) U (j ⁻¹ᵁ U) le_rfl
      (pullbackSection (pullback.diagonal p) (idealModule (pullback.diagonal p))
        (squareOpen p U) U (squareOpenAlongDiagonal p U) (idealDifferenceSection p U a))) = _
  rw [conormalPullbackIso_section p j (squareOpen p U) U (j ⁻¹ᵁ U)
    (squareOpenAlongDiagonal p U) le_rfl h']
  have hn := pullbackSection_naturality (pullback.diagonal (j ≫ p))
    (idealModule (pullback.diagonal (j ≫ p))) (squareMap_preimage_squareOpen p j U).ge
    (V := j ⁻¹ᵁ U) (V' := j ⁻¹ᵁ U) le_rfl h'
    (squareOpenAlongDiagonal (j ≫ p) (j ⁻¹ᵁ U))
    ((idealPushforwardMap (pullback.diagonal p) (pullback.diagonal (j ≫ p))
      (squareMap p j) j (diagonal_squareMap p j)).val.app (op (squareOpen p U))
        (idealDifferenceSection p U a))
  change (conormal (j ≫ p)).presheaf.map (𝟙 (op (j ⁻¹ᵁ U))) _ = _ at hn
  rw [(conormal (j ≫ p)).presheaf.map_id, idealDifferenceSection_squareMap] at hn
  exact hn


/-- The actual differential sheaf commutes with open-source pullback. -/
def differentialPullbackIso (p : X ⟶ S) (j : Y ⟶ X) [IsOpenImmersion j] :
    (Scheme.Modules.pullback j).obj (relativeDifferentialSheaf p) ≅
      relativeDifferentialSheaf (j ≫ p) :=
  ((Scheme.Modules.restrictFunctorIsoPullback j).app (relativeDifferentialSheaf p)).symm ≪≫
    relativeDifferentialRestrictIso p j

theorem differentialPullbackIso_hom (p : X ⟶ S) (j : Y ⟶ X) [IsOpenImmersion j] :
    (differentialPullbackIso p j).hom =
      (Scheme.Modules.restrictFunctorIsoPullback j).inv.app (relativeDifferentialSheaf p) ≫
        relativeDifferentialRestrictHom p j := rfl

/-- The pullback differential isomorphism is the mate of the original restricted derivation. -/
theorem differentialPullbackIso_adjoint (p : X ⟶ S) (j : Y ⟶ X) [IsOpenImmersion j] :
    (Scheme.Modules.pullbackPushforwardAdjunction j).homEquiv _ _
      (differentialPullbackIso p j).hom =
    relativeDifferentialDesc p _
      (pushforwardRelativeDerivation p j _ (relativeDifferentialDerivation (j ≫ p))) := by
  rw [Adjunction.homEquiv_unit, differentialPullbackIso_hom, Functor.map_comp,
    ← Category.assoc, Scheme.Modules.restrictFunctorIsoPullback_inv_adjunction_unit]
  exact ((Scheme.Modules.restrictAdjunction j).homEquiv _ _).apply_symm_apply _

theorem pullback_map_unit_apply (f : X ⟶ Y) {M N : Y.Modules} (φ : M ⟶ N)
    (U : Y.Opens) (m : Γ(M, U)) :
    ((Scheme.Modules.pullback f).map φ).val.app (op (f ⁻¹ᵁ U))
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app (op U) m) =
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).val.app (op U)
      (φ.val.app (op U) m) :=
  (congrArg (fun q => q.val.app (op U) m)
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality φ)).symm

/-- The canonical differential-to-conormal map commutes with source-open pullback. -/
theorem differentialToConormal_pullback (p : X ⟶ S) (j : Y ⟶ X) [IsOpenImmersion j] :
    (Scheme.Modules.pullback j).map (differentialToConormal p) ≫ (conormalPullbackIso p j).hom =
      (differentialPullbackIso p j).hom ≫ differentialToConormal (j ≫ p) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction j).homEquiv _ _).injective
  rw [(Scheme.Modules.pullbackPushforwardAdjunction j).homEquiv_naturality_right
      ((Scheme.Modules.pullback j).map (differentialToConormal p))
      (conormalPullbackIso p j).hom,
    (Scheme.Modules.pullbackPushforwardAdjunction j).homEquiv_naturality_right
      (differentialPullbackIso p j).hom (differentialToConormal (j ≫ p)),
    differentialPullbackIso_adjoint, Adjunction.homEquiv_unit]
  apply relativeDifferentialSheaf_hom_ext p
  intro U a
  change (conormalPullbackIso p j).hom.val.app (op (j ⁻¹ᵁ U.unop))
    (((Scheme.Modules.pullback j).map (differentialToConormal p)).val.app
      (op (j ⁻¹ᵁ U.unop))
      (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app
        (relativeDifferentialSheaf p)).val.app U ((relativeDifferentialDerivation p).d a))) =
    (differentialToConormal (j ≫ p)).val.app (op (j ⁻¹ᵁ U.unop))
      ((relativeDifferentialDesc p _
        (pushforwardRelativeDerivation p j _ (relativeDifferentialDerivation (j ≫ p)))).val.app
          U ((relativeDifferentialDerivation p).d a))
  rw [pullback_map_unit_apply, differentialToConormal_d, conormalPullbackIso_unit_difference,
    relativeDifferentialDesc_d]
  exact (differentialToConormal_d (j ≫ p) (j ⁻¹ᵁ U.unop) (j.app U.unop a)).symm

/-- Invertibility of the canonical comparison passes from the restricted source to
restriction of the original map. -/
theorem differentialToConormal_restrict_isIso (p : X ⟶ S) (j : Y ⟶ X)
    [IsOpenImmersion j] [IsIso (differentialToConormal (j ≫ p))] :
    IsIso ((Scheme.Modules.restrictFunctor j).map (differentialToConormal p)) := by
  have : IsIso ((Scheme.Modules.pullback j).map (differentialToConormal p) ≫
      (conormalPullbackIso p j).hom) := by
    rw [differentialToConormal_pullback]
    infer_instance
  have : IsIso ((Scheme.Modules.pullback j).map (differentialToConormal p)) :=
    IsIso.of_isIso_comp_right _ (conormalPullbackIso p j).hom
  exact (NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback j)
    (differentialToConormal p)).mpr this

/-- For every scheme over an affine base the canonical diagonal-conormal comparison
is an isomorphism, proved on the actual affine source cover. -/
instance differentialToConormal_affineBase_isIso (R : CommRingCat.{u}) (p : X ⟶ Spec R) :
    IsIso (differentialToConormal p) := by
  apply isIso_of_restrict_openCover X.affineBasisCover.X X.affineBasisCover.f
    (fun x => ⟨X.affineBasisCover.idx x, X.affineBasisCover.covers x⟩)
  intro i
  have : IsIso (differentialToConormal (X.affineBasisCover.f i ≫ p)) := by
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.affineBasisCover.f i ≫ p)
    rw [← hφ]
    exact differentialToConormal_specMap_isIso φ
  exact differentialToConormal_restrict_isIso p (X.affineBasisCover.f i)

/-- The actual diagonal conormal is the native relative differential sheaf over an affine base. -/
def conormalIsoOfAffineBase (R : CommRingCat.{u}) (p : X ⟶ Spec R) :
    conormal p ≅ relativeDifferentialSheaf p :=
  (asIso (differentialToConormal p)).symm

end AlgebraicGeometry.Scheme.Modules.Differentials.Diagonal
