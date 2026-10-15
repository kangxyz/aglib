/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: R5Lab contributors
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

/-!
# Open restriction and the pullback adjunction

The actual direct-image square for a restricted scheme morphism induces
a canonical local pullback isomorphism by uniqueness of left adjoints.
The restriction/direct-image comparison is proved on sections and is an
isomorphism. Restricting an adjoint morphism agrees, through this canonical
local isomorphism, with the adjoint of the restricted morphism.
These are identities for arbitrary structure-module sheaves and use no
base-change theorem-family premise. An open-local isomorphism criterion
is included. The supporting generic over-restriction and sheafification
constructions have their single implementation here, below the invertible tier.

Extraction sources: `R5Lab.AlgebraicGeometry.Curves.Picard.PullbackLocal`,
`R5Lab.AlgebraicGeometry.Curves.Picard.Tensor`, and
`R5Lab.AlgebraicGeometry.Curves.Picard.TensorAssociator`
at revision `95a3772b895fbc19a81684be4ffd519d0fdcd6b3`.
The primary namespace is `AlgebraicGeometry.Scheme.Modules.Pullback.OpenRestriction`;
source names are provenance.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
namespace PresheafOfModules.Restriction
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (R : Sheaf J RingCat.{u})
variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (U : C)
variable [HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
variable [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Restriction of module presheaves to the slice over U, with the identity scalar map. -/
def restrictPresheaf : _root_.PresheafOfModules.{u} R.obj ⥤
    _root_.PresheafOfModules.{u} (R.over U).obj :=
  _root_.PresheafOfModules.pushforward (F := Over.forget U) (𝟙 _)

/-- The actual module sheafification unit restricted to the slice over U. -/
def restrictedSheafificationUnit (P : _root_.PresheafOfModules.{u} R.obj) :
    (restrictPresheaf R U).obj P ⟶
      ((_root_.PresheafOfModules.sheafification (𝟙 R.obj)).obj P).over U |>.val :=
  (restrictPresheaf R U).map
    ((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app P)

omit [HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}] in
theorem restrictedSheafificationUnit_locallyInjective (P : _root_.PresheafOfModules.{u} R.obj) :
    _root_.PresheafOfModules.IsLocallyInjective (J.over U)
      (restrictedSheafificationUnit R U P) := by
  change Presheaf.IsLocallyInjective (J.over U)
    (Functor.whiskerLeft (Over.forget U).op (CategoryTheory.toSheafify J P.presheaf))
  exact Presheaf.isLocallyInjective_whisker (J.over U) J (Over.forget U) _

omit [HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}] in
theorem restrictedSheafificationUnit_locallySurjective (P : _root_.PresheafOfModules.{u} R.obj) :
    _root_.PresheafOfModules.IsLocallySurjective (J.over U)
      (restrictedSheafificationUnit R U P) := by
  change Presheaf.IsLocallySurjective (J.over U)
    (Functor.whiskerLeft (Over.forget U).op (CategoryTheory.toSheafify J P.presheaf))
  exact Presheaf.isLocallySurjective_whisker (J.over U) J (Over.forget U) _

theorem restrictedSheafificationUnit_sheafification_iso (P : _root_.PresheafOfModules.{u} R.obj) :
    IsIso ((_root_.PresheafOfModules.sheafification (𝟙 (R.over U).obj)).map
      (restrictedSheafificationUnit R U P)) := by
  apply Functor.IsLocalization.inverts
    (W := (J.over U).W.inverseImage (_root_.PresheafOfModules.toPresheaf (R.over U).obj))
  change (J.over U).W ((_root_.PresheafOfModules.toPresheaf (R.over U).obj).map
    (restrictedSheafificationUnit R U P))
  rw [(J.over U).W_iff_isLocallyBijective]
  exact ⟨restrictedSheafificationUnit_locallyInjective R U P,
    restrictedSheafificationUnit_locallySurjective R U P⟩

/-- Sheafification of slice restriction compared with slice restriction of sheafification. -/
def sheafificationOverIso (P : _root_.PresheafOfModules.{u} R.obj) :
    (_root_.PresheafOfModules.sheafification (𝟙 (R.over U).obj)).obj
      ((restrictPresheaf R U).obj P) ≅
      ((_root_.PresheafOfModules.sheafification (𝟙 R.obj)).obj P).over U := by
  let S : SheafOfModules.{u} (R.over U) :=
    ((_root_.PresheafOfModules.sheafification (𝟙 R.obj)).obj P).over U
  let f : (_root_.PresheafOfModules.sheafification (𝟙 (R.over U).obj)).obj
      ((restrictPresheaf R U).obj P) ⟶
      (_root_.PresheafOfModules.sheafification (𝟙 (R.over U).obj)).obj S.val :=
    (_root_.PresheafOfModules.sheafification (𝟙 (R.over U).obj)).map
      (restrictedSheafificationUnit R U P)
  have hf : IsIso f := restrictedSheafificationUnit_sheafification_iso R U P
  let c := (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 (R.over U).obj)).counit.app S
  have hc : IsIso c := inferInstance
  exact asIso f ≪≫ asIso c

end PresheafOfModules.Restriction

namespace PresheafOfModules
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R : Cᵒᵖ ⥤ RingCat.{u}}
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
theorem isIso_of_locallyBijective {P Q : _root_.PresheafOfModules.{u} R} (f : P ⟶ Q)
    (hP : Presheaf.IsSheaf J P.presheaf) (hQ : Presheaf.IsSheaf J Q.presheaf)
    [_root_.PresheafOfModules.IsLocallyInjective J f]
    [_root_.PresheafOfModules.IsLocallySurjective J f] :
    IsIso f := by
  let eP := _root_.PresheafOfModules.homEquivOfIsLocallyBijective (J := J) f hP
  let eQ := _root_.PresheafOfModules.homEquivOfIsLocallyBijective (J := J) f hQ
  let g : Q ⟶ P := eP.symm (𝟙 P)
  have hfg : f ≫ g = 𝟙 P := eP.apply_symm_apply _
  have hgf : g ≫ f = 𝟙 Q := by
    apply eQ.injective
    change f ≫ (g ≫ f) = f ≫ 𝟙 Q
    rw [← Category.assoc, hfg, Category.id_comp, Category.comp_id]
  exact ⟨⟨g, hfg, hgf⟩⟩
end PresheafOfModules

namespace AlgebraicGeometry.Scheme.Modules
universe u
variable (X : Scheme.{u})

/-- Being an isomorphism on neighborhoods implies actual local bijectivity. -/
theorem locallyBijective_of_local_isIso {P Q : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj}
    (f : P ⟶ Q) (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      IsIso ((_root_.PresheafOfModules.Restriction.restrictPresheaf X.ringCatSheaf U).map f)) :
    _root_.PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X) f ∧
      _root_.PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X) f := by
  constructor
  · constructor
    intro V s t hst x hxV
    obtain ⟨U, hxU, hf⟩ := h x
    let W := U ⊓ V.unop
    let i : W ⟶ V.unop := homOfLE inf_le_right
    have : IsIso
        (((_root_.PresheafOfModules.Restriction.restrictPresheaf X.ringCatSheaf U).map f).app
        (op (Over.mk (homOfLE (show W ≤ U from inf_le_left))))) := by
      let := hf
      exact Functor.map_isIso
        (_root_.PresheafOfModules.evaluation (X.ringCatSheaf.over U).obj
          (op (Over.mk (homOfLE (show W ≤ U from inf_le_left)))))
        ((_root_.PresheafOfModules.Restriction.restrictPresheaf X.ringCatSheaf U).map f)
    refine ⟨W, i, ?_, hxU, hxV⟩
    apply (ConcreteCategory.bijective_of_isIso
      (((_root_.PresheafOfModules.Restriction.restrictPresheaf X.ringCatSheaf U).map f).app
        (op (Over.mk (homOfLE (show W ≤ U from inf_le_left)))))).injective
    change f.app (op W) (P.map i.op s) = f.app (op W) (P.map i.op t)
    rw [_root_.PresheafOfModules.naturality_apply, _root_.PresheafOfModules.naturality_apply]
    exact congrArg (Q.map i.op) hst
  · constructor
    intro V s x hxV
    obtain ⟨U, hxU, hf⟩ := h x
    let W := U ⊓ V
    let i : W ⟶ V := homOfLE inf_le_right
    have : IsIso
        (((_root_.PresheafOfModules.Restriction.restrictPresheaf X.ringCatSheaf U).map f).app
        (op (Over.mk (homOfLE (show W ≤ U from inf_le_left))))) := by
      let := hf
      exact Functor.map_isIso
        (_root_.PresheafOfModules.evaluation (X.ringCatSheaf.over U).obj
          (op (Over.mk (homOfLE (show W ≤ U from inf_le_left)))))
        ((_root_.PresheafOfModules.Restriction.restrictPresheaf X.ringCatSheaf U).map f)
    refine ⟨W, i, ?_, hxU, hxV⟩
    exact (ConcreteCategory.bijective_of_isIso
      (((_root_.PresheafOfModules.Restriction.restrictPresheaf X.ringCatSheaf U).map f).app
        (op (Over.mk (homOfLE (show W ≤ U from inf_le_left)))))).surjective (Q.map i.op s)

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules.Pullback.OpenRestriction
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)

/-- The actual pushforward square coming from the restricted morphism. -/
def pushforwardSquare :
    Scheme.Modules.pushforward (f ⁻¹ᵁ U).ι ⋙ Scheme.Modules.pushforward f ≅
      Scheme.Modules.pushforward (f ∣_ U) ⋙ Scheme.Modules.pushforward U.ι :=
  Scheme.Modules.pushforwardComp (f ⁻¹ᵁ U).ι f ≪≫
    Scheme.Modules.pushforwardCongr (morphismRestrict_ι f U).symm ≪≫
      (Scheme.Modules.pushforwardComp (f ∣_ U) U.ι).symm

/-- The composite adjunction for pullback along f followed by restriction to the inverse-image
open. -/
def restrictedLeftAdjunction :
    Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι ⊣
      Scheme.Modules.pushforward (f ⁻¹ᵁ U).ι ⋙ Scheme.Modules.pushforward f :=
  (Scheme.Modules.pullbackPushforwardAdjunction f).comp
    (Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι)

/-- Target-open restriction followed by restricted pullback, with the same composite right
adjoint. -/
def restrictedRightAdjunction :
    Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback (f ∣_ U) ⊣
      Scheme.Modules.pushforward (f ⁻¹ᵁ U).ι ⋙ Scheme.Modules.pushforward f :=
  ((Scheme.Modules.restrictAdjunction U.ι).comp
    (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U))).ofNatIsoRight
      (pushforwardSquare f U).symm

/-- The canonical local pullback square, obtained from the actual pushforward
square by adjunction. -/
def localPullbackIso :
    Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι ≅
      Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback (f ∣_ U) :=
  (restrictedLeftAdjunction f U).leftAdjointUniq (restrictedRightAdjunction f U)

/-- The actual restriction/direct-image base-change map, using the open-restriction unit. -/
def restrictedPushforwardMap (N : X.Modules) :
    (Scheme.Modules.restrictFunctor U.ι).obj ((Scheme.Modules.pushforward f).obj N) ⟶
      (Scheme.Modules.pushforward (f ∣_ U)).obj
        ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj N) :=
  ((Scheme.Modules.restrictAdjunction U.ι).homEquiv _ _).symm
    ((Scheme.Modules.pushforward f).map
      ((Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι).unit.app N) ≫
      (pushforwardSquare f U).hom.app _)

set_option maxHeartbeats 400000 in
-- The sectionwise restriction/direct-image comparison uses 256000 heartbeats
-- after the comparison is unfolded separately.
theorem restrictedPushforwardMap_app (N : X.Modules) (V : U.toScheme.Opens) :
    (restrictedPushforwardMap f U N).app V =
      N.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V)).op := by
  unfold restrictedPushforwardMap
  rw [Adjunction.homEquiv_counit]
  simp only [Functor.map_comp, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.restrictAdjunction_counit_app_app]
  rw [Category.assoc]
  change ((Scheme.Modules.pushforward f).map
      ((Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι).unit.app N)).app (U.ι ''ᵁ V) ≫
    ((pushforwardSquare f U).hom.app _).app (U.ι ''ᵁ V) ≫ _ = _
  dsimp only [pushforwardSquare, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Scheme.Modules.Hom.comp_app]
  simp only [Scheme.Modules.pushforward_map_app, Scheme.Modules.restrictAdjunction_unit_app_app,
    Scheme.Modules.pushforwardComp_hom_app_app, Scheme.Modules.pushforwardComp_inv_app_app,
    Scheme.Modules.pushforwardCongr_hom_app_app, Category.id_comp, Category.comp_id]
  simp only [Scheme.Modules.pushforward_obj_presheaf_map, Scheme.Modules.restrict_map]
  change N.presheaf.map _ ≫ N.presheaf.map _ ≫ N.presheaf.map _ = N.presheaf.map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

theorem restrictedPushforwardMap_isIso (N : X.Modules) :
    IsIso (restrictedPushforwardMap f U N) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro V
  rw [restrictedPushforwardMap_app]
  infer_instance

/-- The canonical comparison between restricting direct image and direct image of the
inverse-image restriction. -/
def restrictedPushforwardIso (N : X.Modules) :
    (Scheme.Modules.restrictFunctor U.ι).obj ((Scheme.Modules.pushforward f).obj N) ≅
      (Scheme.Modules.pushforward (f ∣_ U)).obj
        ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj N) :=
  letI := restrictedPushforwardMap_isIso f U N
  asIso (restrictedPushforwardMap f U N)

theorem localPullbackIso_hom_adjoint (M : Y.Modules) (N : (f ⁻¹ᵁ U).toScheme.Modules)
    (h : (Scheme.Modules.pullback (f ∣_ U)).obj ((Scheme.Modules.restrictFunctor U.ι).obj M) ⟶ N) :
    (restrictedLeftAdjunction f U).homEquiv M N ((localPullbackIso f U).hom.app M ≫ h) =
      (restrictedRightAdjunction f U).homEquiv M N h := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
  unfold localPullbackIso
  rw [Adjunction.unit_leftAdjointUniq_hom_app]

/-- Restricting an actual adjoint agrees with adjoining the actual restricted map. -/
theorem restrictedAdjoint_eq {M : Y.Modules} {N : X.Modules}
    (φ : M ⟶ (Scheme.Modules.pushforward f).obj N) :
    (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map
        (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv M N).symm φ) =
      (localPullbackIso f U).hom.app M ≫
        ((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).homEquiv _ _).symm
          ((Scheme.Modules.restrictFunctor U.ι).map φ ≫ restrictedPushforwardMap f U N) := by
  apply ((restrictedLeftAdjunction f U).homEquiv _ _).injective
  rw [localPullbackIso_hom_adjoint]
  simp only [restrictedLeftAdjunction, restrictedRightAdjunction,
    Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
  let ψ := ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv M N).symm φ
  change (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
      ((Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι).homEquiv _ _
        ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map ψ)) =
    (Scheme.Modules.restrictAdjunction U.ι).homEquiv _ _
      ((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).homEquiv _ _
        (((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).homEquiv _ _).symm
          ((Scheme.Modules.restrictFunctor U.ι).map φ ≫ restrictedPushforwardMap f U N))) ≫
      (pushforwardSquare f U).inv.app _
  rw [Equiv.apply_symm_apply,
    Adjunction.homEquiv_unit (Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι)]
  rw [Adjunction.unit_naturality, Adjunction.homEquiv_naturality_right,
    Equiv.apply_symm_apply, Adjunction.homEquiv_naturality_left]
  unfold restrictedPushforwardMap
  rw [Equiv.apply_symm_apply]
  simp only [Category.assoc, Iso.hom_inv_id_app]
  exact congrArg (fun h => φ ≫ h) (Category.comp_id
    ((Scheme.Modules.pushforward f).map
      ((Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι).unit.app N))).symm
/-- Isomorphisms of module sheaves can be checked on an open neighborhood of every point. -/
theorem isIso_of_local_restrict {M N : SheafOfModules.{u} X.ringCatSheaf} (φ : M ⟶ N)
    (h : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧
      IsIso ((Scheme.Modules.restrictFunctor V.ι).map φ)) : IsIso φ := by
  have hh := locallyBijective_of_local_isIso X φ.val (by
    intro x
    obtain ⟨V, hxV, hv⟩ := h x
    let := hv
    let : IsIso ((Scheme.Modules.overEquiv V).functor.map
        ((SheafOfModules.overFunctor X.ringCatSheaf V).map φ)) :=
      (NatIso.isIso_map_iff (Scheme.Modules.overFunctorEquiv V) φ).mpr hv
    let : IsIso ((SheafOfModules.overFunctor X.ringCatSheaf V).map φ) :=
      isIso_of_reflects_iso _ (Scheme.Modules.overEquiv V).functor
    refine ⟨V, hxV, ?_⟩
    exact Functor.map_isIso (SheafOfModules.forget (X.ringCatSheaf.over V))
      ((SheafOfModules.overFunctor X.ringCatSheaf V).map φ))
  let := hh.1
  let := hh.2
  let : IsIso ((SheafOfModules.forget X.ringCatSheaf).map φ) :=
    _root_.PresheafOfModules.isIso_of_locallyBijective φ.val M.isSheaf N.isSheaf
  exact isIso_of_reflects_iso φ (SheafOfModules.forget _)
end AlgebraicGeometry.Scheme.Modules.Pullback.OpenRestriction
