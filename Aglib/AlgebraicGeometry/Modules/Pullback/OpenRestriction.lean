/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Aglib.Algebra.Category.ModuleCat.Presheaf.SheafificationRestriction
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
constructions are imported from the module-presheaf owner.

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

private theorem restrictHomEquiv_symm_app
    {Z T : Scheme.{u}} (j : Z ⟶ T) [IsOpenImmersion j]
    {M : T.Modules} {P : Z.Modules}
    (a : M ⟶ (Scheme.Modules.pushforward j).obj P) (V : Z.Opens) :
    (((Scheme.Modules.restrictAdjunction j).homEquiv M P).symm a).app V =
      a.app (j ''ᵁ V) ≫
        P.presheaf.map (eqToHom (j.preimage_image_eq V).symm).op := by
  rw [Adjunction.homEquiv_counit, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.restrictAdjunction_counit_app_app]
  rfl

private theorem pushforwardSquare_hom_app_app
    (M : (f ⁻¹ᵁ U).toScheme.Modules) (W : Y.Opens) :
    ((pushforwardSquare f U).hom.app M).app W =
      M.presheaf.map (eqToHom (congrArg
        (fun h : (f ⁻¹ᵁ U).toScheme ⟶ Y => h ⁻¹ᵁ W)
        (morphismRestrict_ι f U))).op := by
  dsimp only [pushforwardSquare, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Scheme.Modules.Hom.comp_app]
  simp only [Scheme.Modules.pushforwardComp_hom_app_app,
    Scheme.Modules.pushforwardComp_inv_app_app,
    Scheme.Modules.pushforwardCongr_hom_app_app, Category.id_comp, Category.comp_id]

theorem restrictedPushforwardMap_app (N : X.Modules) (V : U.toScheme.Opens) :
    (restrictedPushforwardMap f U N).app V =
      N.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V)).op := by
  rw [restrictedPushforwardMap, restrictHomEquiv_symm_app,
    Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    Scheme.Modules.restrictAdjunction_unit_app_app, pushforwardSquare_hom_app_app]
  rw [Category.assoc]
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

namespace AlgebraicGeometry.Scheme.Modules
universe u
variable (X : Scheme.{u})

/-- Restrict a supplied over-site unit trivialization to a smaller open. -/
def restrictOverUnitIso (M : SheafOfModules.{u} X.ringCatSheaf) {U V : X.Opens}
    (i : U ⟶ V) (e : M.over V ≅ SheafOfModules.unit (X.ringCatSheaf.over V)) :
    M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U) :=
  ((SheafOfModules.overFunctorMap X.ringCatSheaf i).app M).symm ≪≫
    (SheafOfModules.overMap X.ringCatSheaf i).mapIso e ≪≫
      SheafOfModules.overMapUnitIso (R := X.ringCatSheaf) i

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules
universe u
variable {X : Scheme.{u}}

/-- Transport the over-site structure module to the open subscheme. -/
def overUnitIso (U : X.Opens) :
    (Scheme.Modules.overEquiv U).functor.obj (SheafOfModules.unit (X.ringCatSheaf.over U)) ≅
      SheafOfModules.unit U.toScheme.ringCatSheaf :=
  (Scheme.Modules.overFunctorEquiv U).app (SheafOfModules.unit X.ringCatSheaf) ≪≫
    Scheme.Modules.restrictUnitIso U.ι

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules.Pullback.OpenRestriction
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)

theorem restrictedUnit (M : Y.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app
        ((Scheme.Modules.restrictFunctor U.ι).obj M) ≫
      (Scheme.Modules.pushforward (f ∣_ U)).map ((localPullbackIso f U).inv.app M) =
    (Scheme.Modules.restrictFunctor U.ι).map
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) ≫
      restrictedPushforwardMap f U ((Scheme.Modules.pullback f).obj M) := by
  let A := Scheme.Modules.pullbackPushforwardAdjunction f
  let B := Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)
  let φ := (Scheme.Modules.restrictFunctor U.ι).map (A.unit.app M) ≫
    restrictedPushforwardMap f U ((Scheme.Modules.pullback f).obj M)
  have h := restrictedAdjoint_eq f U (A.unit.app M)
  have hi : (A.homEquiv _ _).symm (A.unit.app M) = 𝟙 _ := A.homEquiv_symm_unit M
  rw [hi, CategoryTheory.Functor.map_id] at h
  have he : (B.homEquiv _ _).symm φ = (localPullbackIso f U).inv.app M := by
    apply (cancel_epi ((localPullbackIso f U).hom.app M)).mp
    exact h.symm.trans (Iso.hom_inv_id_app (localPullbackIso f U) M).symm
  have hh := congrArg (B.homEquiv _ _) he
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit] at hh
  exact hh.symm

theorem restrictedPushforwardMap_apply (M : X.Modules) (W : U.toScheme.Opensᵒᵖ)
    (m : ((Scheme.Modules.restrictFunctor U.ι).obj
      ((Scheme.Modules.pushforward f).obj M)).val.obj W) :
    (restrictedPushforwardMap f U M).val.app W m =
      M.val.map (eqToHom (image_morphismRestrict_preimage f U W.unop)).op m := by
  exact congrArg (fun k ↦ k m) (restrictedPushforwardMap_app f U M W.unop)

end AlgebraicGeometry.Scheme.Modules.Pullback.OpenRestriction
