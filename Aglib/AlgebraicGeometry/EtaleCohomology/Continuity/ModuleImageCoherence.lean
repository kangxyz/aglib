/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantImages
public import Aglib.AlgebraicGeometry.EtaleCohomology.BaseChangeMap

/-! # Original native module image coherence

The unchanged native ModuleCat-valued inverse and direct images, over an
arbitrary fixed ring, with their original site comparisons. The direct-image
laws are proved on original sections using actual scheme base-change coherence.
No fullness of the underlying abelian functor is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity.NativeModule

universe u r

variable (R : Type r) [Ring R]

attribute [local instance] ModuleCat.Sheaf.hasSheafify

/-- The original module-valued sheaf category in the fixed value universe. -/
abbrev Coefficient (X : Scheme.{u}) :=
  Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)

/-- Native pullback on the actual small etale site. -/
abbrev inverseImage {X S : Scheme.{u}} (f : S ⟶ X) :
    Coefficient R X ⥤ Coefficient R S :=
  (siteBaseChange f).sheafPullback (ModuleCat.{u + 1} R)
    X.smallEtaleTopology S.smallEtaleTopology

/-- Native pushforward on the actual small etale site. -/
abbrev directImage {X S : Scheme.{u}} (f : S ⟶ X) :
    Coefficient R S ⥤ Coefficient R X :=
  (siteBaseChange f).sheafPushforwardContinuous (ModuleCat.{u + 1} R)
    X.smallEtaleTopology S.smallEtaleTopology

/-- The original native image adjunction. -/
abbrev imageAdjunction {X S : Scheme.{u}} (f : S ⟶ X) :
    inverseImage R f ⊣ directImage R f :=
  (siteBaseChange f).sheafAdjunctionContinuous (ModuleCat.{u + 1} R)
    X.smallEtaleTopology S.smallEtaleTopology

instance inverseImage_preservesFiniteLimits {X S : Scheme.{u}} (f : S ⟶ X) :
    PreservesFiniteLimits (inverseImage R f) := by
  have := flat_of_preservesFiniteLimits (siteBaseChange f)
  exact ModuleCat.Sheaf.pullback_preservesFiniteLimits R (siteBaseChange f)
    X.smallEtaleTopology S.smallEtaleTopology

/-- Original identity comparison on native module sections. -/
def directImageIdIso (X : Scheme.{u}) :
    directImage R (𝟙 X) ≅ 𝟭 (Coefficient R X) :=
  Functor.sheafPushforwardContinuousId' (siteBaseChangeId X)
    (ModuleCat.{u + 1} R) X.smallEtaleTopology

/-- Original composition comparison on native module sections. -/
def directImageCompIso {X S T : Scheme.{u}} (f : S ⟶ X) (g : T ⟶ S) :
    directImage R g ⋙ directImage R f ≅ directImage R (g ≫ f) :=
  Functor.sheafPushforwardContinuousComp' (siteBaseChangeComp f g).symm
    (ModuleCat.{u + 1} R) X.smallEtaleTopology S.smallEtaleTopology T.smallEtaleTopology

/-- Equality transport is the original contravariant test-object transport. -/
theorem directImage_eqToHom_hom_app {X S : Scheme.{u}} {f g : S ⟶ X}
    (h : f = g) (F : Coefficient R S) (U : X.Etaleᵒᵖ) :
    (eqToHom (congrArg (fun k => (directImage R k).obj F) h)).hom.app U =
      F.obj.map (eqToHom
        (congrArg (fun k => (siteBaseChange k).obj U.unop) h.symm)).op := by
  subst g
  change (𝟙 _) = F.obj.map (𝟙 _)
  exact (F.obj.map_id _).symm

/-- Direct-image composition associates on the original coefficient sheaf, including
transport between the two parenthesizations of the composite scheme morphism. -/
@[reassoc]
theorem directImageCompIso_assoc_app {X S T V : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) (h : V ⟶ T) (F : Coefficient R V) :
    (directImage R f).map ((directImageCompIso R g h).hom.app F) ≫
        (directImageCompIso R f (h ≫ g)).hom.app F ≫
        (eqToIso (congrArg (fun k => (directImage R k).obj F) (Category.assoc h g f))).hom =
      (directImageCompIso R f g).hom.app ((directImage R h).obj F) ≫
        (directImageCompIso R (g ≫ f) h).hom.app F := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  change F.obj.map
      ((siteBaseChangeComp g h).hom.app ((siteBaseChange f).obj U.unop)).op ≫
      F.obj.map ((siteBaseChangeComp f (h ≫ g)).hom.app U.unop).op ≫
      (eqToHom (congrArg (fun k => (directImage R k).obj F)
        (Category.assoc h g f))).hom.app U =
    F.obj.map ((siteBaseChange h).map ((siteBaseChangeComp f g).hom.app U.unop)).op ≫
      F.obj.map ((siteBaseChangeComp (g ≫ f) h).hom.app U.unop).op
  rw [directImage_eqToHom_hom_app R]
  · simp only [← F.obj.map_comp, ← op_comp]
    apply congrArg F.obj.map
    · apply congrArg Quiver.Hom.op
      · have hs := congrArg
          (fun k => eqToHom (congrArg (fun a => (siteBaseChange a).obj U.unop)
            (Category.assoc h g f).symm) ≫ k) (siteBaseChangeComp_assoc f g h U.unop)
        simpa only [Category.assoc, eqToIso.hom, eqToHom_trans_assoc,
          eqToHom_refl, Category.id_comp] using hs
      · exact Category.assoc h g f

/-- Composition with the source identity retains the original comparison. -/
theorem directImageCompIso_comp_id {X S : Scheme.{u}} (f : S ⟶ X) :
    (directImageCompIso R f (𝟙 S)).symm ≪≫
        Functor.isoWhiskerRight (directImageIdIso R S) (directImage R f) ≪≫
        Functor.leftUnitor (directImage R f) =
      eqToIso (congrArg (fun k : S ⟶ X => directImage R k) (Category.id_comp f)) := by
  apply Iso.ext_inv
  apply NatTrans.ext
  funext F
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
    Functor.leftUnitor_inv_app, Category.id_comp, eqToIso.inv, eqToHom_app]
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  change F.obj.map ((siteBaseChangeId S).hom.app ((siteBaseChange f).obj U.unop)).op ≫
      F.obj.map ((siteBaseChangeComp f (𝟙 S)).hom.app U.unop).op =
    (eqToHom (congrArg (fun k => (directImage R k).obj F)
      (Category.id_comp f).symm)).hom.app U
  rw [directImage_eqToHom_hom_app R (Category.id_comp f).symm]
  rw [← F.obj.map_comp, ← op_comp, siteBaseChangeComp_comp_id]

/-- Direct-image composition with the target identity uses the original identity comparison. -/
theorem directImageCompIso_id_comp {X S : Scheme.{u}} (f : S ⟶ X) :
    (directImageCompIso R (𝟙 X) f).symm ≪≫
        Functor.isoWhiskerLeft (directImage R f) (directImageIdIso R X) ≪≫
        Functor.rightUnitor (directImage R f) =
      eqToIso (congrArg (fun k : S ⟶ X => directImage R k) (Category.comp_id f)) := by
  apply Iso.ext_inv
  apply NatTrans.ext
  funext F
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
    Functor.rightUnitor_inv_app, Category.id_comp, eqToIso.inv, eqToHom_app]
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  change F.obj.map ((siteBaseChange f).map ((siteBaseChangeId X).hom.app U.unop)).op ≫
      F.obj.map ((siteBaseChangeComp (𝟙 X) f).hom.app U.unop).op =
    (eqToHom (congrArg (fun k => (directImage R k).obj F)
      (Category.comp_id f).symm)).hom.app U
  rw [directImage_eqToHom_hom_app R (Category.comp_id f).symm]
  rw [← F.obj.map_comp, ← op_comp, siteBaseChangeComp_id_comp]


end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity.NativeModule
