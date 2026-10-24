/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ConnectedTorsionSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.EtaleRestriction

/-! # Original constant-module pullback on sections

The native constant pullback is the mate of the native inverse-image unit and
terminal-object transport. On an etale chart this is the literal original
restriction. No torsion or finiteness hypothesis is needed for these equations.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable (R : Type r) [CommRing R] {X S : Scheme.{u}}

/-- Actual direct-image global sections with the original terminal transport. -/
def moduleDirectImageGlobalSectionsIso (f : S ⟶ X) :
    moduleDirectImage R f ⋙ moduleGlobalSections R X ≅ moduleGlobalSections R S :=
  NatIso.ofComponents (fun F => F.obj.mapIso (siteBaseChangeTerminalIso f).symm.op)
    (fun a => (a.hom.naturality (siteBaseChangeTerminalIso f).inv.op).symm)

/-- The original inverse-image unit induces the original map on global sections. -/
def moduleGlobalSectionsPullback (f : S ⟶ X) (F : ModuleSheaf R X) :
    (moduleGlobalSections R X).obj F ⟶
      (moduleGlobalSections R S).obj ((moduleInverseImage R f).obj F) :=
  (moduleGlobalSections R X).map ((moduleImageAdjunction R f).unit.app F) ≫
    (moduleDirectImageGlobalSectionsIso R f).hom.app ((moduleInverseImage R f).obj F)

/-- The fixed-terminal mate used to compare the original constant functors. -/
def moduleInverseImageConstantCanonicalIso (f : S ⟶ X) :
    constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R) ⋙ moduleInverseImage R f ≅
      constantSheaf S.smallEtaleTopology (ModuleCat.{u + 1} R) :=
  Adjunction.leftAdjointCompIso (moduleConstantAdjunction R X) (moduleImageAdjunction R f)
    (moduleConstantAdjunction R S) (moduleDirectImageGlobalSectionsIso R f)

/-- The fixed-terminal mate is the original native constant-pullback isomorphism. -/
theorem moduleInverseImageConstantCanonicalIso_eq (f : S ⟶ X) :
    moduleInverseImageConstantCanonicalIso R f = moduleInverseImageConstantIso R f := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  let cAdj := moduleConstantAdjunction R X
  let adj := moduleImageAdjunction R f
  let targetAdj := constantSheafAdj S.smallEtaleTopology (ModuleCat.{u + 1} R)
    ((etaleTerminalIsTerminal X).isTerminalObj (siteBaseChange f))
  apply ((cAdj.comp adj).homEquiv _ _).injective
  refine Eq.trans (unit_conjugateEquiv_symm (moduleConstantAdjunction R S)
    (cAdj.comp adj) (moduleDirectImageGlobalSectionsIso R f).inv M).symm ?_
  refine Eq.trans ?_ (Adjunction.homEquiv_leftAdjointUniq_hom_app
    (cAdj.comp adj) targetAdj M).symm
  change (toSheafify S.smallEtaleTopology ((Functor.const S.Etaleᵒᵖ).obj M)).app
      (op (etaleTerminal S)) ≫
    (sheafify S.smallEtaleTopology ((Functor.const S.Etaleᵒᵖ).obj M)).map
      (siteBaseChangeTerminalIso f).hom.op =
    (toSheafify S.smallEtaleTopology ((Functor.const S.Etaleᵒᵖ).obj M)).app
      (op ((siteBaseChange f).obj (etaleTerminal X)))
  exact ((toSheafify S.smallEtaleTopology ((Functor.const S.Etaleᵒᵖ).obj M)).naturality
    (siteBaseChangeTerminalIso f).hom.op).symm.trans (Category.id_comp _)

/-- Constant-source pullback retains the original adjunction and section map. -/
theorem moduleConstantTransport_homEquiv (f : S ⟶ X) (M : ModuleCat.{u + 1} R)
    {F : ModuleSheaf R X}
    (a : (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M ⟶ F) :
    (moduleConstantAdjunction R S).homEquiv M _
      (((moduleInverseImageConstantIso R f).app M).inv ≫ (moduleInverseImage R f).map a) =
    (moduleConstantAdjunction R X).homEquiv M F a ≫ moduleGlobalSectionsPullback R f F := by
  rw [← moduleInverseImageConstantCanonicalIso_eq R f]
  let cX := moduleConstantAdjunction R X
  let cS := moduleConstantAdjunction R S
  let adj := moduleImageAdjunction R f
  let e := moduleDirectImageGlobalSectionsIso R f
  let k := moduleInverseImageConstantCanonicalIso R f
  have ht : (cX.comp adj).unit.app M ≫ e.hom.app _ =
      cS.unit.app M ≫ (moduleGlobalSections R S).map (k.inv.app M) := by
    have h := unit_conjugateEquiv (cX.comp adj) cS k.inv M
    simpa only [cX, cS, adj, e, k, moduleInverseImageConstantCanonicalIso,
      Adjunction.conjugateEquiv_leftAdjointCompIso_inv] using h
  change cS.homEquiv M _ (k.inv.app M ≫ (moduleInverseImage R f).map a) =
    cX.homEquiv M F a ≫ ((moduleGlobalSections R X).map (adj.unit.app F) ≫ e.hom.app _)
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc, ← ht,
    Category.assoc, ← e.hom.naturality, ← Category.assoc,
    Adjunction.comp_unit_app]
  change (cX.unit.app M ≫ (moduleGlobalSections R X).map (adj.unit.app _)) ≫
      (moduleGlobalSections R X).map
        ((moduleDirectImage R f).map ((moduleInverseImage R f).map a)) ≫ e.hom.app _ = _
  have hn := adj.unit.naturality a
  change a ≫ adj.unit.app F =
    adj.unit.app _ ≫ (moduleDirectImage R f).map ((moduleInverseImage R f).map a) at hn
  have hm := congrArg (moduleGlobalSections R X).map hn.symm
  simp only [Functor.map_comp] at hm
  rw [Adjunction.homEquiv_unit]
  simpa only [Category.assoc, constantSheaf, Functor.comp_obj] using
    congrArg (fun t => cX.unit.app M ≫ t ≫ e.hom.app ((moduleInverseImage R f).obj F)) hm

/-- On every original test object, the etale comparison sends the unit to the site counit. -/
@[reassoc]
theorem moduleInverseImageEtaleIso_unit_app (f : S ⟶ X) [Etale f]
    (F : ModuleSheaf R X) (U : X.Etale) :
    ((moduleImageAdjunction R f).unit.app F).hom.app (op U) ≫
      ((moduleInverseImageEtaleIso R f).hom.app F).hom.app
        (op ((siteBaseChange f).obj U)) =
    F.obj.map ((siteEtalePostcomposeAdj f).counit.app U).op := by
  exact congrArg (fun a => a.hom.app (op U)) (moduleInverseImageEtaleIso_unit R f F)

/-- Original global-section pullback on an etale chart is literal restriction. -/
@[reassoc]
theorem moduleGlobalSectionsPullback_etale (f : S ⟶ X) [Etale f]
    (F : ModuleSheaf R X) :
    moduleGlobalSectionsPullback R f F ≫
      (moduleGlobalSections R S).map ((moduleInverseImageEtaleIso R f).hom.app F) =
    F.obj.map ((etaleTerminalIsTerminal X).from
      ((siteEtalePostcompose f).obj (etaleTerminal S))).op := by
  let e := (moduleInverseImageEtaleIso R f).hom.app F
  let t := (siteBaseChangeTerminalIso f).inv
  have hn := e.hom.naturality t.op
  change ((moduleInverseImage R f).obj F).obj.map t.op ≫
      e.hom.app (op (etaleTerminal S)) =
    e.hom.app (op ((siteBaseChange f).obj (etaleTerminal X))) ≫
      F.obj.map ((siteEtalePostcompose f).map t).op at hn
  change (((moduleImageAdjunction R f).unit.app F).hom.app (op (etaleTerminal X)) ≫
      ((moduleInverseImage R f).obj F).obj.map t.op) ≫
        e.hom.app (op (etaleTerminal S)) = _
  rw [Category.assoc, hn, ← Category.assoc, moduleInverseImageEtaleIso_unit_app,
    ← Functor.map_comp, ← op_comp]
  congr 1
  exact congrArg Quiver.Hom.op ((etaleTerminalIsTerminal X).hom_ext _ _)

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
