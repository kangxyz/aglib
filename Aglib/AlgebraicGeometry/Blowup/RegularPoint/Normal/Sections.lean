/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.RegularPoint.Normal.Frames
public import Aglib.AlgebraicGeometry.Modules.InternalHom.Restriction
public import Aglib.AlgebraicGeometry.Modules.Restriction.Unit
public import Aglib.AlgebraicGeometry.Modules.Invertible.Trivialization

/-!
# Original restriction-frame coefficients on the blowup centre

Actual open-chart frames descend to their original ranges through the native restriction
Hom equivalence. Their coefficient and generator maps retain actual restriction and
pullback composition. The original Laurent overlap then detects the conormal coefficient.
No section, frame or cocycle comparison family is supplied as a premise.
-/

@[expose] public section
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open Scheme.Hom Scheme.Modules Scheme.Modules.Invertible
open Scheme.Blowup.IdealFrames

universe u

namespace AlgebraicGeometry.Scheme.Blowup.RegularPoint

open CategoryTheory AlgebraicGeometry Scheme.Modules
open Scheme.Modules.InternalHom

variable {W X : Scheme.{u}} (j : W ⟶ X) [IsOpenImmersion j]

private theorem rangeHomToRestriction_comp {M N P : X.Modules}
    (a : M.over j.opensRange ⟶ N.over j.opensRange)
    (b : N.over j.opensRange ⟶ P.over j.opensRange) :
    rangeHomToRestriction j (a ≫ b) =
      rangeHomToRestriction j a ≫ rangeHomToRestriction j b := by
  ext V m
  rfl

private theorem rangeHomToRestriction_id (M : X.Modules) :
    rangeHomToRestriction j (𝟙 (M.over j.opensRange)) = 𝟙 (M.restrict j) := by
  ext V m
  rfl

/-- An actual restriction isomorphism gives an actual isomorphism on its original open range. -/
def rangeIsoOfRestriction {M N : X.Modules} (e : M.restrict j ≅ N.restrict j) :
    M.over j.opensRange ≅ N.over j.opensRange where
  hom := restrictionHomToRange j e.hom
  inv := restrictionHomToRange j e.inv
  hom_inv_id := by
    apply (rangeRestrictionHomEquiv j M M).symm.injective
    change rangeHomToRestriction j (_ ≫ _) = rangeHomToRestriction j (𝟙 _)
    rw [rangeHomToRestriction_comp, rangeHomToRestriction_toRange,
      rangeHomToRestriction_toRange, rangeHomToRestriction_id, e.hom_inv_id]
  inv_hom_id := by
    apply (rangeRestrictionHomEquiv j N N).symm.injective
    change rangeHomToRestriction j (_ ≫ _) = rangeHomToRestriction j (𝟙 _)
    rw [rangeHomToRestriction_comp, rangeHomToRestriction_toRange,
      rangeHomToRestriction_toRange, rangeHomToRestriction_id, e.inv_hom_id]

/-- The original restricted forward morphism is recovered exactly. -/
theorem rangeIsoOfRestriction_hom {M N : X.Modules} (e : M.restrict j ≅ N.restrict j) :
    rangeHomToRestriction j (rangeIsoOfRestriction j e).hom = e.hom :=
  rangeHomToRestriction_toRange j e.hom

/-- The original restricted inverse morphism is recovered exactly. -/
theorem rangeIsoOfRestriction_inv {M N : X.Modules} (e : M.restrict j ≅ N.restrict j) :
    rangeHomToRestriction j (rangeIsoOfRestriction j e).inv = e.inv :=
  rangeHomToRestriction_toRange j e.inv

/-- The actual inverse chart frame transported to ordinary open restriction. -/
def chartCoefficientIso (M : X.Modules)
    (e : SheafOfModules.unit W.ringCatSheaf ≅ (Scheme.Modules.pullback j).obj M) :
    M.restrict j ≅ Scheme.Modules.restrict
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) j :=
  (restrictFunctorIsoPullback j).app M ≪≫ e.symm ≪≫ (restrictUnitIso j).symm

/-- The original chart coefficient frame, on its actual open range. -/
def sectionwiseRangeFrame (M : X.Modules)
    (e : SheafOfModules.unit W.ringCatSheaf ≅ (Scheme.Modules.pullback j).obj M) :
    M.over j.opensRange ≅ SheafOfModules.unit (X.ringCatSheaf.over j.opensRange) :=
  rangeIsoOfRestriction j (M := M)
    (N := (show X.Modules from SheafOfModules.unit X.ringCatSheaf))
    (chartCoefficientIso j M e)

/-- Every original image-open component is the actual inverse-chart coefficient map. -/
theorem sectionwiseRangeFrame_coefficient (M : X.Modules)
    (e : SheafOfModules.unit W.ringCatSheaf ≅ (Scheme.Modules.pullback j).obj M)
    (V : W.Opens) (m : Γ(M, j ''ᵁ V)) :
    (sectionwiseRangeFrame j M e).hom.val.app
        (Opposite.op (Over.mk (homOfLE (j.image_le_opensRange V)))) m =
      (chartCoefficientIso j M e).hom.val.app (Opposite.op V) m := by
  exact congrArg (fun f : M.restrict j ⟶ Scheme.Modules.restrict
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) j =>
        f.val.app (Opposite.op V) m)
    (rangeIsoOfRestriction_hom j (chartCoefficientIso j M e))

/-- The original image-open generator is recovered by the actual forward chart frame. -/
theorem sectionwiseRangeFrame_generator (M : X.Modules)
    (e : SheafOfModules.unit W.ringCatSheaf ≅ (Scheme.Modules.pullback j).obj M)
    (V : W.Opens) (s : Γ(X, j ''ᵁ V)) :
    (sectionwiseRangeFrame j M e).inv.val.app
        (Opposite.op (Over.mk (homOfLE (j.image_le_opensRange V)))) s =
      (chartCoefficientIso j M e).inv.val.app (Opposite.op V) s := by
  exact congrArg (fun f : Scheme.Modules.restrict
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) j ⟶ M.restrict j =>
        f.val.app (Opposite.op V) s)
    (rangeIsoOfRestriction_inv j (chartCoefficientIso j M e))

end AlgebraicGeometry.Scheme.Blowup.RegularPoint

namespace AlgebraicGeometry.Scheme.Blowup.RegularPoint

open CategoryTheory AlgebraicGeometry Scheme.Modules

private theorem restrictionComparison_inv_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (M : Y.Modules) :
    (pullbackPushforwardAdjunction f).unit.app M ≫
        (Scheme.Modules.pushforward f).map ((restrictFunctorIsoPullback f).inv.app M) =
      (restrictAdjunction f).unit.app M := by
  rw [← Adjunction.unit_leftAdjointUniq_hom_app (restrictAdjunction f)
    (pullbackPushforwardAdjunction f) M]
  simp only [restrictFunctorIsoPullback, Category.assoc, ← CategoryTheory.Functor.map_comp,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  exact Category.comp_id _

/-- The explicit native restriction-composition map preserves the original composite unit. -/
theorem restrictionComp_unit {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] (M : Z.Modules) :
    (restrictAdjunction (f ≫ g)).unit.app M ≫
        (Scheme.Modules.pushforward (f ≫ g)).map ((restrictFunctorComp f g).hom.app M) =
      (restrictAdjunction g).unit.app M ≫
        (Scheme.Modules.pushforward g).map
          ((restrictAdjunction f).unit.app ((Scheme.Modules.restrictFunctor g).obj M)) ≫
        (pushforwardComp f g).hom.app
          ((Scheme.Modules.restrictFunctor f).obj ((Scheme.Modules.restrictFunctor g).obj M)) := by
  apply Scheme.Modules.hom_ext
  intro U
  simp only [Scheme.Modules.Hom.comp_app, pushforward_map_app,
    restrictAdjunction_unit_app_app, restrictFunctorComp_hom_app_app,
    pushforwardComp_hom_app_app, restrict_map]
  erw [Category.comp_id]
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  congr 1

/-- The original restriction/pullback comparison respects native composition of two
open chart maps. The inverse orientation is convenient for original frame coefficients. -/
theorem restrictionComparison_comp_inv {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] (M : Z.Modules) :
    (pullbackComp f g).inv.app M ≫
        (Scheme.Modules.pullback f).map ((restrictFunctorIsoPullback g).inv.app M) ≫
        (restrictFunctorIsoPullback f).inv.app ((Scheme.Modules.restrictFunctor g).obj M) =
      (restrictFunctorIsoPullback (f ≫ g)).inv.app M ≫
        (restrictFunctorComp f g).hom.app M := by
  apply ((pullbackPushforwardAdjunction (f ≫ g)).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_comp]
  have hp := unit_conjugateEquiv
    ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f))
    (pullbackPushforwardAdjunction (f ≫ g)) (pullbackComp f g).inv M
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv, Adjunction.comp_unit_app] at hp
  have hp' := hp.symm.trans (Category.assoc _ _ _)
  rw [reassoc_of% hp', reassoc_of% restrictionComparison_inv_unit]
  have hn₀ := (pushforwardComp f g).hom.naturality
    ((Scheme.Modules.pullback f).map ((restrictFunctorIsoPullback g).inv.app M))
  have hn₁ := (pushforwardComp f g).hom.naturality
    ((restrictFunctorIsoPullback f).inv.app ((Scheme.Modules.restrictFunctor g).obj M))
  simp only [CategoryTheory.Functor.comp_map] at hn₀ hn₁
  rw [← reassoc_of% hn₀, ← hn₁]
  rw [← CategoryTheory.Functor.map_comp_assoc]
  have hn := (pullbackPushforwardAdjunction f).unit.naturality
    ((restrictFunctorIsoPullback g).inv.app M)
  simp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.id_map] at hn
  rw [← hn]
  rw [CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% restrictionComparison_inv_unit,
    ← CategoryTheory.Functor.map_comp_assoc, restrictionComparison_inv_unit]
  exact (restrictionComp_unit f g M).symm

/-- The native restriction/pullback comparison retains the original structure-module map. -/
theorem restrictionComparison_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] :
    (restrictFunctorIsoPullback f).hom.app (SheafOfModules.unit Y.ringCatSheaf) ≫
        (pullbackUnitIso f).hom = (restrictUnitIso f).hom :=
  Scheme.Modules.restrictFunctorIsoPullback_hom_unit f

/-- The native unit restriction isomorphism retains the original composite chart map. -/
private theorem restrictUnitIso_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] :
    (restrictFunctorComp f g).hom.app (SheafOfModules.unit Z.ringCatSheaf) ≫
        (Scheme.Modules.restrictFunctor f).map (restrictUnitIso g).hom ≫
        (restrictUnitIso f).hom = (restrictUnitIso (f ≫ g)).hom := by
  apply Scheme.Modules.hom_ext
  intro V
  ext x
  change Γ(Z, (f ≫ g) ''ᵁ V) at x
  have h := congrArg (fun e => e.hom x) (Scheme.Hom.comp_appIso f g V)
  exact h.symm

end AlgebraicGeometry.Scheme.Blowup.RegularPoint

namespace AlgebraicGeometry.Scheme.Blowup.RegularPoint

open CategoryTheory AlgebraicGeometry Scheme.Modules
open Scheme.Blowup.IdealFrames

/-- The original restriction/pullback comparison keeps the forward composition square. -/
theorem restrictionComparison_comp_hom {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] (M : Z.Modules) :
    (restrictFunctorComp f g).hom.app M ≫
        (Scheme.Modules.restrictFunctor f).map ((restrictFunctorIsoPullback g).hom.app M) ≫
        (restrictFunctorIsoPullback f).hom.app ((Scheme.Modules.pullback g).obj M) =
      (restrictFunctorIsoPullback (f ≫ g)).hom.app M ≫ (pullbackComp f g).inv.app M := by
  have h :
      (restrictFunctorIsoPullback f).app ((Scheme.Modules.restrictFunctor g).obj M) ≪≫
          (Scheme.Modules.pullback f).mapIso ((restrictFunctorIsoPullback g).app M) ≪≫
          (pullbackComp f g).app M =
        ((restrictFunctorComp f g).app M).symm ≪≫
          (restrictFunctorIsoPullback (f ≫ g)).app M := by
    apply Iso.ext_inv
    exact restrictionComparison_comp_inv f g M
  have hn := (restrictFunctorIsoPullback f).hom.naturality
    ((restrictFunctorIsoPullback g).hom.app M)
  have hh := congrArg Iso.hom h
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    CategoryTheory.Functor.mapIso_hom] at hh
  rw [hn]
  apply (cancel_mono ((pullbackComp f g).hom.app M)).mp
  simp only [Category.assoc]
  rw [hh]
  simp only [Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app, Category.comp_id]

/-- Further actual open restriction of the chart coefficient is the coefficient of the
original normalized pulled frame, including both native composition comparisons. -/
theorem chartCoefficientIso_comp {W P X : Scheme.{u}} (p : W ⟶ P) (j : P ⟶ X)
    [IsOpenImmersion p] [IsOpenImmersion j] (M : X.Modules)
    (e : SheafOfModules.unit P.ringCatSheaf ≅ (Scheme.Modules.pullback j).obj M) :
    (restrictFunctorComp p j).app M ≪≫
        (Scheme.Modules.restrictFunctor p).mapIso (chartCoefficientIso j M e) ≪≫
        ((restrictFunctorComp p j).app (SheafOfModules.unit X.ringCatSheaf)).symm =
      chartCoefficientIso (p ≫ j) M (frameAlong p j M e) := by
  have hu : (restrictFunctorComp p j).inv.app (SheafOfModules.unit X.ringCatSheaf) ≫
      (restrictUnitIso (p ≫ j)).hom =
        (Scheme.Modules.restrictFunctor p).map (restrictUnitIso j).hom ≫
          (restrictUnitIso p).hom := by
    apply (cancel_epi ((restrictFunctorComp p j).hom.app
      (SheafOfModules.unit X.ringCatSheaf))).mp
    simpa only [Iso.hom_inv_id_app_assoc, Category.assoc] using
      (restrictUnitIso_comp p j).symm
  have hn := (restrictFunctorIsoPullback p).hom.naturality e.inv
  apply Iso.ext
  apply (cancel_mono (restrictUnitIso (p ≫ j)).hom).mp
  simp only [chartCoefficientIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    CategoryTheory.Functor.mapIso_hom, CategoryTheory.Functor.map_comp,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hu, ← CategoryTheory.Functor.map_comp_assoc (Scheme.Modules.restrictFunctor p)
    (restrictUnitIso j).inv (restrictUnitIso j).hom, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← restrictionComparison_unit p, reassoc_of% hn,
    reassoc_of% restrictionComparison_comp_hom p j M]
  rfl

end AlgebraicGeometry.Scheme.Blowup.RegularPoint

namespace AlgebraicGeometry.Scheme.Blowup.RegularPoint

open CategoryTheory Opposite AlgebraicGeometry Scheme.Modules
open Scheme.Modules.Invertible Scheme.Modules.InternalHom Scheme.Blowup.IdealFrames

private theorem sectionHomEquiv_restrict_component {X : Scheme.{u}}
    (M N : X.Modules) {U V W : X.Opens} (h : V ≤ U) (hW : W ≤ V)
    (a : Γ(sheaf X M N, U)) (m : Γ(M, W)) :
    (sectionHomEquiv X M N V ((sheaf X M N).val.map (homOfLE h).op a)).val.app
        (op (Over.mk (homOfLE hW))) m =
      (sectionHomEquiv X M N U a).val.app
        (op (Over.mk (homOfLE (hW.trans h)))) m := rfl

private theorem sectionHomEquiv_restrictionHom {W X : Scheme.{u}}
    (j : W ⟶ X) [IsOpenImmersion j] (M N : X.Modules)
    (a : M.restrict j ⟶ N.restrict j) :
    sectionHomEquiv X M N j.opensRange (restrictionHomEquiv j M N a) =
      restrictionHomToRange j a :=
  (sectionHomEquiv X M N j.opensRange).apply_symm_apply _

/-- The original range coefficient on a further chart range is exactly the coefficient of
its normalized composite frame. -/
theorem sectionwiseRangeFrame_coefficient_comp {W P X : Scheme.{u}}
    (p : W ⟶ P) (j : P ⟶ X) [IsOpenImmersion p] [IsOpenImmersion j]
    (M : X.Modules)
    (e : SheafOfModules.unit P.ringCatSheaf ≅ (Scheme.Modules.pullback j).obj M)
    (V : X.Opens) (hV : V ≤ (p ≫ j).opensRange) (m : Γ(M, V)) :
    (sectionwiseRangeFrame j M e).hom.val.app
        (op (Over.mk (homOfLE (hV.trans (restrictionRange_le j p))))) m =
      (sectionwiseRangeFrame (p ≫ j) M (frameAlong p j M e)).hom.val.app
        (op (Over.mk (homOfLE hV))) m := by
  have H := restrictionHomEquiv_restrict j p M (SheafOfModules.unit X.ringCatSheaf)
    (chartCoefficientIso j M e).hom
  have hc : restrictionHomMap j p (chartCoefficientIso j M e).hom =
      (chartCoefficientIso (p ≫ j) M (frameAlong p j M e)).hom := by
    simpa only [restrictionHomMap, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
      Iso.app_inv, CategoryTheory.Functor.mapIso_hom] using
      congrArg Iso.hom (chartCoefficientIso_comp p j M e)
  rw [hc] at H
  have H' := congrArg
    (fun a : Γ(sheaf X M (SheafOfModules.unit X.ringCatSheaf), (p ≫ j).opensRange) =>
      (sectionHomEquiv X M (SheafOfModules.unit X.ringCatSheaf)
        (p ≫ j).opensRange a).val.app (op (Over.mk (homOfLE hV))) m) H
  rw [sectionHomEquiv_restrict_component, sectionHomEquiv_restrictionHom,
    sectionHomEquiv_restrictionHom] at H'
  exact H'

/-- The inverse coefficient also retains the original generator under further open restriction. -/
theorem sectionwiseRangeFrame_generator_comp {W P X : Scheme.{u}}
    (p : W ⟶ P) (j : P ⟶ X) [IsOpenImmersion p] [IsOpenImmersion j]
    (M : X.Modules)
    (e : SheafOfModules.unit P.ringCatSheaf ≅ (Scheme.Modules.pullback j).obj M)
    (V : X.Opens) (hV : V ≤ (p ≫ j).opensRange) :
    (sectionwiseRangeFrame j M e).inv.val.app
        (op (Over.mk (homOfLE (hV.trans (restrictionRange_le j p))))) (1 : Γ(X, V)) =
      (sectionwiseRangeFrame (p ≫ j) M (frameAlong p j M e)).inv.val.app
        (op (Over.mk (homOfLE hV))) (1 : Γ(X, V)) := by
  let c₀ := chartSectionEquiv X M j.opensRange (sectionwiseRangeFrame j M e)
    V (hV.trans (restrictionRange_le j p))
  let c₁ := chartSectionEquiv X M (p ≫ j).opensRange
    (sectionwiseRangeFrame (p ≫ j) M (frameAlong p j M e)) V hV
  apply c₀.injective
  change c₀ (c₀.symm 1) = c₀ (c₁.symm 1)
  rw [c₀.apply_symm_apply]
  exact (sectionwiseRangeFrame_coefficient_comp p j M e V hV (c₁.symm 1)).trans
    (c₁.apply_symm_apply 1) |>.symm

/-- The range coefficient evaluated through the original chart ring map is the actual
inverse frame component. -/
theorem sectionwiseRangeFrame_coefficient_appIso {W X : Scheme.{u}}
    (j : W ⟶ X) [IsOpenImmersion j] (M : X.Modules)
    (e : SheafOfModules.unit W.ringCatSheaf ≅ (Scheme.Modules.pullback j).obj M)
    (V : W.Opens) (m : Γ(M, j ''ᵁ V)) :
    (j.appIso V).hom
      ((sectionwiseRangeFrame j M e).hom.val.app
        (op (Over.mk (homOfLE (j.image_le_opensRange V)))) m) =
      (Scheme.Modules.Hom.app (X := W) e.inv V)
        (((restrictFunctorIsoPullback j).hom.app M).app V m) := by
  rw [sectionwiseRangeFrame_coefficient]
  change (j.appIso V).hom ((j.appIso V).inv
    ((Scheme.Modules.Hom.app (X := W) e.inv V)
      (((restrictFunctorIsoPullback j).hom.app M).app V m))) = _
  exact Iso.inv_hom_id_apply (j.appIso V) _

/-- The actual forward chart comparison sends the range generator to the original frame. -/
theorem sectionwiseRangeFrame_generator_component {W X : Scheme.{u}}
    (j : W ⟶ X) [IsOpenImmersion j] (M : X.Modules)
    (e : SheafOfModules.unit W.ringCatSheaf ≅ (Scheme.Modules.pullback j).obj M)
    (V : W.Opens) :
    ((restrictFunctorIsoPullback j).hom.app M).app V
      ((sectionwiseRangeFrame j M e).inv.val.app
        (op (Over.mk (homOfLE (j.image_le_opensRange V)))) (1 : Γ(X, j ''ᵁ V))) =
      (Scheme.Modules.Hom.app (X := W) e.hom V) (1 : Γ(W, V)) := by
  rw [sectionwiseRangeFrame_generator]
  change ((restrictFunctorIsoPullback j).hom.app M).app V
    (((restrictFunctorIsoPullback j).inv.app M).app V
      ((Scheme.Modules.Hom.app (X := W) e.hom V)
        ((j.appIso V).hom (1 : Γ(X, j ''ᵁ V))))) = _
  rw [map_one]
  exact Iso.inv_hom_id_apply
    (((Scheme.Modules.toPresheaf W).mapIso ((restrictFunctorIsoPullback j).app M)).app (op V)) _

/-- On a common actual open chart the original coefficient of the second generator is
exactly the value of the original change-of-frame morphism on one. -/
theorem sectionwiseRangeFrame_transition_value {W X : Scheme.{u}}
    (j : W ⟶ X) [IsOpenImmersion j] (M : X.Modules)
    (e₀ e₁ : SheafOfModules.unit W.ringCatSheaf ≅ (Scheme.Modules.pullback j).obj M)
    (s : (show W.Modules from SheafOfModules.unit W.ringCatSheaf) ⟶
      SheafOfModules.unit W.ringCatSheaf) (h : e₁.hom = s ≫ e₀.hom) :
    (j.appIso ⊤).hom
      ((sectionwiseRangeFrame j M e₀).hom.val.app
        (op (Over.mk (homOfLE (j.image_le_opensRange ⊤))))
          ((sectionwiseRangeFrame j M e₁).inv.val.app
            (op (Over.mk (homOfLE (j.image_le_opensRange ⊤)))) (1 : Γ(X, j ''ᵁ ⊤)))) =
      s.app ⊤ (1 : Γ(W, ⊤)) := by
  rw [sectionwiseRangeFrame_coefficient_appIso, sectionwiseRangeFrame_generator_component]
  rw [h, Scheme.Modules.Hom.comp_app]
  exact Iso.hom_inv_id_apply (((Scheme.Modules.toPresheaf W).mapIso e₀).app (op ⊤)) _

end AlgebraicGeometry.Scheme.Blowup.RegularPoint

namespace AlgebraicGeometry.Scheme.Blowup.RegularPoint

open CategoryTheory Opposite AlgebraicGeometry Scheme.Modules
open Scheme.Modules.Invertible Scheme.Modules.InternalHom Scheme.Blowup.IdealFrames

/-- Equal actual chart arrows retain the same original coefficient on every common subopen. -/
theorem sectionwiseRangeFrame_coefficient_congr {W X : Scheme.{u}}
    {j k : W ⟶ X} [IsOpenImmersion j] [IsOpenImmersion k] (h : j = k)
    (M : X.Modules)
    (e : SheafOfModules.unit W.ringCatSheaf ≅ (Scheme.Modules.pullback j).obj M)
    (V : X.Opens) (hj : V ≤ j.opensRange) (hk : V ≤ k.opensRange) (m : Γ(M, V)) :
    (sectionwiseRangeFrame j M e).hom.val.app (op (Over.mk (homOfLE hj))) m =
      (sectionwiseRangeFrame k M (e ≪≫ (pullbackCongr h).app M)).hom.val.app
        (op (Over.mk (homOfLE hk))) m := by
  subst k
  have he : e ≪≫ (pullbackCongr (rfl : j = j)).app M = e := by
    apply Iso.ext
    simp [pullbackCongr]
  rw [he]

/-- Equal actual chart arrows retain the same original generator on every common subopen. -/
theorem sectionwiseRangeFrame_generator_congr {W X : Scheme.{u}}
    {j k : W ⟶ X} [IsOpenImmersion j] [IsOpenImmersion k] (h : j = k)
    (M : X.Modules)
    (e : SheafOfModules.unit W.ringCatSheaf ≅ (Scheme.Modules.pullback j).obj M)
    (V : X.Opens) (hj : V ≤ j.opensRange) (hk : V ≤ k.opensRange) :
    (sectionwiseRangeFrame j M e).inv.val.app (op (Over.mk (homOfLE hj))) (1 : Γ(X, V)) =
      (sectionwiseRangeFrame k M (e ≪≫ (pullbackCongr h).app M)).inv.val.app
        (op (Over.mk (homOfLE hk))) (1 : Γ(X, V)) := by
  subst k
  have he : e ≪≫ (pullbackCongr (rfl : j = j)).app M = e := by
    apply Iso.ext
    simp [pullbackCongr]
  rw [he]

/-- The original transition coefficient is detected on an actual common open chart by
its original frame equation. No normal bundle or comparison family is supplied. -/
theorem originalFrameTransition_value {W P₀ P₁ X : Scheme.{u}}
    (p₀ : W ⟶ P₀) (p₁ : W ⟶ P₁) (j₀ : P₀ ⟶ X) (j₁ : P₁ ⟶ X)
    [IsOpenImmersion p₀] [IsOpenImmersion p₁]
    [IsOpenImmersion j₀] [IsOpenImmersion j₁]
    (h : p₀ ≫ j₀ = p₁ ≫ j₁) (M : X.Modules)
    (e₀ : SheafOfModules.unit P₀.ringCatSheaf ≅ (Scheme.Modules.pullback j₀).obj M)
    (e₁ : SheafOfModules.unit P₁.ringCatSheaf ≅ (Scheme.Modules.pullback j₁).obj M)
    (s : (show W.Modules from SheafOfModules.unit W.ringCatSheaf) ⟶
      SheafOfModules.unit W.ringCatSheaf)
    (hs : (frameAlong p₁ j₁ M e₁).hom ≫ (pullbackCongr h.symm).hom.app M =
      s ≫ (frameAlong p₀ j₀ M e₀).hom)
    (V : X.Opens) (hV : V = (p₀ ≫ j₀) ''ᵁ ⊤)
    (h₀ : V ≤ j₀.opensRange) (h₁ : V ≤ j₁.opensRange)
    (hv : (⊤ : W.Opens) ≤ (p₀ ≫ j₀) ⁻¹ᵁ V) :
    (p₀ ≫ j₀).appLE V ⊤ hv
      ((sectionwiseRangeFrame j₀ M e₀).hom.val.app (op (Over.mk (homOfLE h₀)))
        ((sectionwiseRangeFrame j₁ M e₁).inv.val.app (op (Over.mk (homOfLE h₁))) (1 : Γ(X, V)))) =
      s.app ⊤ (1 : Γ(W, ⊤)) := by
  subst V
  have hv₀ := (p₀ ≫ j₀).image_le_opensRange ⊤
  have hv₁ : (p₀ ≫ j₀) ''ᵁ ⊤ ≤ (p₁ ≫ j₁).opensRange := by
    simpa only [h] using hv₀
  rw [← Scheme.Hom.appIso_hom']
  rw [sectionwiseRangeFrame_generator_comp p₁ j₁ M e₁ _ hv₁]
  rw [sectionwiseRangeFrame_coefficient_comp p₀ j₀ M e₀ _ hv₀]
  rw [sectionwiseRangeFrame_generator_congr h.symm M (frameAlong p₁ j₁ M e₁) _ hv₁ hv₀]
  have ht : (frameAlong p₁ j₁ M e₁ ≪≫ (pullbackCongr h.symm).app M).hom =
      s ≫ (frameAlong p₀ j₀ M e₀).hom := by
    rw [Iso.trans_hom, Iso.app_hom]
    exact hs
  rw [sectionwiseRangeFrame_coefficient_appIso, sectionwiseRangeFrame_generator_component]
  rw [ht, Scheme.Modules.Hom.comp_app]
  exact Iso.hom_inv_id_apply
    (((Scheme.Modules.toPresheaf W).mapIso (frameAlong p₀ j₀ M e₀)).app (op ⊤)) _

/-- An original affine scalar frame relation evaluates through the actual Spec section map.
The conversion is proved before the coefficient ring or target scheme is specialized. -/
theorem originalFrameTransition_affineValue {S : Type u} [CommRing S]
    {P₀ P₁ X : Scheme.{u}} (p₀ : Spec (.of S) ⟶ P₀) (p₁ : Spec (.of S) ⟶ P₁)
    (j₀ : P₀ ⟶ X) (j₁ : P₁ ⟶ X)
    [IsOpenImmersion p₀] [IsOpenImmersion p₁]
    [IsOpenImmersion j₀] [IsOpenImmersion j₁]
    (h : p₀ ≫ j₀ = p₁ ≫ j₁) (M : X.Modules)
    (e₀ : SheafOfModules.unit P₀.ringCatSheaf ≅ (Scheme.Modules.pullback j₀).obj M)
    (e₁ : SheafOfModules.unit P₁.ringCatSheaf ≅ (Scheme.Modules.pullback j₁).obj M) (r : S)
    (hs : (frameAlong p₁ j₁ M e₁).hom ≫ (pullbackCongr h.symm).hom.app M =
      affineMultiplication S r ≫ (frameAlong p₀ j₀ M e₀).hom)
    (V : X.Opens) (hV : V = (p₀ ≫ j₀) ''ᵁ ⊤)
    (h₀ : V ≤ j₀.opensRange) (h₁ : V ≤ j₁.opensRange)
    (hv : (⊤ : (Spec (.of S)).Opens) ≤ (p₀ ≫ j₀) ⁻¹ᵁ V) :
    ((p₀ ≫ j₀).appLE V ⊤ hv).hom
      ((sectionwiseRangeFrame j₀ M e₀).hom.val.app (op (Over.mk (homOfLE h₀)))
        ((sectionwiseRangeFrame j₁ M e₁).inv.val.app
          (op (Over.mk (homOfLE h₁))) (1 : Γ(X, V)))) =
      (Scheme.ΓSpecIso (.of S)).inv.hom r := by
  have H := originalFrameTransition_value p₀ p₁ j₀ j₁ h M e₀ e₁
    (affineMultiplication S r) hs V hV h₀ h₁ hv
  refine H.trans ?_
  rw [affineMultiplication_eq_unitMul, unitMul_app]
  simp

private theorem chartSectionEquiv_apply_native {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens) (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (V : X.Opens) (hV : V ≤ U) (m : Γ(M, V)) :
    chartSectionEquiv X M U e V hV m =
      e.hom.val.app (op (Over.mk (homOfLE hV))) m := rfl

private theorem chartSectionEquiv_symm_apply_native {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens) (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (V : X.Opens) (hV : V ≤ U) (r : Γ(X, V)) :
    (chartSectionEquiv X M U e V hV).symm r =
      e.inv.val.app (op (Over.mk (homOfLE hV))) r := rfl

/-- The original coefficient is stored with its literal chart-section formula.
The checked opaque body keeps evaluation-functor implementations out of concrete conversion. -/
opaque rangeFrameCoefficientData {X : Scheme.{u}} (M : X.Modules) (U₀ U₁ : X.Opens)
    (e₀ : M.over U₀ ≅ SheafOfModules.unit (X.ringCatSheaf.over U₀))
    (e₁ : M.over U₁ ≅ SheafOfModules.unit (X.ringCatSheaf.over U₁))
    (V : X.Opens) (h₀ : V ≤ U₀) (h₁ : V ≤ U₁) :
    { c : Γ(X, V) // c = (chartSectionEquiv X M U₀ e₀ V h₀)
      ((chartSectionEquiv X M U₁ e₁ V h₁).symm 1) } :=
  ⟨(chartSectionEquiv X M U₀ e₀ V h₀)
    ((chartSectionEquiv X M U₁ e₁ V h₁).symm 1), rfl⟩

/-- The scalar is projected while the original scheme and frames remain symbolic. -/
def rangeFrameCoefficient {X : Scheme.{u}} (M : X.Modules) (U₀ U₁ : X.Opens)
    (e₀ : M.over U₀ ≅ SheafOfModules.unit (X.ringCatSheaf.over U₀))
    (e₁ : M.over U₁ ≅ SheafOfModules.unit (X.ringCatSheaf.over U₁))
    (V : X.Opens) (h₀ : V ≤ U₀) (h₁ : V ≤ U₁) : Γ(X, V) :=
  (rangeFrameCoefficientData M U₀ U₁ e₀ e₁ V h₀ h₁).val

/-- The projected value is exactly the original coefficient of the second frame generator. -/
theorem rangeFrameCoefficient_eq {X : Scheme.{u}} (M : X.Modules) (U₀ U₁ : X.Opens)
    (e₀ : M.over U₀ ≅ SheafOfModules.unit (X.ringCatSheaf.over U₀))
    (e₁ : M.over U₁ ≅ SheafOfModules.unit (X.ringCatSheaf.over U₁))
    (V : X.Opens) (h₀ : V ≤ U₀) (h₁ : V ≤ U₁) :
    rangeFrameCoefficient M U₀ U₁ e₀ e₁ V h₀ h₁ =
      (chartSectionEquiv X M U₀ e₀ V h₀)
        ((chartSectionEquiv X M U₁ e₁ V h₁).symm 1) :=
  (rangeFrameCoefficientData M U₀ U₁ e₀ e₁ V h₀ h₁).property

/-- The original chart-section equivalences give the same affine scalar coefficient.
Their evaluation-functor components are normalized at symbolic schemes before specialization. -/
theorem originalFrameTransition_affineCoefficient {S : Type u} [CommRing S]
    {P₀ P₁ X : Scheme.{u}} (p₀ : Spec (.of S) ⟶ P₀) (p₁ : Spec (.of S) ⟶ P₁)
    (j₀ : P₀ ⟶ X) (j₁ : P₁ ⟶ X)
    [IsOpenImmersion p₀] [IsOpenImmersion p₁]
    [IsOpenImmersion j₀] [IsOpenImmersion j₁]
    (h : p₀ ≫ j₀ = p₁ ≫ j₁) (M : X.Modules)
    (e₀ : SheafOfModules.unit P₀.ringCatSheaf ≅ (Scheme.Modules.pullback j₀).obj M)
    (e₁ : SheafOfModules.unit P₁.ringCatSheaf ≅ (Scheme.Modules.pullback j₁).obj M) (r : S)
    (hs : (frameAlong p₁ j₁ M e₁).hom ≫ (pullbackCongr h.symm).hom.app M =
      affineMultiplication S r ≫ (frameAlong p₀ j₀ M e₀).hom)
    (V : X.Opens) (hV : V = (p₀ ≫ j₀) ''ᵁ ⊤)
    (h₀ : V ≤ j₀.opensRange) (h₁ : V ≤ j₁.opensRange)
    (hv : (⊤ : (Spec (.of S)).Opens) ≤ (p₀ ≫ j₀) ⁻¹ᵁ V) :
    ((p₀ ≫ j₀).appLE V ⊤ hv).hom
      ((chartSectionEquiv X M j₀.opensRange (sectionwiseRangeFrame j₀ M e₀) V h₀)
        ((chartSectionEquiv X M j₁.opensRange
          (sectionwiseRangeFrame j₁ M e₁) V h₁).symm 1)) =
      (Scheme.ΓSpecIso (.of S)).inv.hom r := by
  rw [chartSectionEquiv_apply_native, chartSectionEquiv_symm_apply_native]
  exact originalFrameTransition_affineValue p₀ p₁ j₀ j₁ h M e₀ e₁ r hs V hV h₀ h₁ hv

/-- The same original affine coefficient equation for the projected scalar, retaining the
literal section map and the proved equality to the original frame formula. -/
theorem originalFrameTransition_affineFrameCoefficient {S : Type u} [CommRing S]
    {P₀ P₁ X : Scheme.{u}} (p₀ : Spec (.of S) ⟶ P₀) (p₁ : Spec (.of S) ⟶ P₁)
    (j₀ : P₀ ⟶ X) (j₁ : P₁ ⟶ X)
    [IsOpenImmersion p₀] [IsOpenImmersion p₁]
    [IsOpenImmersion j₀] [IsOpenImmersion j₁]
    (h : p₀ ≫ j₀ = p₁ ≫ j₁) (M : X.Modules)
    (e₀ : SheafOfModules.unit P₀.ringCatSheaf ≅ (Scheme.Modules.pullback j₀).obj M)
    (e₁ : SheafOfModules.unit P₁.ringCatSheaf ≅ (Scheme.Modules.pullback j₁).obj M) (r : S)
    (hs : (frameAlong p₁ j₁ M e₁).hom ≫ (pullbackCongr h.symm).hom.app M =
      affineMultiplication S r ≫ (frameAlong p₀ j₀ M e₀).hom)
    (V : X.Opens) (hV : V = (p₀ ≫ j₀) ''ᵁ ⊤)
    (h₀ : V ≤ j₀.opensRange) (h₁ : V ≤ j₁.opensRange)
    (hv : (⊤ : (Spec (.of S)).Opens) ≤ (p₀ ≫ j₀) ⁻¹ᵁ V) :
    ((p₀ ≫ j₀).appLE V ⊤ hv).hom
      (rangeFrameCoefficient M j₀.opensRange j₁.opensRange
        (sectionwiseRangeFrame j₀ M e₀) (sectionwiseRangeFrame j₁ M e₁) V h₀ h₁) =
      (Scheme.ΓSpecIso (.of S)).inv.hom r := by
  rw [rangeFrameCoefficient_eq]
  exact originalFrameTransition_affineCoefficient p₀ p₁ j₀ j₁ h M e₀ e₁ r hs V hV h₀ h₁ hv

/-- The original overlap coefficient, evaluated in the actual affine coefficient ring. -/
theorem originalFrameTransition_affineCoordinate {S : Type u} [CommRing S]
    {P₀ P₁ X : Scheme.{u}} (p₀ : Spec (.of S) ⟶ P₀) (p₁ : Spec (.of S) ⟶ P₁)
    (j₀ : P₀ ⟶ X) (j₁ : P₁ ⟶ X)
    [IsOpenImmersion p₀] [IsOpenImmersion p₁]
    [IsOpenImmersion j₀] [IsOpenImmersion j₁]
    (h : p₀ ≫ j₀ = p₁ ≫ j₁) (M : X.Modules)
    (e₀ : SheafOfModules.unit P₀.ringCatSheaf ≅ (Scheme.Modules.pullback j₀).obj M)
    (e₁ : SheafOfModules.unit P₁.ringCatSheaf ≅ (Scheme.Modules.pullback j₁).obj M) (r : S)
    (hs : (frameAlong p₁ j₁ M e₁).hom ≫ (pullbackCongr h.symm).hom.app M =
      affineMultiplication S r ≫ (frameAlong p₀ j₀ M e₀).hom)
    (V : X.Opens) (hV : V = (p₀ ≫ j₀) ''ᵁ ⊤)
    (h₀ : V ≤ j₀.opensRange) (h₁ : V ≤ j₁.opensRange)
    (hv : (⊤ : (Spec (.of S)).Opens) ≤ (p₀ ≫ j₀) ⁻¹ᵁ V) :
    (Scheme.ΓSpecIso (.of S)).hom.hom
      (((p₀ ≫ j₀).appLE V ⊤ hv).hom
        (rangeFrameCoefficient M j₀.opensRange j₁.opensRange
          (sectionwiseRangeFrame j₀ M e₀) (sectionwiseRangeFrame j₁ M e₁) V h₀ h₁)) = r := by
  have H := originalFrameTransition_affineFrameCoefficient p₀ p₁ j₀ j₁ h M e₀ e₁ r hs
    V hV h₀ h₁ hv
  exact (congrArg (Scheme.ΓSpecIso (.of S)).hom.hom H).trans
    (Iso.inv_hom_id_apply (Scheme.ΓSpecIso (.of S)) r)

/-- A checked presentation of the literal native pullback. The body chooses that very
module and its identity comparison; opacity prevents its implementation from being expanded
when the actual blowup's section functors inspect a module argument. -/
opaque pullbackSectionModuleData {X Y : Scheme.{u}} (f : X ⟶ Y) (L : LineBundle Y) :
    Σ N : X.Modules, N ≅ (pullbackLineBundle f L).val :=
  ⟨(Scheme.Modules.pullback f).obj L.val, Iso.refl _⟩

/-- The displayed native pullback module, projected before concrete specialization. -/
def pullbackSectionModule {X Y : Scheme.{u}} (f : X ⟶ Y) (L : LineBundle Y) : X.Modules :=
  (pullbackSectionModuleData f L).1

/-- Its canonical comparison to the actual pulled line module. -/
def pullbackSectionModuleIso {X Y : Scheme.{u}} (f : X ⟶ Y) (L : LineBundle Y) :
    pullbackSectionModule f L ≅ (pullbackLineBundle f L).val :=
  (pullbackSectionModuleData f L).2

/-- Changing a displayed module through its actual isomorphism commutes with original
frame pullback. All maps are the native pullback and composition-comparison maps. -/
private theorem frameAlong_moduleIso_hom {W P X : Scheme.{u}} (p : W ⟶ P) (j : P ⟶ X)
    {M N : X.Modules} (v : M ≅ N)
    (e : SheafOfModules.unit P.ringCatSheaf ≅ (Scheme.Modules.pullback j).obj M) :
    (frameAlong p j N (e ≪≫ (Scheme.Modules.pullback j).mapIso v)).hom =
      (frameAlong p j M e).hom ≫ (Scheme.Modules.pullback (p ≫ j)).map v.hom := by
  simp only [frameAlong, Iso.trans_hom, Iso.app_hom, pullbackFrame_trans_hom,
    CategoryTheory.Functor.mapIso_hom, Category.assoc]
  have hn := (pullbackComp p j).hom.naturality v.hom
  simp only [CategoryTheory.Functor.comp_map] at hn
  rw [hn]

/-- The literal equal-map transition is preserved by a canonical module comparison. -/
private theorem frameAlong_moduleIso_transition {W P₀ P₁ X : Scheme.{u}}
    (p₀ : W ⟶ P₀) (p₁ : W ⟶ P₁) (j₀ : P₀ ⟶ X) (j₁ : P₁ ⟶ X)
    (h : p₀ ≫ j₀ = p₁ ≫ j₁) {M N : X.Modules} (v : M ≅ N)
    (e₀ : SheafOfModules.unit P₀.ringCatSheaf ≅ (Scheme.Modules.pullback j₀).obj M)
    (e₁ : SheafOfModules.unit P₁.ringCatSheaf ≅ (Scheme.Modules.pullback j₁).obj M)
    (s : SheafOfModules.unit W.ringCatSheaf ⟶ SheafOfModules.unit W.ringCatSheaf)
    (hs : (frameAlong p₁ j₁ M e₁).hom ≫ (pullbackCongr h.symm).hom.app M =
      s ≫ (frameAlong p₀ j₀ M e₀).hom) :
    (frameAlong p₁ j₁ N (e₁ ≪≫ (Scheme.Modules.pullback j₁).mapIso v)).hom ≫
        (pullbackCongr h.symm).hom.app N =
      s ≫ (frameAlong p₀ j₀ N (e₀ ≪≫ (Scheme.Modules.pullback j₀).mapIso v)).hom := by
  rw [frameAlong_moduleIso_hom, frameAlong_moduleIso_hom]
  have hn := (pullbackCongr h.symm).hom.naturality v.hom
  rw [Category.assoc, hn, ← Category.assoc, hs, Category.assoc]

/-- The original range map of an actual module morphism is its ordinary restriction. -/
private theorem rangeHomToRestriction_overMap {W X : Scheme.{u}} (j : W ⟶ X)
    [IsOpenImmersion j] {M N : X.Modules} (f : M ⟶ N) :
    Scheme.Modules.InternalHom.rangeHomToRestriction j
        ((SheafOfModules.overFunctor X.ringCatSheaf j.opensRange).map f) =
      (Scheme.Modules.restrictFunctor j).map f := by
  ext V m
  rfl

/-- The range frame has the original restriction coefficient morphism. -/
private theorem sectionwiseRangeFrame_hom {W X : Scheme.{u}} (j : W ⟶ X)
    [IsOpenImmersion j] (M : X.Modules)
    (e : SheafOfModules.unit W.ringCatSheaf ≅ (Scheme.Modules.pullback j).obj M) :
    Scheme.Modules.InternalHom.rangeHomToRestriction j (sectionwiseRangeFrame j M e).hom =
      (chartCoefficientIso j M e).hom :=
  rangeIsoOfRestriction_hom j (chartCoefficientIso j M e)

/-- A transported chart frame retains the original range coefficient isomorphism. -/
private theorem sectionwiseRangeFrame_moduleIso {W X : Scheme.{u}} (j : W ⟶ X)
    [IsOpenImmersion j] {M N : X.Modules} (v : M ≅ N)
    (e : SheafOfModules.unit W.ringCatSheaf ≅ (Scheme.Modules.pullback j).obj M) :
    sectionwiseRangeFrame j N (e ≪≫ (Scheme.Modules.pullback j).mapIso v) =
      ((SheafOfModules.overFunctor X.ringCatSheaf j.opensRange).mapIso v).symm ≪≫
        sectionwiseRangeFrame j M e := by
  apply Iso.ext
  apply (Scheme.Modules.InternalHom.rangeRestrictionHomEquiv j N
    (show X.Modules from SheafOfModules.unit X.ringCatSheaf)).symm.injective
  change Scheme.Modules.InternalHom.rangeHomToRestriction j _ =
    Scheme.Modules.InternalHom.rangeHomToRestriction j _
  erw [sectionwiseRangeFrame_hom j N (e ≪≫ (Scheme.Modules.pullback j).mapIso v)]
  simp only [Iso.trans_hom, Iso.symm_hom, CategoryTheory.Functor.mapIso_inv,
    rangeHomToRestriction_comp, sectionwiseRangeFrame_hom, rangeHomToRestriction_overMap]
  have hn := (restrictFunctorIsoPullback j).hom.naturality v.inv
  simpa only [chartCoefficientIso, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
    CategoryTheory.Functor.mapIso_inv, Iso.app_hom, Category.assoc] using
    (congrArg (fun q => q ≫ e.inv ≫ (restrictUnitIso j).inv) hn).symm

/-- The original coefficient of one range generator in another is invariant under an
actual common module isomorphism, with the original component maps retained. -/
private theorem rangeFrameCoefficient_moduleIso {X : Scheme.{u}} {M N : X.Modules}
    (v : M ≅ N) (U₀ U₁ : X.Opens)
    (e₀ : M.over U₀ ≅ SheafOfModules.unit (X.ringCatSheaf.over U₀))
    (e₁ : M.over U₁ ≅ SheafOfModules.unit (X.ringCatSheaf.over U₁))
    (V : X.Opens) (h₀ : V ≤ U₀) (h₁ : V ≤ U₁) :
    rangeFrameCoefficient N U₀ U₁
        (((SheafOfModules.overFunctor X.ringCatSheaf U₀).mapIso v).symm ≪≫ e₀)
        (((SheafOfModules.overFunctor X.ringCatSheaf U₁).mapIso v).symm ≪≫ e₁) V h₀ h₁ =
      rangeFrameCoefficient M U₀ U₁ e₀ e₁ V h₀ h₁ := by
  rw [rangeFrameCoefficient_eq, rangeFrameCoefficient_eq]
  rw [chartSectionEquiv_apply_native, chartSectionEquiv_symm_apply_native,
    chartSectionEquiv_apply_native, chartSectionEquiv_symm_apply_native]
  change e₀.hom.val.app (op (Over.mk (homOfLE h₀)))
      (v.inv.val.app (op V) (v.hom.val.app (op V)
        (e₁.inv.val.app (op (Over.mk (homOfLE h₁))) (1 : Γ(X, V))))) =
    e₀.hom.val.app (op (Over.mk (homOfLE h₀)))
      (e₁.inv.val.app (op (Over.mk (homOfLE h₁))) (1 : Γ(X, V)))
  have hc := congrArg (fun f : M ⟶ M => f.val.app (op V)
    (e₁.inv.val.app (op (Over.mk (homOfLE h₁))) (1 : Γ(X, V)))) v.hom_inv_id
  exact congrArg (e₀.hom.val.app (op (Over.mk (homOfLE h₀)))) hc

/-- The original two chart coefficients are unchanged by a common canonical module
transport. This equation, rather than definitional identification of modules, is used below. -/
theorem rangeFrameCoefficient_chartModuleIso {P₀ P₁ X : Scheme.{u}}
    (j₀ : P₀ ⟶ X) (j₁ : P₁ ⟶ X) [IsOpenImmersion j₀] [IsOpenImmersion j₁]
    {M N : X.Modules} (v : M ≅ N)
    (e₀ : SheafOfModules.unit P₀.ringCatSheaf ≅ (Scheme.Modules.pullback j₀).obj M)
    (e₁ : SheafOfModules.unit P₁.ringCatSheaf ≅ (Scheme.Modules.pullback j₁).obj M)
    (V : X.Opens) (h₀ : V ≤ j₀.opensRange) (h₁ : V ≤ j₁.opensRange) :
    rangeFrameCoefficient N j₀.opensRange j₁.opensRange
        (sectionwiseRangeFrame j₀ N (e₀ ≪≫ (Scheme.Modules.pullback j₀).mapIso v))
        (sectionwiseRangeFrame j₁ N (e₁ ≪≫ (Scheme.Modules.pullback j₁).mapIso v)) V h₀ h₁ =
      rangeFrameCoefficient M j₀.opensRange j₁.opensRange
        (sectionwiseRangeFrame j₀ M e₀) (sectionwiseRangeFrame j₁ M e₁) V h₀ h₁ := by
  rw [sectionwiseRangeFrame_moduleIso, sectionwiseRangeFrame_moduleIso]
  exact rangeFrameCoefficient_moduleIso v _ _ _ _ _ _ _

/-- The native coordinate equation for the canonical presentation of an actual pulled
line. The input module is the literal direct pullback appearing in the original transition. -/
private theorem originalFrameTransition_presentedCoordinate {S : Type u} [CommRing S]
    {P₀ P₁ X Y : Scheme.{u}} (i : X ⟶ Y) (L : LineBundle Y)
    (p₀ : Spec (.of S) ⟶ P₀) (p₁ : Spec (.of S) ⟶ P₁)
    (j₀ : P₀ ⟶ X) (j₁ : P₁ ⟶ X)
    [IsOpenImmersion p₀] [IsOpenImmersion p₁]
    [IsOpenImmersion j₀] [IsOpenImmersion j₁]
    (h : p₀ ≫ j₀ = p₁ ≫ j₁)
    (e₀ : SheafOfModules.unit P₀.ringCatSheaf ≅
      (Scheme.Modules.pullback j₀).obj ((Scheme.Modules.pullback i).obj L.val))
    (e₁ : SheafOfModules.unit P₁.ringCatSheaf ≅
      (Scheme.Modules.pullback j₁).obj ((Scheme.Modules.pullback i).obj L.val)) (r : S)
    (c : (Scheme.Modules.pullback (p₁ ≫ j₁)).obj ((Scheme.Modules.pullback i).obj L.val) ⟶
      (Scheme.Modules.pullback (p₀ ≫ j₀)).obj ((Scheme.Modules.pullback i).obj L.val))
    (hs : (frameAlong p₁ j₁ ((Scheme.Modules.pullback i).obj L.val) e₁).hom ≫ c =
      affineMultiplication S r ≫
        (frameAlong p₀ j₀ ((Scheme.Modules.pullback i).obj L.val) e₀).hom)
    (hc : c = (pullbackCongr h.symm).hom.app ((Scheme.Modules.pullback i).obj L.val))
    (V : X.Opens) (hV : V = (p₀ ≫ j₀) ''ᵁ ⊤)
    (h₀ : V ≤ j₀.opensRange) (h₁ : V ≤ j₁.opensRange)
    (hv : (⊤ : (Spec (.of S)).Opens) ≤ (p₀ ≫ j₀) ⁻¹ᵁ V) :
    (Scheme.ΓSpecIso (.of S)).hom.hom
      (((p₀ ≫ j₀).appLE V ⊤ hv).hom
        (rangeFrameCoefficient (pullbackSectionModule i L) j₀.opensRange j₁.opensRange
          (sectionwiseRangeFrame j₀ _
            (e₀ ≪≫ (Scheme.Modules.pullback j₀).mapIso (pullbackSectionModuleIso i L).symm))
          (sectionwiseRangeFrame j₁ _
            (e₁ ≪≫ (Scheme.Modules.pullback j₁).mapIso (pullbackSectionModuleIso i L).symm))
          V h₀ h₁)) = r := by
  subst c
  exact originalFrameTransition_affineCoordinate p₀ p₁ j₀ j₁ h _ _ _ r
    (frameAlong_moduleIso_transition p₀ p₁ j₀ j₁ h (pullbackSectionModuleIso i L).symm
      e₀ e₁ (affineMultiplication S r) hs) V hV h₀ h₁ hv

private theorem ringIso_eq_inv {R S : CommRingCat.{u}} (e : R ≅ S) (x : R) (y : S)
    (h : e.hom.hom x = y) : x = e.inv.hom y :=
  (Iso.hom_inv_id_apply e x).symm.trans (congrArg e.inv.hom h)

end AlgebraicGeometry.Scheme.Blowup.RegularPoint

namespace AlgebraicGeometry.Scheme.Blowup.RegularPoint

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

/-- The common original chart of a Cartesian overlap has exactly the original range intersection. -/
theorem originalOverlap_opensRange {W P₀ P₁ X : Scheme.{u}}
    (p₀ : W ⟶ P₀) (p₁ : W ⟶ P₁) (j₀ : P₀ ⟶ X) (j₁ : P₁ ⟶ X)
    [IsOpenImmersion p₀] [IsOpenImmersion j₀] [IsOpenImmersion j₁]
    (h : IsPullback p₀ p₁ j₀ j₁) :
    (p₀ ≫ j₀).opensRange = j₀.opensRange ⊓ j₁.opensRange := by
  apply Opens.ext
  change Set.range (j₀ ∘ p₀) = Set.range j₀ ∩ Set.range j₁
  rw [Set.range_comp, Scheme.Pullback.Fibre.pullback_range_fst h,
    Set.image_preimage_eq_inter_range, Set.inter_comm]

end AlgebraicGeometry.Scheme.Blowup.RegularPoint

namespace AlgebraicGeometry.Scheme.Blowup.RegularPoint

open CategoryTheory Opposite AlgebraicGeometry Scheme.Modules Scheme.Modules.Invertible
open Scheme.Blowup.IdealFrames Scheme.PolynomialLaurent

variable {A : Type u} [CommRing A] (I : Ideal A) (a b : A)
  (hI : Ideal.span {a, b} = I) (ha : IsSMulRegular A a)
  (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b)
  (hb' : IsSMulRegular A b) (ha' : IsSMulRegular (A ⧸ Ideal.span {b}) a)

/-- The original Laurent centre map covers exactly the common open of the two actual charts. -/
theorem conormalOverlap_preimage :
    (laurentPlus (.of (A ⧸ I)) ≫ centreChart I a b hI ha hb) ⁻¹ᵁ
        ((centreChart I a b hI ha hb).opensRange ⊓
          (centreChart I b a (Ideal.span_pair_comm.trans hI) hb' ha').opensRange) = ⊤ := by
  rw [← originalOverlap_opensRange (laurentPlus (.of (A ⧸ I)))
    (laurentMinus (.of (A ⧸ I))) (centreChart I a b hI ha hb)
    (centreChart I b a (Ideal.span_pair_comm.trans hI) hb' ha')
    (centreCharts_isPullback I a b hI ha hb hb' ha'),
    Scheme.Hom.preimage_opensRange]

/-- The original positive Laurent map to the actual inverse-image centre. -/
def conormalOverlapMap : Spec (.of (LaurentPolynomial (A ⧸ I))) ⟶ centreScheme I :=
  laurentPlus (.of (A ⧸ I)) ≫ centreChart I a b hI ha hb

instance conormalOverlapMapIsOpenImmersion :
    IsOpenImmersion (conormalOverlapMap I a b hI ha hb) :=
  inferInstanceAs (IsOpenImmersion
    (laurentPlus (.of (A ⧸ I)) ≫ centreChart I a b hI ha hb))

/-- The checked canonical presentation of the literal native pullback of the kernel. -/
def conormalSectionModule : (centreScheme I).Modules :=
  pullbackSectionModule ((affineCenter A I).comap (blowdown I)).subschemeι (centreIdealLine I)

/-- The original canonical comparison to the actual conormal line, rather than a forced
judgmental identification of the two module presentations. -/
def conormalSectionModuleIso : conormalSectionModule I ≅ (centreConormalLine I).val :=
  pullbackSectionModuleIso ((affineCenter A I).comap (blowdown I)).subschemeι (centreIdealLine I)

/-- The same original kernel frame in the canonical section-module presentation. -/
def conormalSectionChartFrame :
    SheafOfModules.unit (Spec (.of (Polynomial (A ⧸ I)))).ringCatSheaf ≅
      (Scheme.Modules.pullback (centreChart I a b hI ha hb)).obj (conormalSectionModule I) :=
  conormalChartFrame I a b hI ha hb ≪≫
    (Scheme.Modules.pullback (centreChart I a b hI ha hb)).mapIso (conormalSectionModuleIso I).symm

/-- Following the canonical module comparison recovers the original parameter frame map. -/
theorem conormalSectionChartFrame_hom_original :
    (conormalSectionChartFrame I a b hI ha hb).hom ≫
        (Scheme.Modules.pullback (centreChart I a b hI ha hb)).map
          (conormalSectionModuleIso I).hom =
      (conormalChartFrame I a b hI ha hb).hom := by
  simp only [conormalSectionChartFrame, Iso.trans_hom, CategoryTheory.Functor.mapIso_hom,
    Iso.symm_hom, Category.assoc, ← CategoryTheory.Functor.map_comp,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.comp_id]

/-- The intersection of the original two centre chart ranges. -/
def conormalOverlapOpen : (centreScheme I).Opens :=
  (centreChart I a b hI ha hb).opensRange ⊓
    (centreChart I b a (Ideal.span_pair_comm.trans hI) hb' ha').opensRange

/-- The actual coefficient of the second kernel generator in the first original range frame. -/
def conormalOverlapCoefficient :
    Γ(centreScheme I, conormalOverlapOpen I a b hI ha hb hb' ha') :=
  rangeFrameCoefficient (conormalSectionModule I)
    (centreChart I a b hI ha hb).opensRange
    (centreChart I b a (Ideal.span_pair_comm.trans hI) hb' ha').opensRange
    (sectionwiseRangeFrame (centreChart I a b hI ha hb) (conormalSectionModule I)
      (conormalSectionChartFrame I a b hI ha hb))
    (sectionwiseRangeFrame (centreChart I b a (Ideal.span_pair_comm.trans hI) hb' ha')
      (conormalSectionModule I)
      (conormalSectionChartFrame I b a (Ideal.span_pair_comm.trans hI) hb' ha'))
    _ inf_le_left inf_le_right

/-- The coefficient is exactly that of the original actual conormal frames. The
canonical module transport changes neither the original generators nor their ratio. -/
theorem conormalOverlapCoefficient_original :
    conormalOverlapCoefficient I a b hI ha hb hb' ha' =
      rangeFrameCoefficient (centreConormalLine I).val
        (centreChart I a b hI ha hb).opensRange
        (centreChart I b a (Ideal.span_pair_comm.trans hI) hb' ha').opensRange
        (sectionwiseRangeFrame (centreChart I a b hI ha hb) (centreConormalLine I).val
          (conormalChartFrame I a b hI ha hb))
        (sectionwiseRangeFrame (centreChart I b a (Ideal.span_pair_comm.trans hI) hb' ha')
          (centreConormalLine I).val
          (conormalChartFrame I b a (Ideal.span_pair_comm.trans hI) hb' ha'))
        (conormalOverlapOpen I a b hI ha hb hb' ha') inf_le_left inf_le_right :=
  rangeFrameCoefficient_chartModuleIso (centreChart I a b hI ha hb)
    (centreChart I b a (Ideal.span_pair_comm.trans hI) hb' ha')
    (conormalSectionModuleIso I).symm
    (conormalChartFrame I a b hI ha hb)
    (conormalChartFrame I b a (Ideal.span_pair_comm.trans hI) hb' ha') _ _ _

/-- The actual overlap section map followed by the native affine-ring identification. -/
def conormalOverlapCoordinateMap :
    Γ(centreScheme I, conormalOverlapOpen I a b hI ha hb hb' ha') →+*
      LaurentPolynomial (A ⧸ I) :=
  (Scheme.ΓSpecIso (.of (LaurentPolynomial (A ⧸ I)))).hom.hom.comp
    ((conormalOverlapMap I a b hI ha hb).appLE
      (conormalOverlapOpen I a b hI ha hb hb' ha') ⊤
      (conormalOverlap_preimage I a b hI ha hb hb' ha').ge).hom

/-- The coordinate map retains the literal original ring-section map as its forward action. -/
theorem conormalOverlapCoordinateMap_apply
    (x : Γ(centreScheme I, conormalOverlapOpen I a b hI ha hb hb' ha')) :
    conormalOverlapCoordinateMap I a b hI ha hb hb' ha' x =
      (Scheme.ΓSpecIso (.of (LaurentPolynomial (A ⧸ I)))).hom.hom
        (((conormalOverlapMap I a b hI ha hb).appLE
          (conormalOverlapOpen I a b hI ha hb hb' ha') ⊤
          (conormalOverlap_preimage I a b hI ha hb hb' ha').ge).hom x) := rfl

/-- The original range intersection is exactly the image of the actual Laurent map. -/
theorem conormalOverlapOpen_eq_image :
    conormalOverlapOpen I a b hI ha hb hb' ha' = conormalOverlapMap I a b hI ha hb ''ᵁ ⊤ :=
  (originalOverlap_opensRange (laurentPlus (.of (A ⧸ I)))
    (laurentMinus (.of (A ⧸ I))) (centreChart I a b hI ha hb)
    (centreChart I b a (Ideal.span_pair_comm.trans hI) hb' ha')
    (centreCharts_isPullback I a b hI ha hb hb' ha')).symm.trans
      (conormalOverlapMap I a b hI ha hb).image_top_eq_opensRange.symm

-- Keep only the large frame and scalar wrappers opaque to automatic conversion in these
-- concrete comparisons. Their proved equations and targeted unfolding retain the actual maps.
attribute [local irreducible] frameAlong conormalChartFrame affineMultiplication

-- Respect the local opaque wrappers when the original equation determines the symbolic data.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option maxHeartbeats 800000 in
-- Matching the original concrete frame equation exhausted 400000 heartbeats in native builds.
-- This finite allowance remains local to that coordinate comparison; other declarations use 200000.
/-- The original coefficient has the literal positive Laurent coordinate in the actual ring. -/
theorem conormalOverlapCoordinateMap_coefficient :
    conormalOverlapCoordinateMap I a b hI ha hb hb' ha'
      (conormalOverlapCoefficient I a b hI ha hb hb' ha') = LaurentPolynomial.T 1 := by
  have hs := conormalLaurentFrames_transition I a b hI ha hb hb' ha'
  exact originalFrameTransition_presentedCoordinate
    ((affineCenter A I).comap (blowdown I)).subschemeι (centreIdealLine I)
    (laurentPlus (.of (A ⧸ I))) (laurentMinus (.of (A ⧸ I)))
    (centreChart I a b hI ha hb)
    (centreChart I b a (Ideal.span_pair_comm.trans hI) hb' ha')
    (centreCharts_laurent_compatibility I a b hI ha hb hb' ha')
    (conormalChartFrame I a b hI ha hb)
    (conormalChartFrame I b a (Ideal.span_pair_comm.trans hI) hb' ha')
    (LaurentPolynomial.T 1) _ hs rfl
    (conormalOverlapOpen I a b hI ha hb hb' ha')
    (conormalOverlapOpen_eq_image I a b hI ha hb hb' ha') inf_le_left inf_le_right
    (conormalOverlap_preimage I a b hI ha hb hb' ha').ge

/-- The actual common-chart section map sends the original coefficient to its native T(1)
section. This is obtained from the actual ring equation through the same Spec isomorphism. -/
theorem conormalOverlapCoefficient_laurent :
    ((conormalOverlapMap I a b hI ha hb).appLE
        (conormalOverlapOpen I a b hI ha hb hb' ha') ⊤
        (conormalOverlap_preimage I a b hI ha hb hb' ha').ge).hom
      (conormalOverlapCoefficient I a b hI ha hb hb' ha') =
      (Scheme.ΓSpecIso (.of (LaurentPolynomial (A ⧸ I)))).inv.hom (LaurentPolynomial.T 1) := by
  have H := conormalOverlapCoordinateMap_coefficient I a b hI ha hb hb' ha'
  rw [conormalOverlapCoordinateMap_apply] at H
  exact ringIso_eq_inv (Scheme.ΓSpecIso (.of (LaurentPolynomial (A ⧸ I)))) _ _ H

end AlgebraicGeometry.Scheme.Blowup.RegularPoint
