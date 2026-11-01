/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Modules.Ext.OpenPullback

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry TopologicalSpace

universe u v u' v' u'' v'' u''' v''' w₁ w₂ w₃ w₄

section IndependentWorlds

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w₁} C]
    {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w₂} D]
    {E : Type u''} [Category.{v''} E] [Abelian E] [HasExt.{w₃} E]
    {F : Type u'''} [Category.{v'''} F] [Abelian F] [HasExt.{w₄} F]
    (FX : C ⥤ E) [FX.Additive] [PreservesFiniteLimits FX] [PreservesFiniteColimits FX]
    (FY : D ⥤ F) [FY.Additive] [PreservesFiniteLimits FY] [PreservesFiniteColimits FY]
    (P : C ⥤ D) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (Q : E ⥤ F) [Q.Additive] [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]

/-- The four original Ext worlds remain independent even after evaluation
of the whole actual operator square. -/
example (τ : FX ⋙ Q ⟶ P ⋙ FY) {UX : C} {UY : D} {IX : E} {IY : F}
    (a : IX ⟶ FX.obj UX) (b : IY ⟶ FY.obj UY)
    (α : IY ⟶ Q.obj IX) (β : UY ⟶ P.obj UX)
    (hsource : α ≫ Q.map a ≫ τ.app UX = b ≫ FY.map β) (M : C) (n : ℕ)
    (x : Ext.{w₁} UX M n) :
    ((Ext.mk₀ α).comp
      (((Ext.mk₀ a).comp (x.mapExactFunctor FX) (zero_add n)).mapExactFunctor Q)
        (zero_add n)).comp (Ext.mk₀ (τ.app M)) (add_zero n) =
      (Ext.mk₀ b).comp
        (((Ext.mk₀ β).comp (x.mapExactFunctor P) (zero_add n)).mapExactFunctor FY)
          (zero_add n) :=
  DFunLike.congr_fun
    (Functor.extPrecompMap_naturality_square FX FY P Q τ a b α β hsource M n) x

end IndependentWorlds

namespace AlgebraicGeometry.Scheme.Cohomology

variable {X Y Z : Scheme.{u}} (p : Y ⟶ X)

/-- Degree-zero geometric pullback of the actual integer-open generator
needs no Flat premise and retains the original inverse module-open Iso. -/
example (U : X.Opens) :
    (zariskiCohomologyOpenMap p (moduleAddSheaf X (Modules.openFree X U))
        (moduleAddSheaf Y ((Modules.pullback p).obj (Modules.openFree X U)))
        ((modulePullbackAdditiveComparison p).app (Modules.openFree X U)) 0).app (op U)
        (Ext.mk₀ (moduleOpenIntegerMap X U)) =
      Ext.mk₀ (moduleOpenIntegerMap Y (p ⁻¹ᵁ U) ≫
        (SheafOfModules.toSheaf.{u} Y.ringCatSheaf).map
          (Modules.openFreePullbackIso p U).inv) := by
  change ((Ext.mk₀ ((additiveOpenPullbackIso p).inv.app U)).comp
      ((Ext.mk₀ (moduleOpenIntegerMap X U)).mapExactFunctor (zariskiPullback p))
        (zero_add 0)).comp
      (Ext.mk₀ ((modulePullbackAdditiveComparison p).app (Modules.openFree X U)))
        (add_zero 0) = _
  simp only [Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀, Category.assoc]
  rw [moduleOpenIntegerMap_pullback p U]

/-- Top-source normalization is an original module-arrow equation for any morphism. -/
example :
    (Modules.openFreePullbackIso p ⊤).hom ≫ moduleOpenTopUnitMap Y =
      (Modules.pullback p).map (moduleOpenTopUnitMap X) ≫ (Modules.pullbackUnitIso p).hom :=
  moduleOpenTopUnitMap_pullback p

/-- The same original open-free source comparison respects native pullback composition. -/
example (f : Y ⟶ X) (g : Z ⟶ Y) (U : X.Opens) :
    (Modules.pullbackComp g f).hom.app (Modules.openFree X U) ≫
        (Modules.openFreePullbackIso (g ≫ f) U).hom =
      (Modules.pullback g).map (Modules.openFreePullbackIso f U).hom ≫
        (Modules.openFreePullbackIso g (f ⁻¹ᵁ U)).hom :=
  Modules.openFreePullbackIso_comp g f U

example (U : X.Opens) :
    (Modules.pullbackId X).hom.app (Modules.openFree X U) =
      (Modules.openFreePullbackIso (𝟙 X) U).hom :=
  Modules.openFreePullbackIso_id X U

/-- The current consumer's literal original H' operator, with no QC or field hypotheses. -/
example [Flat p] (U : X.Opens) (M : X.Modules) (n : ℕ)
    (x : Ext.{u + 1} (Modules.openFree X U) M n) :
    (zariskiCohomologyOpenMap p (moduleAddSheaf X M)
        (moduleAddSheaf Y ((Modules.pullback p).obj M))
          ((modulePullbackAdditiveComparison p).app M) n).app (op U)
        (moduleOpenExtCohomologyMap X U M n x) =
      moduleOpenExtCohomologyMap Y (p ⁻¹ᵁ U) ((Modules.pullback p).obj M) n
        ((Ext.mk₀ (Modules.openFreePullbackIso p U).inv).comp
          (x.mapExactFunctor (Modules.pullback p)) (zero_add n)) :=
  moduleOpenExtCohomologyMap_pullback p U M n x

end AlgebraicGeometry.Scheme.Cohomology

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.moduleOpenIntegerNatTrans_pullback' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.moduleOpenIntegerNatTrans_pullback

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.moduleOpenExtCohomologyMap_pullback' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.moduleOpenExtCohomologyMap_pullback
