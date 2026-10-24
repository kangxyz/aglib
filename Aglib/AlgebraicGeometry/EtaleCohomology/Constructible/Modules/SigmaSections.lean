/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ConstantPullbackSections
public import Aglib.AlgebraicGeometry.Sites.EtaleSigmaSections
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.RingTheory.Finiteness.Basic

/-! # Literal module sections on an actual scheme coproduct

The linear equivalence is the original restriction to each component chart.
Its equivalent inverse-image presentation uses the original image adjunction.
Finite generation uses an actual finite product, never a submodule argument.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable (R : Type r) [CommRing R]

/-- Original inverse-image sections on an actual etale chart are the original
module value of that chart. -/
def moduleEtaleChartSectionsIso {X : Scheme.{u}} (F : ModuleSheaf R X) (U : X.Etale) :
    (moduleGlobalSections R U.left).obj ((moduleInverseImage R U.hom).obj F) ≅
      F.obj.obj (op U) := by
  let e : (siteEtalePostcompose U.hom).obj (etaleTerminal U.left) ≅ U :=
    MorphismProperty.Over.isoMk (Iso.refl _) (by rfl)
  exact (moduleGlobalSections R U.left).mapIso
      ((moduleInverseImageEtaleIso R U.hom).app F) ≪≫ F.obj.mapIso e.symm.op

/-- The chart comparison sends original unit pullback to literal restriction. -/
@[reassoc]
theorem moduleEtaleChartSectionsIso_restriction {X : Scheme.{u}}
    (F : ModuleSheaf R X) (U : X.Etale) :
    moduleGlobalSectionsPullback R U.hom F ≫ (moduleEtaleChartSectionsIso R F U).hom =
      F.obj.map ((etaleTerminalIsTerminal X).from U).op := by
  let e : (siteEtalePostcompose U.hom).obj (etaleTerminal U.left) ≅ U :=
    MorphismProperty.Over.isoMk (Iso.refl _) (by rfl)
  change moduleGlobalSectionsPullback R U.hom F ≫
    ((moduleGlobalSections R U.left).map ((moduleInverseImageEtaleIso R U.hom).hom.app F) ≫
      F.obj.map e.inv.op) = _
  let a := (etaleTerminalIsTerminal X).from
    ((siteEtalePostcompose U.hom).obj (etaleTerminal U.left))
  have h := moduleGlobalSectionsPullback_etale R U.hom F
  have ha : e.inv ≫ a = (etaleTerminalIsTerminal X).from U :=
    (etaleTerminalIsTerminal X).hom_ext _ _
  calc
    _ = (moduleGlobalSectionsPullback R U.hom F ≫
        (moduleGlobalSections R U.left).map
          ((moduleInverseImageEtaleIso R U.hom).hom.app F)) ≫ F.obj.map e.inv.op :=
      (Category.assoc _ _ _).symm
    _ = F.obj.map a.op ≫ F.obj.map e.inv.op :=
      congrArg (fun b => b ≫ F.obj.map e.inv.op) h
    _ = F.obj.map (e.inv ≫ a).op := (F.obj.map_comp a.op e.inv.op).symm
    _ = _ := congrArg (fun b => F.obj.map b.op) ha

variable {ι : Type u} (Y : ι → Scheme.{u})

/-- Literal component restrictions form the original linear product comparison. -/
def moduleSigmaSectionsLinearEquiv (F : ModuleSheaf R (∐ Y)) :
    (moduleGlobalSections R (∐ Y)).obj F ≃ₗ[R]
      ∀ i, F.obj.obj (op (Scheme.Etale.sigmaChart Y i)) :=
  LinearEquiv.ofBijective
    (LinearMap.pi (fun i => (F.obj.map (Scheme.Etale.sigmaChartInclusion Y i).op).hom))
    (Scheme.Etale.sigmaSections_bijective Y ((moduleUnderlying R (∐ Y)).obj F))

/-- Each coordinate is the literal original restriction map. -/
theorem moduleSigmaSectionsLinearEquiv_apply (F : ModuleSheaf R (∐ Y))
    (s : (moduleGlobalSections R (∐ Y)).obj F) (i : ι) :
    moduleSigmaSectionsLinearEquiv R Y F s i =
      F.obj.map (Scheme.Etale.sigmaChartInclusion Y i).op s := rfl

/-- Original sections are the product of original inverse-image component sections. -/
def moduleSigmaGlobalSectionsLinearEquiv (F : ModuleSheaf R (∐ Y)) :
    (moduleGlobalSections R (∐ Y)).obj F ≃ₗ[R]
      ∀ i, (moduleGlobalSections R (Y i)).obj
        ((moduleInverseImage R (Sigma.ι Y i)).obj F) :=
  (moduleSigmaSectionsLinearEquiv R Y F).trans
    (LinearEquiv.piCongrRight fun i =>
      (moduleEtaleChartSectionsIso R F (Scheme.Etale.sigmaChart Y i)).symm.toLinearEquiv)

/-- Finite component sections imply finite original sections, including the
empty coproduct, over an arbitrary coefficient ring. -/
theorem moduleGlobalSections_finite_of_finite_components [Finite ι]
    (F : ModuleSheaf R (∐ Y))
    (hF : ∀ i, Module.Finite R ((moduleGlobalSections R (Y i)).obj
      ((moduleInverseImage R (Sigma.ι Y i)).obj F))) :
    Module.Finite R ((moduleGlobalSections R (∐ Y)).obj F) := by
  let := hF
  exact Module.Finite.equiv (moduleSigmaGlobalSectionsLinearEquiv R Y F).symm

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
