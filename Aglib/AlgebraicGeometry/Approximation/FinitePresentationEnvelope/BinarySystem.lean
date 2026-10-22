/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Approximation.FinitePresentationEnvelope.BinaryLimit
public import Aglib.AlgebraicGeometry.Approximation.FinitePresentationEnvelope.System

/-!
# Arithmetic systems obtained from actual binary open gluing

This packages the native pointwise pushout diagram and its proved limit cone.
Arithmetic finite type is checked on the two original open charts. Every
hypothesis concerns displayed maps, diagrams, and cartesian squares; no
gluing existence or limiting property of the resulting system is assumed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.FinitePresentationEnvelope.BinaryGluing

/-- Finite type over the arithmetic base is local on the two original charts. -/
lemma openPushout_finiteType
    {W U V : Scheme.{u}} (f : W ⟶ U) (g : W ⟶ V)
    [IsOpenImmersion f] [IsOpenImmersion g]
    [LocallyOfFiniteType (specULiftZIsTerminal.from U)]
    [LocallyOfFiniteType (specULiftZIsTerminal.from V)] :
    LocallyOfFiniteType (specULiftZIsTerminal.from (pushout f g)) := by
  apply IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFiniteType)
    (OpenNormalizationGluing.twoChartCover f g)
  intro a
  cases a
  · change LocallyOfFiniteType (pushout.inl f g ≫ specULiftZIsTerminal.from (pushout f g))
    rw [specULiftZIsTerminal.hom_ext
      (pushout.inl f g ≫ specULiftZIsTerminal.from (pushout f g))
      (specULiftZIsTerminal.from U)]
    infer_instance
  · change LocallyOfFiniteType (pushout.inr f g ≫ specULiftZIsTerminal.from (pushout f g))
    rw [specULiftZIsTerminal.hom_ext
      (pushout.inr f g ≫ specULiftZIsTerminal.from (pushout f g))
      (specULiftZIsTerminal.from V)]
    infer_instance

/-- Actual compatible open-chart systems glue to a system on their literal
original pushout. All stages, projections and transition maps are native. -/
def system
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    {W U V : I ⥤ Scheme.{u}} (f : W ⟶ U) (g : W ⟶ V)
    [∀ i, IsOpenImmersion (f.app i)] [∀ i, IsOpenImmersion (g.app i)]
    (hf : f.Equifibered) (hg : g.Equifibered)
    [∀ {i j} (r : i ⟶ j), IsAffineHom (U.map r)]
    [∀ {i j} (r : i ⟶ j), IsAffineHom (V.map r)]
    [∀ i, CompactSpace (U.obj i)] [∀ i, CompactSpace (V.obj i)]
    [∀ i, LocallyOfFiniteType (specULiftZIsTerminal.from (U.obj i))]
    [∀ i, LocallyOfFiniteType (specULiftZIsTerminal.from (V.obj i))]
    (cW : Cone W) (cU : Cone U) (cV : Cone V)
    (f₀ : cW.pt ⟶ cU.pt) (g₀ : cW.pt ⟶ cV.pt)
    [IsOpenImmersion f₀] [IsOpenImmersion g₀]
    (hf₀ : ∀ i, f₀ ≫ cU.π.app i = cW.π.app i ≫ f.app i)
    (hg₀ : ∀ i, g₀ ≫ cV.π.app i = cW.π.app i ≫ g.app i)
    (Hf : ∀ i, IsPullback (cW.π.app i) f₀ (f.app i) (cU.π.app i))
    (Hg : ∀ i, IsPullback (cW.π.app i) g₀ (g.app i) (cV.π.app i))
    (hcU : IsLimit cU) (hcV : IsLimit cV) : System (pushout f₀ g₀) where
  Index := I
  category := inferInstance
  cofiltered := inferInstance
  diagram := diagram f g
  projection := (cone f g cW cU cV f₀ g₀ hf₀ hg₀).π
  isLimit := isLimitCone f g hf hg cW cU cV f₀ g₀ hf₀ hg₀ Hf Hg hcU hcV
  affine r := map_isAffineHom f g hf hg r
  finiteType i := openPushout_finiteType (f.app i) (g.app i)
  compact _ := inferInstance

end AlgebraicGeometry.Scheme.FinitePresentationEnvelope.BinaryGluing
