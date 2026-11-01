/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.InternalHomLocalExactness
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.UnitValued

/-!
# Original internal-Hom acyclicity for finite locally constant sources

The local finite-module boundary proof and the original chart complex map
make the image of the native injective resolution exact in positive degrees.
The native right-derived comparison therefore proves vanishing on an actual
constant injective target, and in particular on the original unit when the
coefficient ring is self-injective. The source is not assumed locally free.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe c h

namespace ModuleCat.Sheaf.ConstantRing

variable {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
  (Λ : Type (max c h)) [CommRing Λ]
  [HasWeakSheafify J RingCat.{max c h}] [J.WEqualsLocallyBijective RingCat.{max c h}]
  [J.HasSheafCompose (CategoryTheory.forget RingCat.{max c h})]
  [J.HasSheafCompose (forget₂ CommRingCat.{max c h} RingCat.{max c h})]
  [HasSheafify J AddCommGrpCat.{max c h}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c h}]
  [J.HasSheafCompose (forget₂ (ModuleCat.{max c h} Λ) AddCommGrpCat.{max c h})]
  [∀ V : C, HasWeakSheafify (J.over V) RingCat.{max c h}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective RingCat.{max c h}]
  [∀ V : C, (J.over V).HasSheafCompose (CategoryTheory.forget RingCat.{max c h})]
  [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{max c h}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max c h}]
  [∀ V : C, (J.over V).HasSheafCompose
    (forget₂ (ModuleCat.{max c h} Λ) AddCommGrpCat.{max c h})]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{max c h})]



attribute [local instance] ModuleCat.Sheaf.hasSheafify

variable [IsNoetherianRing Λ]
  [EnoughInjectives (ModuleSheaf.{c, h, max c h, max c h} J Λ)]

-- Pin the same original category at the native internal-Hom derived-functor header.
set_option backward.isDefEq.respectTransparency false in
local instance internalHomAcyclic_enoughInjectives :
    EnoughInjectives (SheafOfModulesOfCommRing (commutativeSheaf J Λ)) :=
  inferInstanceAs (EnoughInjectives (ModuleSheaf.{c, h, max c h, max c h} J Λ))

set_option backward.isDefEq.respectTransparency false in
local instance internalHomAcyclic_homFunctor_additive
    (M : ModuleSheaf.{c, h, max c h, max c h} J Λ) :
    (SheafOfModules.InternalHom.homFunctor.{c, h, 0} (commutativeSheaf J Λ) M).Additive :=
  SheafOfModules.InternalHom.homFunctor_additive (commutativeSheaf J Λ) M

set_option backward.isDefEq.respectTransparency false in
/-- Original internal Hom has zero higher derived objects at an actual constant injective target. -/
theorem isZero_rightDerived_of_finiteConstantCharts
    (M N : ModuleSheaf.{c, h, max c h, max c h} J Λ)
    (hM : ModuleCat.Sheaf.HasFiniteTypeConstantCharts J
      ((moduleSheafEquivalence J Λ).inverse.obj M))
    (Q : ModuleCat.{max c h} Λ) [Injective Q]
    (θ : (Functor.const Cᵒᵖ).obj Q ⟶ ((moduleSheafEquivalence J Λ).inverse.obj N).obj)
    [CategoryTheory.Presheaf.IsLocallySurjective J θ]
    [CategoryTheory.Presheaf.IsLocallyInjective J θ] (q : ℕ) :
    IsZero (((SheafOfModules.InternalHom.homFunctor.{c, h, 0}
      (commutativeSheaf J Λ) M).rightDerived (q + 1)).obj N) := by
  let I : InjectiveResolution
      (C := SheafOfModulesOfCommRing (commutativeSheaf J Λ)) N := injectiveResolution N
  exact IsZero.of_iso
    (homFunctor_exactAt_of_finiteConstantCharts J Λ M N hM Q θ I q).isZero_homology
    (I.isoRightDerivedObj
      (SheafOfModules.InternalHom.homFunctor.{c, h, 0} (commutativeSheaf J Λ) M) (q + 1))

/-- The original unit is internally acyclic for finite constant-chart sources over a
self-injective coefficient ring. -/
theorem isZero_rightDerived_moduleUnit [Module.Injective Λ Λ]
    (M : ModuleSheaf.{c, h, max c h, max c h} J Λ)
    (hM : ModuleCat.Sheaf.HasFiniteTypeConstantCharts J
      ((moduleSheafEquivalence J Λ).inverse.obj M)) (q : ℕ) :
    IsZero (((SheafOfModules.InternalHom.homFunctor.{c, h, 0}
      (commutativeSheaf J Λ) M).rightDerived (q + 1)).obj (moduleUnit J Λ)) := by
  let : Injective (ModuleCat.of Λ Λ) := Module.injective_object_of_injective_module Λ Λ
  exact isZero_rightDerived_of_finiteConstantCharts J Λ M (moduleUnit J Λ) hM
    (ModuleCat.of Λ Λ) (moduleUnitConstantLinearMap J Λ) q

end ModuleCat.Sheaf.ConstantRing
