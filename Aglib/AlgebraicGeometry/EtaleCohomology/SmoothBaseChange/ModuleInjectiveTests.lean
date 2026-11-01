/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.Underlying
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Reduction.ZModAcyclic
public import Aglib.AlgebraicGeometry.EtaleCohomology.Derived.BaseChange.Higher
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-! # Single-degree canonical exchange tests from genuine ringed injective vanishing

The two existing scalar and constant-ring equivalences transport an injective
ZMod-valued sheaf into a genuine ringed module sheaf. Their existing underlying
comparisons retain the original abelian coefficient. A supplied positive-degree
target vanishing then combines with the proved original source acyclicity to
make the same canonical higher exchange invertible. This does not supply target
vanishing, assume injectivity after forgetting scalars, or use all-degree tests.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

open Coefficients Proper.Reduction

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  moduleForget_preservesSheafification TorsionZMod.hasSheafifyStandard

/-- Positive-degree target vanishing on genuine ringed injectives gives the
original canonical exchange test on genuine ZMod-valued injectives in that
same degree. The target-vanishing input remains an independent producer. -/
theorem higherBaseChangeMap_zmodInjective_isIso_of_ringed_target_vanishing
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S')
    (g : S' ⟶ S) (g' : X' ⟶ X) (h : f' ≫ g = g' ≫ f) (n q : ℕ)
    (hvan : ∀ (I : ModuleSheaf X (ULift.{u + 1} (ZMod n))) [Injective I],
      IsZero ((higherDirectImage f' (q + 1)).obj ((inverseImage g').obj
        ((SheafOfModules.toSheaf (constantRing X (ULift.{u + 1} (ZMod n)))).obj I))))
    (M : ZModSheaf X n) [Injective M] :
    IsIso ((higherBaseChangeMap f f' g g' h (q + 1)).app ((zmodUnderlying X n).obj M)) := by
  let Λ := ULift.{u + 1} (ZMod n)
  let E₁ : ZModSheaf X n ≌ ModuleValuedSheaf X Λ :=
    TorsionZMod.Ringed.scalarSheafEquivalence.{u + 1, u, u + 1} X.smallEtaleTopology n
  let E₂ := moduleSheafEquivalence X Λ
  let N := E₁.functor.obj M
  let I := E₂.functor.obj N
  let : Injective N := E₁.functor.injective_obj M
  let : Injective I := E₂.functor.injective_obj N
  let e₂ : (SheafOfModules.toSheaf (constantRing X Λ)).obj I ≅
      (sheafCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj N :=
    (ModuleCat.Sheaf.ConstantRing.moduleSheafUnderlyingIso.{u + 1, u, u + 1, u + 1}
      X.smallEtaleTopology Λ).app N
  let e : (SheafOfModules.toSheaf (constantRing X Λ)).obj I ≅
      (zmodUnderlying X n).obj M :=
    e₂ ≪≫ (TorsionZMod.Ringed.scalarSheafUnderlyingIso.{u + 1, u, u + 1}
      X.smallEtaleTopology n).app M
  have htarget := (hvan I).of_iso
    ((higherDirectImage f' (q + 1)).mapIso ((inverseImage g').mapIso e)).symm
  let : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} X) := hasExtStandard X
  have hsource := (inverseImage g).map_isZero
    (higherDirectImage_zmodInjective_isZero f n M q)
  exact hsource.isIso htarget _

end AlgebraicGeometry.Scheme.EtaleCohomology
