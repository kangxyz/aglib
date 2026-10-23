/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Reduction.ExchangeShift
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Reduction.InjectiveExchange
public import Aglib.Algebra.Homology.DerivedCategory.Plus.InjectiveComparison
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.TStructure

/-! # Original exchange on all genuine module coefficients

The exact original underlying functor has a native bounded-below derived
functor. Precomposing the actual canonical exchange with that functor gives
a shift-compatible triangulated comparison. Its two sides preserve the
nonnegative range, so tests on genuine module injectives extend to all
genuine module singles by finite degree induction. The original exact-single
comparison transports back to the displayed canonical exchange map.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper.Reduction

universe u dX dS dX' dS'

attribute [local instance] hasSheafifyLarge TorsionZMod.hasSheafifyStandard

variable {X S X' S' : Scheme.{u}}
  [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{dX'} (AbelianSheaf.{u, u + 1} X')]
  [HasDerivedCategory.{dS'} (AbelianSheaf.{u, u + 1} S')]
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f) (n : ℕ)

/-- Tests on underlying genuine module injectives imply invertibility of the
same original canonical derived exchange on every underlying module single.
The auxiliary module-derived model is supplied by the native standard
producer; all four original abelian-derived universes remain independent. -/
theorem derivedExchange_on_all_zmodCoefficients
    (hI : ∀ (I : ZModSheaf X n) [Injective I],
      IsIso ((derivedBaseChangeMap f f' g g' h).app
        ((zmodSingle X n).obj I)))
    (M : ZModSheaf X n) :
    IsIso ((derivedBaseChangeMap f f' g g' h).app
      ((zmodSingle X n).obj M)) := by
  let : HasDerivedCategory.{u + 2} (ZModSheaf X n) :=
    HasDerivedCategory.standard (ZModSheaf X n)
  let U : ZModSheaf X n ⥤ AbelianSheaf.{u, u + 1} X := zmodUnderlying X n
  have : U.Additive :=
    { map_add := by
        intro A B a b
        apply Sheaf.hom_ext
        apply NatTrans.ext
        funext V
        rfl }
  have : PreservesFiniteLimits U :=
    TorsionZMod.underlying_preservesFiniteLimits.{u + 1, u} X.smallEtaleTopology n
  have : PreservesFiniteColimits U :=
    TorsionZMod.underlying_preservesFiniteColimits.{u + 1, u} X.smallEtaleTopology n
  have : EnoughInjectives (ZModSheaf X n) :=
    TorsionZMod.enoughInjectivesStandard.{u + 1, u} X.smallEtaleTopology n
  let β := derivedBaseChangeMap f f' g g' h
  have : NatTrans.CommShift β ℤ := derivedBaseChangeMap_commShift f f' g g' h
  let F := U.rightDerivedFunctorPlus ⋙ (derivedDirectImage f ⋙ derivedInverseImage g)
  let G := U.rightDerivedFunctorPlus ⋙ (derivedInverseImage g' ⋙ derivedDirectImage f')
  let α : F ⟶ G := Functor.whiskerLeft U.rightDerivedFunctorPlus β
  let e (N : ZModSheaf X n) :
      U.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor (ZModSheaf X n) 0).obj N) ≅
        (zmodSingle X n).obj N :=
    (U.rightDerivedFunctorPlusSingleIso 0).app N
  have hF (N : ZModSheaf X n) :
      (F.obj ((DerivedCategory.Plus.singleFunctor (ZModSheaf X n) 0).obj N)).IsGE 0 := by
    have := U.rightDerivedFunctorPlus_isGE
      ((DerivedCategory.Plus.singleFunctor (ZModSheaf X n) 0).obj N) 0
    have := (directImage f).rightDerivedFunctorPlus_isGE
      (U.rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor (ZModSheaf X n) 0).obj N)) 0
    exact (inverseImage g).rightDerivedFunctorPlus_isGE _ 0
  have hG (N : ZModSheaf X n) :
      (G.obj ((DerivedCategory.Plus.singleFunctor (ZModSheaf X n) 0).obj N)).IsGE 0 := by
    have := U.rightDerivedFunctorPlus_isGE
      ((DerivedCategory.Plus.singleFunctor (ZModSheaf X n) 0).obj N) 0
    have := (inverseImage g').rightDerivedFunctorPlus_isGE
      (U.rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor (ZModSheaf X n) 0).obj N)) 0
    exact (directImage f').rightDerivedFunctorPlus_isGE _ 0
  have hJ (I : ZModSheaf X n) [Injective I] :
      IsIso (α.app ((DerivedCategory.Plus.singleFunctor (ZModSheaf X n) 0).obj I)) := by
    exact (NatTrans.isIso_app_iff_of_iso β (e I)).mpr (hI I)
  have hM := DerivedCategory.Plus.InjectiveComparison.isIso_app_single_of_injective
    F G α hF hG hJ M
  exact (NatTrans.isIso_app_iff_of_iso β (e M)).mp hM

/-- An actual n-killed abelian coefficient carries its canonical genuine-module
structure. No supplied coefficient marking is needed, and the conclusion is
the same original derived exchange on that coefficient's original single. -/
theorem derivedExchange_on_killedCoefficients
    (hI : ∀ (I : ZModSheaf X n) [Injective I],
      IsIso ((derivedBaseChangeMap f f' g g' h).app
        ((zmodSingle X n).obj I)))
    (F : AbelianSheaf.{u, u + 1} X) (hF : n • 𝟙 F = 0) :
    IsIso ((derivedBaseChangeMap f f' g g' h).app
      ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F)) := by
  let M : ZModSheaf X n := TorsionZMod.sheaf X.smallEtaleTopology n F hF
  let e : (zmodUnderlying X n).obj M ≅ F :=
    TorsionZMod.sheafUnderlyingIso X.smallEtaleTopology n F hF
  let e' : (zmodSingle X n).obj M ≅
      (DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F :=
    (DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).mapIso e
  have hM := derivedExchange_on_all_zmodCoefficients f f' g g' h n hI M
  exact (NatTrans.isIso_app_iff_of_iso (derivedBaseChangeMap f f' g g' h) e').mp hM

/-- Every original natural-degree higher exchange is invertible on an actual
coefficient annihilated by the specified modulus, from genuine injective tests. -/
theorem higherExchange_on_killedCoefficients
    (hI : ∀ (I : ZModSheaf X n) [Injective I],
      IsIso ((derivedBaseChangeMap f f' g g' h).app
        ((zmodSingle X n).obj I)))
    (F : AbelianSheaf.{u, u + 1} X) (hF : n • 𝟙 F = 0) (q : ℕ) :
    IsIso ((higherBaseChangeMap f f' g g' h q).app F) := by
  have := derivedExchange_on_killedCoefficients f f' g g' h n hI F hF
  exact higherBaseChangeMap_isIso_app_of_derived f f' g g' h F q

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper.Reduction
