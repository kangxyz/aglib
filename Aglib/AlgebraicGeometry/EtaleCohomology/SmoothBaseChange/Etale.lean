/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.EtaleInverseImageInjectives
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.EtaleDirectImageMate
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Reduction.SingleHigher
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Reduction.ExchangeShift
public import Aglib.Algebra.Homology.DerivedCategory.Plus.InjectiveComparison

/-! # Canonical étale base change in every natural degree

For an arbitrary scheme morphism and arbitrary abelian coefficients, the
original higher exchange maps are invertible under étale
base change. The proof uses the original ordinary mate, preservation of
injectives by étale inverse image, and native injective-single comparison.
No properness, quasi-compactness or torsion premise is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u dX dS dX' dS'

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) [Etale g]
  [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{dX'} (AbelianSheaf.{u, u + 1} (pullback g f))]
  [HasDerivedCategory.{dS'} (AbelianSheaf.{u, u + 1} S')]

/-- The original higher exchange is invertible on actual injective coefficients. -/
theorem higherBaseChangeMap_etale_injective_isIso
    (I : AbelianSheaf.{u, u + 1} X) [Injective I] (q : ℕ) :
    IsIso ((higherBaseChangeMap f (pullback.fst g f) g (pullback.snd g f)
      pullback.condition q).app I) := by
  cases q with
  | zero =>
    have hz := higherBaseChangeMap_zero f (pullback.fst g f) g (pullback.snd g f)
      pullback.condition I
    dsimp only [Functor.HigherExchangeZeroEquation] at hz
    apply (isIso_comp_right_iff _
      ((directImage (pullback.fst g f)).rightDerivedZeroIsoSelf.hom.app
        ((inverseImage (pullback.snd g f)).obj I))).mp
    rw [← hz]
    infer_instance
  | succ q =>
    exact ((inverseImage g).map_isZero
      ((directImage f).isZero_rightDerived_obj_injective_succ q I)).isIso
      ((directImage (pullback.fst g f)).isZero_rightDerived_obj_injective_succ q
        ((inverseImage (pullback.snd g f)).obj I)) _

/-- Original étale derived exchange on a degree-zero single, with no condition
on the abelian coefficient. -/
theorem derivedBaseChangeMap_etale_single_isIso
    (F : AbelianSheaf.{u, u + 1} X) :
    IsIso ((derivedBaseChangeMap f (pullback.fst g f) g (pullback.snd g f)
      pullback.condition).app
        ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F)) := by
  let τ := derivedBaseChangeMap f (pullback.fst g f) g (pullback.snd g f)
    pullback.condition
  let : NatTrans.CommShift τ ℤ :=
    Proper.Reduction.derivedBaseChangeMap_commShift f (pullback.fst g f) g
      (pullback.snd g f) pullback.condition
  apply DerivedCategory.Plus.InjectiveComparison.isIso_app_single_of_injective _ _ τ
  · intro M
    let K := (DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj M
    let : ((derivedDirectImage f).obj K).IsGE 0 :=
      (directImage f).rightDerivedFunctorPlus_isGE K 0
    exact (inverseImage g).rightDerivedFunctorPlus_isGE ((derivedDirectImage f).obj K) 0
  · intro M
    let K := (DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj M
    let : ((derivedInverseImage (pullback.snd g f)).obj K).IsGE 0 :=
      (inverseImage (pullback.snd g f)).rightDerivedFunctorPlus_isGE K 0
    exact (directImage (pullback.fst g f)).rightDerivedFunctorPlus_isGE
      ((derivedInverseImage (pullback.snd g f)).obj K) 0
  · intro I hI
    exact (Proper.Reduction.derivedBaseChangeMap_single_isIso_iff_higher f
      (pullback.fst g f) g (pullback.snd g f) pullback.condition I).mpr
        (higherBaseChangeMap_etale_injective_isIso f g I)

/-- The canonical higher base-change map along an étale morphism is invertible
in every natural degree for every abelian sheaf. -/
theorem higherBaseChangeMap_etale_isIso (q : ℕ) :
    IsIso (higherBaseChangeMap f (pullback.fst g f) g (pullback.snd g f)
      pullback.condition q) := by
  have (F : AbelianSheaf.{u, u + 1} X) :
      IsIso ((higherBaseChangeMap f (pullback.fst g f) g (pullback.snd g f)
        pullback.condition q).app F) :=
    (Proper.Reduction.derivedBaseChangeMap_single_isIso_iff_higher f
      (pullback.fst g f) g (pullback.snd g f) pullback.condition F).mp
        (derivedBaseChangeMap_etale_single_isIso f g F) q
  exact NatIso.isIso_of_isIso_app _

end AlgebraicGeometry.Scheme.EtaleCohomology
