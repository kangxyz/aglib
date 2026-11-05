/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.ArithmeticPrincipalOpenH1
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.EtaleCoefficientComponentClass

/-! # Outer degree induction supplies the actual refined open-summand vanishing

The original principal-open restriction of a genuine injective stays injective.
Every later target-etale refinement remains a smooth relative curve over the
same coefficient base. Thus strictly lower arithmetic vanishing supplies the
original lower higher-images required by the Leray support detector.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u
attribute [local instance] hasSheafifyLarge hasSheafifyModules

/-- Discharge, rather than assume, the refined open-part vanishing from the
outer induction in strictly smaller positive cohomological degrees. -/
theorem arithmetic_principal_refinement_lower_higherImage_isZero
    (q : ℕ)
    (ih : ∀ r : ℕ, 1 ≤ r → r < q → ArithmeticCurveModuleInjectiveVanishing.{u} r)
    (S : Type u) [CommRing S] [Algebra.FiniteType ℤ S] (s : S)
    {G Y : Scheme.{u}} (b : Y ⟶ Spec (.of S)) [SmoothOfRelativeDimension 1 b]
    (a : Y ⟶ G) (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : S))
    (I : ModuleSheaf (Spec (.of S)) (ULift.{u + 1} (ZMod n))) [Injective I]
    (U : G.Etale) :
    let t := pullback.snd U.hom a
    let j' := pullback.snd (principalSupportOpen S s).ι b
    let bU := pullback.fst (principalSupportOpen S s).ι b
    let j₂ := pullback.snd j' t
    let bU₂ := pullback.fst j' t ≫ bU
    ∀ r : ℕ, 1 ≤ r → r < q →
      IsZero ((higherDirectImage j₂ r).obj ((inverseImage bU₂).obj
        ((SheafOfModules.toSheaf (constantRing (principalSupportOpen S s).toScheme
          (ULift.{u + 1} (ZMod n)))).obj
          ((moduleInverseImage (principalSupportOpen S s).ι
            (ULift.{u + 1} (ZMod n))).obj I)))) := by
  let j := (principalSupportOpen S s).ι
  let t := pullback.snd U.hom a
  let j' := pullback.snd j b
  let bU := pullback.fst j b
  let j₂ := pullback.snd j' t
  let bU₂ := pullback.fst j' t ≫ bU
  let : Etale U.hom := U.prop
  let : Etale t := inferInstanceAs (Etale (pullback.snd U.hom a))
  let : SmoothOfRelativeDimension 1 (t ≫ b) := by
    simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 1 t b
  have H : IsPullback bU₂ j₂ j (t ≫ b) :=
    (IsPullback.of_hasPullback j' t).paste_horiz (IsPullback.of_hasPullback j b)
  let J := (moduleInverseImage j (ULift.{u + 1} (ZMod n))).obj I
  let : Injective J := moduleInverseImage_etale_injective j _ I
  dsimp only
  intro r hr hrq
  exact higherDirectImage_arithmetic_principalOpen_injective_isZero
    r (ih r hr hrq) S s (t ≫ b) j₂ bU₂ H n hn hunit J

end AlgebraicGeometry.Scheme.EtaleCohomology
