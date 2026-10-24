/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.Locality
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Universal.ModelTransport

/-! # Horizontal closure of the existing bounded exchange test

The existing `Proper.boundedExchange` is an all-degree test on the original
n-killed coefficients, not a properness assumption. Native horizontal pasting
and actual target-locality preserve this same regular test before geometric
pullback squares are substituted. No second bounded-exchange definition is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Scheme.EtaleCohomology.SmoothReduction

attribute [local instance] hasSheafifyLarge HasDerivedCategory.standard

/-- The original arbitrary-cartesian étale comparison supplies the existing
all-degree test on every n-killed coefficient. -/
theorem boundedExchange_etale (n : ℕ) {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : IsPullback g' f' f g) [Etale g] :
    Proper.boundedExchange n f f' g g' h.w.symm := by
  intro F _ q
  have := higherBaseChangeMap_etale_isIso_of_isPullback f f' g g' h q
  infer_instance

/-- Original horizontal pasting preserves the same all-degree bounded test.
The second coefficient is its literal inverse image and remains n-killed. -/
theorem boundedExchange_hComp (n : ℕ) {X₀ X₁ X₂ S₀ S₁ S₂ : Scheme.{u}}
    (f₀ : X₀ ⟶ S₀) (f₁ : X₁ ⟶ S₁) (f₂ : X₂ ⟶ S₂)
    (g₁ : S₁ ⟶ S₀) (g₂ : S₂ ⟶ S₁) (h₁ : X₁ ⟶ X₀) (h₂ : X₂ ⟶ X₁)
    (e₁ : f₁ ≫ g₁ = h₁ ≫ f₀) (e₂ : f₂ ≫ g₂ = h₂ ≫ f₁)
    (e : f₂ ≫ (g₂ ≫ g₁) = (h₂ ≫ h₁) ≫ f₀)
    (H₁ : Proper.boundedExchange n f₀ f₁ g₁ h₁ e₁)
    (H₂ : Proper.boundedExchange n f₁ f₂ g₂ h₂ e₂) :
    Proper.boundedExchange n f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e := by
  intro F hF q
  have hF₁ : n • 𝟙 ((inverseImage h₁).obj F) = 0 := by
    have hm := congrArg (fun a => (inverseImage h₁).map a) hF
    simpa only [CategoryTheory.Functor.map_nsmul, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_zero] using hm
  have : IsIso ((higherBaseChangeMap f₀ f₁ g₁ h₁ e₁ q).app F) := H₁ F hF q
  have : IsIso ((higherBaseChangeMap f₁ f₂ g₂ h₂ e₂ q).app
      ((inverseImage h₁).obj F)) := H₂ _ hF₁ q
  exact higherBaseChangeMap_isIso_hComp f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e F q

private theorem higherExchangeTest_of_boundedExchange (n : ℕ)
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f) (hf : Proper.boundedExchange n f f' g g' h)
    (F : AbelianSheaf.{u, u + 1} X) (hF : n • 𝟙 F = 0) (q : ℕ) :
    higherExchangeTest f f' g g' h (𝟭 _) F q := hf F hF q

private theorem boundedExchange_of_higherExchangeTest (n : ℕ)
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f)
    (hf : ∀ (F : AbelianSheaf.{u, u + 1} X), n • 𝟙 F = 0 →
      ∀ q : ℕ, higherExchangeTest f f' g g' h (𝟭 _) F q) :
    Proper.boundedExchange n f f' g g' h := hf

/-- Target étale locality of the same original all-degree bounded test, with
abstract actual chart squares retained before literal pullbacks are supplied. -/
theorem boundedExchange_of_etaleCover (n : ℕ) {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f) {ι : Type v} (U : ι → S'.Etale)
    (hU : ∀ s : S', ∃ (i : ι) (x : (U i).left), (U i).hom x = s)
    (Y : ι → Scheme.{u}) (p : ∀ i, Y i ⟶ (U i).left) (k : ∀ i, Y i ⟶ X')
    (hp : ∀ i, IsPullback (k i) (p i) f' (U i).hom)
    (hc : ∀ i, p i ≫ ((U i).hom ≫ g) = (k i ≫ g') ≫ f)
    (hloc : ∀ i, Proper.boundedExchange n f (p i) ((U i).hom ≫ g)
      (k i ≫ g') (hc i)) :
    Proper.boundedExchange n f f' g g' h :=
  boundedExchange_of_higherExchangeTest n f f' g g' h fun F hF q =>
    higherExchangeTest_of_etale_cover f f' g g' h U hU Y p k hp hc F q fun i =>
      higherExchangeTest_of_boundedExchange n
        f (p i) ((U i).hom ≫ g) (k i ≫ g') (hc i) (hloc i) F hF q

end AlgebraicGeometry.Scheme.EtaleCohomology.SmoothReduction
