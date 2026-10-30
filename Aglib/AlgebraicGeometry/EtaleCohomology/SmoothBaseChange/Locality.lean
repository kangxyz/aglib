/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.Horizontal
public import Aglib.AlgebraicGeometry.EtaleCohomology.EtaleCover

/-! # Horizontal composition and target locality of the original higher exchange

All calculations use the native exact horizontal-pasting equation. Étale
comparison for the second cartesian square makes the original exchange local
on its target, tested by any jointly surjective actual étale family. The
coefficient is arbitrary and is never replaced by a new cohomology model.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u v dX₀ dX₁ dX₂ dS₀ dS₁ dS₂

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

/-- A shared regular head for the actual original exchange tested by an
actual postfunctor. The identity functor is the original comparison itself;
a chart inverse image is precisely its local test. -/
def higherExchangeTest {X S X' S' T : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f)
    (E : AbelianSheaf.{u, u + 1} S' ⥤ AbelianSheaf.{u, u + 1} T)
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) : Prop :=
  IsIso (E.map ((higherBaseChangeMap f f' g g' h q).app F))

section OriginalComponent

variable {X S X' S' : Scheme.{u}}
  [HasDerivedCategory.{dX₀} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dS₀} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{dX₁} (AbelianSheaf.{u, u + 1} X')]
  [HasDerivedCategory.{dS₁} (AbelianSheaf.{u, u + 1} S')]
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f) (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)

omit [HasDerivedCategory.{dX₀} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dS₀} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{dX₁} (AbelianSheaf.{u, u + 1} X')]
  [HasDerivedCategory.{dS₁} (AbelianSheaf.{u, u + 1} S')] in
private theorem higherExchangeTest_of_isIso
    (hi : IsIso ((higherBaseChangeMap f f' g g' h q).app F)) :
    higherExchangeTest f f' g g' h (𝟭 _) F q := hi

omit [HasDerivedCategory.{dX₀} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dS₀} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{dX₁} (AbelianSheaf.{u, u + 1} X')]
  [HasDerivedCategory.{dS₁} (AbelianSheaf.{u, u + 1} S')] in
private theorem higherExchangeTest_isIso
    (hi : higherExchangeTest f f' g g' h (𝟭 _) F q) :
    IsIso ((higherBaseChangeMap f f' g g' h q).app F) := hi

end OriginalComponent

section SingleSquare

variable {X₀ X₁ X₂ S₀ S₁ S₂ : Scheme.{u}}
  [HasDerivedCategory.{dX₀} (AbelianSheaf.{u, u + 1} X₀)]
  [HasDerivedCategory.{dX₁} (AbelianSheaf.{u, u + 1} X₁)]
  [HasDerivedCategory.{dX₂} (AbelianSheaf.{u, u + 1} X₂)]
  [HasDerivedCategory.{dS₀} (AbelianSheaf.{u, u + 1} S₀)]
  [HasDerivedCategory.{dS₁} (AbelianSheaf.{u, u + 1} S₁)]
  [HasDerivedCategory.{dS₂} (AbelianSheaf.{u, u + 1} S₂)]
  (f₀ : X₀ ⟶ S₀) (f₁ : X₁ ⟶ S₁) (f₂ : X₂ ⟶ S₂)
  (g₁ : S₁ ⟶ S₀) (g₂ : S₂ ⟶ S₁) (h₁ : X₁ ⟶ X₀) (h₂ : X₂ ⟶ X₁)
  (e₁ : f₁ ≫ g₁ = h₁ ≫ f₀)
  (e : f₂ ≫ (g₂ ≫ g₁) = (h₂ ≫ h₁) ≫ f₀)
  (F : AbelianSheaf.{u, u + 1} X₀) (q : ℕ)

omit [HasDerivedCategory.{dX₀} (AbelianSheaf.{u, u + 1} X₀)]
  [HasDerivedCategory.{dS₀} (AbelianSheaf.{u, u + 1} S₀)] in
/-- Original single-square cancellation, at the same shared test head on
both sides before any indexed chart data is substituted. -/
private theorem higherExchangeTest_inverseImage_of_etale_hComp
    [Etale g₂] (hp : IsPullback h₂ f₂ f₁ g₂)
    (hcomp : higherExchangeTest f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e (𝟭 _) F q) :
    higherExchangeTest f₀ f₁ g₁ h₁ e₁ (inverseImage g₂) F q :=
  higherBaseChangeMap_inverseImage_isIso_of_etale_hComp
    f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e F q hp hcomp

end SingleSquare

section EtaleLocality

variable {X S X' S' : Scheme.{u}} {ι : Type v}
  [DX : HasDerivedCategory.{dX₀} (AbelianSheaf.{u, u + 1} X)]
  [DS : HasDerivedCategory.{dS₀} (AbelianSheaf.{u, u + 1} S)]
  [DX' : HasDerivedCategory.{dX₁} (AbelianSheaf.{u, u + 1} X')]
  [DS' : HasDerivedCategory.{dS₁} (AbelianSheaf.{u, u + 1} S')]
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f)
  (U : ι → S'.Etale)
  (hU : ∀ s : S', ∃ (i : ι) (x : (U i).left), (U i).hom x = s)

omit [HasDerivedCategory.{dX₀} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dS₀} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{dX₁} (AbelianSheaf.{u, u + 1} X')]
  [HasDerivedCategory.{dS₁} (AbelianSheaf.{u, u + 1} S')] in
include hU in
/-- Cover detection at the same original-map test head. The coefficient and
square are unchanged throughout this family. -/
private theorem higherExchangeTest_of_etale_inverseImages
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)
    (hloc : ∀ i, higherExchangeTest f f' g g' h (inverseImage (U i).hom) F q) :
    higherExchangeTest f f' g g' h (𝟭 _) F q :=
  isIso_of_etale_inverseImages U hU _ hloc

variable (Y : ι → Scheme.{u})
  [DY : ∀ i, HasDerivedCategory.{dX₂} (AbelianSheaf.{u, u + 1} (Y i))]
  [DU : ∀ i, HasDerivedCategory.{dS₂} (AbelianSheaf.{u, u + 1} (U i).left)]
  (p : ∀ i, Y i ⟶ (U i).left) (k : ∀ i, Y i ⟶ X')
  (hp : ∀ i, IsPullback (k i) (p i) f' (U i).hom)
  (hc : ∀ i, p i ≫ ((U i).hom ≫ g) = (k i ≫ g') ≫ f)

include hU hp

omit DX DS in
/-- Assemble the indexed original-map tests without unfolding their common
regular head. This introduces no new mathematical condition. -/
theorem higherExchangeTest_of_etale_cover
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)
    (hloc : ∀ i, higherExchangeTest f (p i) ((U i).hom ≫ g)
      (k i ≫ g') (hc i) (𝟭 _) F q) :
    higherExchangeTest f f' g g' h (𝟭 _) F q :=
  higherExchangeTest_of_etale_inverseImages f f' g g' h U hU F q fun i =>
    higherExchangeTest_inverseImage_of_etale_hComp f f' (p i) g (U i).hom
      g' (k i) h (hc i) F q (hp i) (hloc i)

omit DX DS in
/-- Invertibility of the original higher exchange can be checked on any
jointly surjective étale family on its target, using the actual cartesian
restriction squares and the original composite exchange maps. -/
theorem higherBaseChangeMap_isIso_of_etale_cover
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)
    (hloc : ∀ i, IsIso ((higherBaseChangeMap f (p i) ((U i).hom ≫ g)
      (k i ≫ g') (hc i) q).app F)) :
    IsIso ((higherBaseChangeMap f f' g g' h q).app F) :=
  higherExchangeTest_isIso f f' g g' h F q
    (higherExchangeTest_of_etale_cover f f' g g' h U hU Y p k hp hc F q fun i =>
      higherExchangeTest_of_isIso f (p i) ((U i).hom ≫ g) (k i ≫ g') (hc i) F q (hloc i))

end EtaleLocality

end AlgebraicGeometry.Scheme.EtaleCohomology
