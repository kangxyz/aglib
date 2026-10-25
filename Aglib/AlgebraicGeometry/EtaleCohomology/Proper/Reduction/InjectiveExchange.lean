/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Reduction.ZModDerivedImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Reduction.ZModRetract

/-! # Original exchange reductions on genuine injective module tests

Composition uses preservation of genuine module injectives by genuine direct
image. Descent uses the constructed genuine coefficient retract along the
surjection and the native acyclic-single comparison. Both arguments apply to
the published canonical derived mate and its published higher-image maps.
They do not assert injectivity after scalar forgetting or assume base change
for the morphism being deduced. Properness and cartesianness are needed by
applications supplying the two adjacent hypotheses, not by these formal steps.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper.Reduction

section TypedTests

variable {M N C D E E' : Type*}
  [Category* M] [Category* N] [Category* C] [Category* D] [Category* E] [Category* E']
  (V : M ⥤ N) (a : M ⥤ C) (b : N ⥤ D) (R : C ⥤ D)
  {U W : D ⥤ E} (β : U ⟶ W)
  {L L' : C ⥤ E'} (γ : L ⟶ L') {T T' : C ⥤ E} (δ : T ⟶ T')

private theorem injectiveTest_comp [V.PreservesInjectiveObjects]
    (e : ∀ (J : M) [Injective J], R.obj (a.obj J) ≅ b.obj (V.obj J))
    (hpaste : ∀ K : C, IsIso (β.app (R.obj K)) → IsIso (γ.app K) → IsIso (δ.app K))
    (hOuter : ∀ (I : N) [Injective I], IsIso (β.app (b.obj I)))
    (hInner : ∀ (J : M) [Injective J], IsIso (γ.app (a.obj J)))
    (J : M) [Injective J] : IsIso (δ.app (a.obj J)) := by
  have : Injective (V.obj J) := inferInstance
  have hR : IsIso (β.app (R.obj (a.obj J))) :=
    (NatTrans.isIso_app_iff_of_iso β (e J)).mpr (hOuter (V.obj J))
  exact hpaste (a.obj J) hR (hInner J)

private theorem injectiveTest_descent
    (e : ∀ (J : M) [Injective J], R.obj (a.obj J) ≅ b.obj (V.obj J))
    (rtest : ∀ (I : N) [Injective I],
      ∃ J : M, Injective J ∧ Nonempty (Retract I (V.obj J)))
    (hcancel : ∀ K : C, IsIso (γ.app K) → IsIso (δ.app K) → IsIso (β.app (R.obj K)))
    (hInner : ∀ (J : M) [Injective J], IsIso (γ.app (a.obj J)))
    (hComposite : ∀ (J : M) [Injective J], IsIso (δ.app (a.obj J)))
    (I : N) [Injective I] : IsIso (β.app (b.obj I)) := by
  obtain ⟨J, hJ, ⟨r⟩⟩ := rtest I
  have : Injective J := hJ
  have hR : IsIso (β.app (R.obj (a.obj J))) :=
    hcancel (a.obj J) (hInner J) (hComposite J)
  let t : Retract (b.obj I) (R.obj (a.obj J)) :=
    (r.map b).trans (Retract.ofIso (e J).symm)
  exact MorphismProperty.of_retract (P := MorphismProperty.isomorphisms E)
    (β.retractArrowApp t) hR

end TypedTests

universe u dS dX dY dS' dX' dY'

attribute [local instance] hasSheafifyLarge TorsionZMod.hasSheafifyStandard

section Single

variable (X : Scheme.{u}) [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]

/-- The literal original underlying-coefficient functor followed by the
original degree-zero single. Its regular head is shared by the reduction
constructors and their acyclic-image comparison. -/
def zmodSingle (n : ℕ) :
    ZModSheaf X n ⥤ DerivedCategory.Plus (AbelianSheaf.{u, u + 1} X) :=
  zmodUnderlying X n ⋙ DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0

/-- The coefficient object is exactly the original underlying module single. -/
theorem zmodSingle_obj (n : ℕ) (I : ZModSheaf X n) :
    (zmodSingle X n).obj I =
      (DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj
        ((zmodUnderlying X n).obj I) := rfl

/-- The coefficient arrow is exactly the original underlying map on singles. -/
theorem zmodSingle_map (n : ℕ) {I J : ZModSheaf X n} (a : I ⟶ J) :
    (zmodSingle X n).map a =
      (DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).map
        ((zmodUnderlying X n).map a) := rfl

end Single

/-- At the shared original-single heads, use the same native acyclic-single
isomorphism, constructed from the original right-derived unit. -/
def zmodInjectiveImageSingleIso {Y X : Scheme.{u}}
    [HasDerivedCategory.{dY} (AbelianSheaf.{u, u + 1} Y)]
    [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
    (k : Y ⟶ X) (n : ℕ) (I : ZModSheaf Y n) [Injective I] :
    (derivedDirectImage k).obj ((zmodSingle Y n).obj I) ≅
      (zmodSingle X n).obj ((zmodDirectImage k n).obj I) :=
  derivedDirectImageZModInjectiveSingleIso k n I

variable {S X Y S' X' Y' : Scheme.{u}}
  [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dY} (AbelianSheaf.{u, u + 1} Y)]
  [HasDerivedCategory.{dS'} (AbelianSheaf.{u, u + 1} S')]
  [HasDerivedCategory.{dX'} (AbelianSheaf.{u, u + 1} X')]
  [HasDerivedCategory.{dY'} (AbelianSheaf.{u, u + 1} Y')]
  (f : X ⟶ S) (k : Y ⟶ X) (f' : X' ⟶ S') (k' : Y' ⟶ X')
  (g : S' ⟶ S) (g' : X' ⟶ X) (g'' : Y' ⟶ Y)
  (h₁ : f' ≫ g = g' ≫ f) (h₂ : k' ≫ g' = g'' ≫ k)
  (h : (k' ≫ f') ≫ g = g'' ≫ (k ≫ f)) (n : ℕ)

/-- Adjacent original exchange tests on genuine module injectives give the
original composite exchange test, using the actual direct-image injective. -/
theorem derivedExchange_on_zmodInjectives_comp
    (hOuter : ∀ (I : ZModSheaf X n) [Injective I],
      IsIso ((derivedBaseChangeMap f f' g g' h₁).app
        ((zmodSingle X n).obj I)))
    (hInner : ∀ (J : ZModSheaf Y n) [Injective J],
      IsIso ((derivedBaseChangeMap k k' g' g'' h₂).app
        ((zmodSingle Y n).obj J)))
    (J : ZModSheaf Y n) [Injective J] :
    IsIso ((derivedBaseChangeMap (k ≫ f) (k' ≫ f') g g'' h).app
      ((zmodSingle Y n).obj J)) := by
  have : (zmodDirectImage k n).PreservesInjectiveObjects :=
    zmodDirectImage_preservesInjectiveObjects k n
  exact injectiveTest_comp (zmodDirectImage k n)
    (zmodSingle Y n) (zmodSingle X n)
    (derivedDirectImage k) (derivedBaseChangeMap f f' g g' h₁)
    (derivedBaseChangeMap k k' g' g'' h₂)
    (derivedBaseChangeMap (k ≫ f) (k' ≫ f') g g'' h)
    (fun I _ => zmodInjectiveImageSingleIso k n I)
    (fun K hK hL => by
      have := hK
      have := hL
      exact derivedBaseChangeMap_isIso_vComp f k f' k' g g' g'' h₁ h₂ h K)
    hOuter hInner J

/-- Source and composite original exchange tests descend along the actual
surjection to the outer original exchange on every genuine module injective. -/
theorem derivedExchange_on_zmodInjectives_descent [Surjective k]
    (hInner : ∀ (J : ZModSheaf Y n) [Injective J],
      IsIso ((derivedBaseChangeMap k k' g' g'' h₂).app
        ((zmodSingle Y n).obj J)))
    (hComposite : ∀ (J : ZModSheaf Y n) [Injective J],
      IsIso ((derivedBaseChangeMap (k ≫ f) (k' ≫ f') g g'' h).app
        ((zmodSingle Y n).obj J)))
    (I : ZModSheaf X n) [Injective I] :
    IsIso ((derivedBaseChangeMap f f' g g' h₁).app
      ((zmodSingle X n).obj I)) := by
  exact injectiveTest_descent (zmodDirectImage k n)
    (zmodSingle Y n) (zmodSingle X n)
    (derivedDirectImage k) (derivedBaseChangeMap f f' g g' h₁)
    (derivedBaseChangeMap k k' g' g'' h₂)
    (derivedBaseChangeMap (k ≫ f) (k' ≫ f') g g'' h)
    (fun J _ => zmodInjectiveImageSingleIso k n J)
    (fun J _ => exists_zmodInjective_directImage_retract k n J)
    (fun K hK hL => by
      have := hK
      have := hL
      exact derivedBaseChangeMap_isIso_of_vComp f k f' k' g g' g'' h₁ h₂ h K)
    hInner hComposite I

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper.Reduction
