/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.DirectImage
public import Aglib.CategoryTheory.Sites.Torsion.ZMod.Cohomology
public import Aglib.CategoryTheory.Sites.Torsion.ZMod.Full
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantImageMates
public import Aglib.CategoryTheory.Adjunction.UnderlyingMate
public import Aglib.CategoryTheory.Adjunction.UnderlyingHomEquiv
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves

/-! # Genuine constant-module images for proper base-change reduction

The module images are the native site pullback and pushforward with genuine
ZMod-valued sheaves as coefficients. Exactness of the native module inverse
image gives preservation of injectives by the genuine module direct image.
The displayed underlying comparison is the original abelian direct image.
No claim about injectivity after scalar forgetting is made.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper.Reduction

universe u

attribute [local instance] hasSheafifyLarge TorsionZMod.hasSheafifyStandard

/-- The actual standard-value category of genuine ZMod-valued etale sheaves. -/
abbrev ZModSheaf (X : Scheme.{u}) (n : ℕ) :=
  Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod n))

/-- The original underlying abelian sheaf functor of genuine module coefficients. -/
abbrev zmodUnderlying (X : Scheme.{u}) (n : ℕ) :
    ZModSheaf X n ⥤ AbelianSheaf.{u, u + 1} X :=
  sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} (ZMod n)) AddCommGrpCat.{u + 1})

/-- The native site direct image with genuine ZMod-module coefficients. -/
abbrev zmodDirectImage {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ) :
    ZModSheaf X n ⥤ ZModSheaf S n :=
  (siteBaseChange f).sheafPushforwardContinuous (ModuleCat.{u + 1} (ZMod n))
    S.smallEtaleTopology X.smallEtaleTopology

/-- The native site inverse image with genuine ZMod-module coefficients. -/
abbrev zmodInverseImage {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ) :
    ZModSheaf S n ⥤ ZModSheaf X n :=
  (siteBaseChange f).sheafPullback (ModuleCat.{u + 1} (ZMod n))
    S.smallEtaleTopology X.smallEtaleTopology

/-- The actual native module inverse-image/direct-image adjunction. -/
def zmodImageAdjunction {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ) :
    zmodInverseImage f n ⊣ zmodDirectImage f n :=
  (siteBaseChange f).sheafAdjunctionContinuous (ModuleCat.{u + 1} (ZMod n))
    S.smallEtaleTopology X.smallEtaleTopology

/-- Flat presheaf inverse image is exact also for genuine module coefficients;
its comparison with the original abelian Kan extension is the native one. -/
theorem zmodPresheafLan_preservesFiniteLimits {X S : Scheme.{u}}
    (f : X ⟶ S) (n : ℕ) :
    PreservesFiniteLimits
      ((siteBaseChange f).op.lan :
        (S.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} (ZMod n)) ⥤
          X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} (ZMod n)) := by
  let G : S.Etale ⥤ X.Etale := siteBaseChange f
  let : RepresentablyFlat G := flat_of_preservesFiniteLimits G
  exact ModuleCat.Sheaf.presheafLan_preservesFiniteLimits.{u + 1, u, 0}
    (C := S.Etale) (D := X.Etale) (ZMod n) G

/-- The actual inverse image of genuine ZMod coefficients preserves finite limits. -/
instance zmodInverseImage_preservesFiniteLimits {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ) :
    PreservesFiniteLimits (zmodInverseImage f n) := by
  have := zmodPresheafLan_preservesFiniteLimits f n
  have := flat_of_preservesFiniteLimits (siteBaseChange f)
  exact Functor.sheafPullbackConstruction.preservesFiniteLimits
    (siteBaseChange f) (ModuleCat.{u + 1} (ZMod n))
    S.smallEtaleTopology X.smallEtaleTopology

/-- The genuine module direct image preserves genuine module injectives,
using exact inverse image and the original native adjunction. -/
theorem zmodDirectImage_preservesInjectiveObjects {X S : Scheme.{u}}
    (f : X ⟶ S) (n : ℕ) :
    (zmodDirectImage f n).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (zmodImageAdjunction f n)

/-- Every additive map between genuine ZMod modules is canonically linear. -/
theorem zmodForget_full (n : ℕ) :
    (forget₂ (ModuleCat.{u + 1} (ZMod n)) AddCommGrpCat.{u + 1}).Full :=
  TorsionZMod.moduleUnderlying_full.{u + 1} n

/-- Forgetting genuine ZMod scalars on the actual etale site is full. -/
theorem zmodUnderlying_full (X : Scheme.{u}) (n : ℕ) : (zmodUnderlying X n).Full :=
  TorsionZMod.sheafUnderlying_full.{u + 1, u, u + 1} X.smallEtaleTopology n

/-- The genuine module direct image has exactly the original underlying
abelian direct image, with identical pointwise restriction and coefficient maps. -/
def zmodDirectImageUnderlyingIso {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ) :
    zmodDirectImage f n ⋙ zmodUnderlying S n ≅
      zmodUnderlying X n ⋙ directImage f :=
  Iso.refl _

/-- The original native pullback commutes with the original scalar forgetting.
The ring remains the unchanged small ring, independently of the sheaf-value world. -/
def zmodInverseImageUnderlyingIso {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ) :
    zmodInverseImage f n ⋙ zmodUnderlying X n ≅
      zmodUnderlying S n ⋙ inverseImage f :=
  ModuleCat.Sheaf.pullbackUnderlyingIso.{u + 1, u, 0}
    (C := S.Etale) (D := X.Etale) (ZMod n) (siteBaseChange f)
    S.smallEtaleTopology X.smallEtaleTopology

/-- The comparison preserves the actual native units and original right comparison. -/
theorem zmodInverseImageUnderlyingIso_unit {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ)
    (M : ZModSheaf S n) :
    (zmodUnderlying S n).map ((zmodImageAdjunction f n).unit.app M) ≫
        (zmodDirectImageUnderlyingIso f n).hom.app ((zmodInverseImage f n).obj M) ≫
        (directImage f).map ((zmodInverseImageUnderlyingIso f n).hom.app M) =
      (inverseImageAdjunction f).unit.app ((zmodUnderlying S n).obj M) := by
  let U := zmodUnderlying S n
  let N := (zmodInverseImage f n).obj M
  let B := U.obj ((zmodDirectImage f n).obj N)
  let C := (directImage f).obj ((inverseImage f).obj (U.obj M))
  let g : B ⟶ C :=
    (directImage f).map ((zmodInverseImageUnderlyingIso f n).hom.app M)
  let u : U.obj M ⟶ B := U.map ((zmodImageAdjunction f n).unit.app M)
  have hi : (zmodDirectImageUnderlyingIso f n).hom.app N ≫ g = g := by
    change (𝟙 B) ≫ g = g
    exact Category.id_comp g
  have hu : u ≫ g = (inverseImageAdjunction f).unit.app (U.obj M) :=
    ModuleCat.Sheaf.pullbackUnderlyingIso_unit.{u + 1, u, 0}
      (C := S.Etale) (D := X.Etale) (ZMod n) (siteBaseChange f)
      S.smallEtaleTopology X.smallEtaleTopology M
  exact (congrArg (fun k : B ⟶ C => u ≫ k) hi).trans hu

/-- The inverse left comparison has exactly the original right underlying map as mate. -/
theorem mate_zmodInverseImageUnderlyingIso_inv {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ) :
    (mateEquiv (zmodImageAdjunction f n) (inverseImageAdjunction f)
      (TwoSquare.mk _ _ _ _ (zmodInverseImageUnderlyingIso f n).inv)).natTrans =
        (zmodDirectImageUnderlyingIso f n).hom :=
  mateEquiv_inv_natTrans_eq_of_unit (zmodImageAdjunction f n) (inverseImageAdjunction f)
    (zmodInverseImageUnderlyingIso f n) (zmodDirectImageUnderlyingIso f n).hom
    (zmodInverseImageUnderlyingIso_unit f n)

/-- The genuine module adjunct has the original underlying abelian adjunct value. -/
theorem zmodImageAdjunction_underlying_homEquiv {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ)
    (I : ZModSheaf S n) (J : ZModSheaf X n) (j : (zmodInverseImage f n).obj I ⟶ J) :
    (zmodUnderlying S n).map ((zmodImageAdjunction f n).homEquiv I J j) ≫
        (zmodDirectImageUnderlyingIso f n).hom.app J =
      (inverseImageAdjunction f).homEquiv _ _
        ((zmodInverseImageUnderlyingIso f n).inv.app I ≫ (zmodUnderlying X n).map j) := by
  exact underlying_homEquiv_of_mate
    (U := zmodUnderlying S n) (V := zmodUnderlying X n)
    (zmodImageAdjunction f n) (inverseImageAdjunction f)
    (TwoSquare.mk _ _ _ _ (zmodInverseImageUnderlyingIso f n).inv)
    (zmodDirectImageUnderlyingIso f n).hom (mate_zmodInverseImageUnderlyingIso_inv f n) I J j

/-- Full scalar forgetting recovers the same module adjunct by the original preimage formula. -/
theorem zmodImageAdjunction_homEquiv_eq_preimage {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ)
    (I : ZModSheaf S n) (J : ZModSheaf X n) (j : (zmodInverseImage f n).obj I ⟶ J) :
    let _ : (zmodUnderlying S n).Full := zmodUnderlying_full S n
    (zmodImageAdjunction f n).homEquiv I J j =
      (zmodUnderlying S n).preimage
        ((inverseImageAdjunction f).homEquiv _ _
            ((zmodInverseImageUnderlyingIso f n).inv.app I ≫ (zmodUnderlying X n).map j) ≫
          (zmodDirectImageUnderlyingIso f n).inv.app J) := by
  let : (zmodUnderlying S n).Full := zmodUnderlying_full S n
  exact homEquiv_eq_preimage_of_underlying_mate
    (U := zmodUnderlying S n) (V := zmodUnderlying X n)
    (zmodImageAdjunction f n) (inverseImageAdjunction f)
    (TwoSquare.mk _ _ _ _ (zmodInverseImageUnderlyingIso f n).inv)
    (zmodDirectImageUnderlyingIso f n) (mate_zmodInverseImageUnderlyingIso_inv f n) I J j

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper.Reduction
