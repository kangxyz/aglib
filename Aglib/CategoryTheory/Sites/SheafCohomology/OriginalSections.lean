/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.ExtRightDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Category.Grp.Preadditive

/-! # Original integer-source Hom and ordinary derived sections

The actual adjunction and evaluation at the original integer one identify Hom
from that integer source with the supplied section functor. Its ordinary
right-derived comparison retains the original supplied injective resolutions
and the independent Ext and value universes.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace CategoryTheory.Adjunction

universe u v s e

section Hom

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {K : AddCommGrpCat.{s} ⥤ C} {Γ : C ⥤ AddCommGrpCat.{s}}
  [K.Additive] (adj : K ⊣ Γ)

/-- Original integer-one evaluation after the actual additive adjunction.
The coefficient and morphism universes are independent at this element level. -/
def integerHomSectionsAddEquiv (Y : C) :
    (K.obj (AddCommGrpCat.of (ULift.{s} ℤ)) ⟶ Y) ≃+ Γ.obj Y :=
  (adj.homAddEquiv (AddCommGrpCat.of (ULift.{s} ℤ)) Y).trans
    (AddCommGrpCat.uliftZMultiplesAddEquiv (Γ.obj Y))

/-- The actual additive Hom equivalence is natural in the coefficient. -/
theorem integerHomSectionsAddEquiv_naturality {Y Z : C} (q : Y ⟶ Z)
    (a : K.obj (AddCommGrpCat.of (ULift.{s} ℤ)) ⟶ Y) :
    integerHomSectionsAddEquiv adj Z (a ≫ q) =
      Γ.map q (integerHomSectionsAddEquiv adj Y a) := by
  change AddCommGrpCat.uliftZMultiplesAddEquiv (Γ.obj Z)
      (adj.homEquiv _ Z (a ≫ q)) =
    Γ.map q (AddCommGrpCat.uliftZMultiplesAddEquiv (Γ.obj Y)
      (adj.homEquiv _ Y a))
  rw [Adjunction.homEquiv_naturality_right]
  rfl

end Hom

section HomFunctor

variable {C : Type u} [Category.{s} C] [Preadditive C]
  {K : AddCommGrpCat.{s} ⥤ C} {Γ : C ⥤ AddCommGrpCat.{s}}
  [K.Additive] (adj : K ⊣ Γ)

/-- The actual Hom functor and section functor have the same value category.
This uses the existing Hom-world realization, with no new lifted carrier. -/
def integerHomSectionsIso :
    preadditiveCoyoneda.obj (op (K.obj (AddCommGrpCat.of (ULift.{s} ℤ)))) ≅ Γ :=
  NatIso.ofComponents
    (fun Y => (integerHomSectionsAddEquiv adj Y).toAddCommGrpIso)
    (by
      intro Y Z q
      ext a
      exact integerHomSectionsAddEquiv_naturality adj q a)

end HomFunctor

section Derived

variable {C : Type u} [Category.{s} C] [Abelian C] [EnoughInjectives C]
  {K : AddCommGrpCat.{s} ⥤ C} {Γ : C ⥤ AddCommGrpCat.{s}}
  [K.Additive] [Γ.Additive] (adj : K ⊣ Γ)

/-- Derive the same original Hom/sections comparison, without a derived-category choice. -/
def integerHomRightDerivedSectionsIso (n : ℕ) :
    (preadditiveCoyoneda.obj (op (K.obj (AddCommGrpCat.of (ULift.{s} ℤ))))).rightDerived n ≅
      Γ.rightDerived n where
  hom := (integerHomSectionsIso adj).hom.rightDerived n
  inv := (integerHomSectionsIso adj).inv.rightDerived n
  hom_inv_id := by
    rw [← NatTrans.rightDerived_comp, Iso.hom_inv_id, NatTrans.rightDerived_id]
  inv_hom_id := by
    rw [← NatTrans.rightDerived_comp, Iso.inv_hom_id, NatTrans.rightDerived_id]

variable [HasExt.{e} C]

/-- The actual supplied-resolution Ext comparison followed by the original derived section Iso. -/
def originalSectionsExtEquivOfResolution {Y : C} (I : InjectiveResolution Y) (n : ℕ) :
    Abelian.Ext.{e} (K.obj (AddCommGrpCat.of (ULift.{s} ℤ))) Y n ≃+
      (Γ.rightDerived n).obj Y :=
  (I.extRightDerivedAddEquiv (K.obj (AddCommGrpCat.of (ULift.{s} ℤ))) n).trans
    ((integerHomRightDerivedSectionsIso adj n).app Y).addCommGroupIsoToAddEquiv

/-- The forward map retains the exact original resolution and comparison components. -/
theorem originalSectionsExtEquivOfResolution_apply {Y : C}
    (I : InjectiveResolution Y) (n : ℕ)
    (a : Abelian.Ext.{e} (K.obj (AddCommGrpCat.of (ULift.{s} ℤ))) Y n) :
    originalSectionsExtEquivOfResolution adj I n a =
      (integerHomRightDerivedSectionsIso adj n).hom.app Y
        (I.extRightDerivedAddEquiv (K.obj (AddCommGrpCat.of (ULift.{s} ℤ))) n a) := rfl

/-- Any supplied coefficient-resolution lift gives the original coefficient map. -/
theorem originalSectionsExtEquivOfResolution_naturality {Y Z : C}
    {I : InjectiveResolution Y} {J : InjectiveResolution Z} {q : Y ⟶ Z}
    (φ : InjectiveResolution.Hom I J q) (n : ℕ)
    (a : Abelian.Ext.{e} (K.obj (AddCommGrpCat.of (ULift.{s} ℤ))) Y n) :
    originalSectionsExtEquivOfResolution adj J n
        (a.comp (Abelian.Ext.mk₀ q) (add_zero n)) =
      (Γ.rightDerived n).map q (originalSectionsExtEquivOfResolution adj I n a) :=
  InjectiveResolution.extRightDerivedAddEquiv_trans_naturality
    (K.obj (AddCommGrpCat.of (ULift.{s} ℤ))) n
    (integerHomRightDerivedSectionsIso adj n) φ a

/-- Canonical ordinary sections comparison uses the existing native injective resolution. -/
def originalSectionsExtEquiv (Y : C) (n : ℕ) :
    Abelian.Ext.{e} (K.obj (AddCommGrpCat.of (ULift.{s} ℤ))) Y n ≃+
      (Γ.rightDerived n).obj Y :=
  originalSectionsExtEquivOfResolution adj (injectiveResolution Y) n

/-- The same actual comparison is independent of its supplied resolution. -/
theorem originalSectionsExtEquiv_eq_ofResolution {Y : C}
    (I : InjectiveResolution Y) (n : ℕ) :
    originalSectionsExtEquiv adj Y n = originalSectionsExtEquivOfResolution adj I n :=
  InjectiveResolution.extRightDerivedAddEquiv_trans_eq
    (K.obj (AddCommGrpCat.of (ULift.{s} ℤ))) n
    (integerHomRightDerivedSectionsIso adj n) (injectiveResolution Y) I

/-- Original coefficient naturality, through the actual canonical resolution lift. -/
theorem originalSectionsExtEquiv_naturality {Y Z : C} (q : Y ⟶ Z) (n : ℕ)
    (a : Abelian.Ext.{e} (K.obj (AddCommGrpCat.of (ULift.{s} ℤ))) Y n) :
    originalSectionsExtEquiv adj Z n (a.comp (Abelian.Ext.mk₀ q) (add_zero n)) =
      (Γ.rightDerived n).map q (originalSectionsExtEquiv adj Y n a) := by
  let φ : InjectiveResolution.Hom (injectiveResolution Y) (injectiveResolution Z) q :=
    ⟨InjectiveResolution.desc q _ _, by
      have h := InjectiveResolution.desc_commutes_zero q (injectiveResolution Z)
        (injectiveResolution Y)
      simp only [CochainComplex.single₀_map_f_zero] at h ⊢
      exact h⟩
  exact originalSectionsExtEquivOfResolution_naturality adj φ n a

end Derived

end CategoryTheory.Adjunction
