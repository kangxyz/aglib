/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.FieldDirectImageCohomology

/-! Original field section values and the original homogeneous normalization. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u wS wX wE

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

section UnitValues

variable (Ω : Type u) [Field Ω] (Λ : Type (u + 1)) [CommRing Λ]

/-- The actual field unit evaluation carries postcomposition to the actual section map. -/
theorem moduleFieldUnitSectionsEquiv_comp
    {M N : ModuleSheaf (Spec (.of Ω)) Λ}
    (s : moduleUnit (Spec (.of Ω)) Λ ⟶ M) (f : M ⟶ N) :
    moduleFieldUnitSectionsEquiv Ω Λ N (s ≫ f) =
      (moduleGlobalSections (Spec (.of Ω)) Λ).map f (moduleFieldUnitSectionsEquiv Ω Λ M s) := by
  unfold moduleFieldUnitSectionsEquiv
  simp only [Equiv.trans_apply, Iso.homCongr_apply, Iso.symm_inv, Iso.refl_hom, Category.comp_id]
  let e := (moduleUnitConstantIso (Spec (.of Ω)) Λ).hom
  let adj := moduleGlobalSectionsAdjunction (Spec (.of Ω)) Λ
  change (adj.homEquiv (ModuleCat.of Λ Λ) N (e ≫ (s ≫ f))).hom 1 =
    ((moduleGlobalSections (Spec (.of Ω)) Λ).map f).hom
      ((adj.homEquiv (ModuleCat.of Λ Λ) M (e ≫ s)).hom 1)
  rw [← Category.assoc, adj.homEquiv_naturality_right]
  rfl

/-- The identity is the original constant generator, evaluated by the original unit. -/
theorem moduleFieldUnitSectionsEquiv_id :
    moduleFieldUnitSectionsEquiv Ω Λ (moduleUnit (Spec (.of Ω)) Λ) (𝟙 _) =
      (moduleGlobalSections (Spec (.of Ω)) Λ).map
        (moduleUnitConstantIso (Spec (.of Ω)) Λ).hom
        ((moduleGlobalSectionsAdjunction (Spec (.of Ω)) Λ).unit.app
          (ModuleCat.of Λ Λ) (1 : Λ)) := by
  unfold moduleFieldUnitSectionsEquiv
  simp only [Equiv.trans_apply, Iso.homCongr_apply, Iso.symm_inv, Iso.refl_hom, Category.comp_id]
  rw [Adjunction.homEquiv_unit]
  rfl

end UnitValues

variable (Ω : Type u) [Field Ω] [IsSepClosed Ω] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of Ω)) (n : ℕ)
  [HasDerivedCategory.{wS} (ModuleSheaf (Spec (.of Ω)) (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory.{wX} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wE} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The original field section evaluates the given map from the original homogeneous image. -/
theorem moduleFieldDirectImageHomology_map_value
    (M : ModuleSheaf X (ULift.{u + 1} (ZMod n))) (q : ℕ)
    (x : Ext.{wE} (moduleUnit X (ULift.{u + 1} (ZMod n))) M q) :
    let Λ := ULift.{u + 1} (ZMod n)
    let S := Spec (.of Ω)
    let C := ModuleSheaf X Λ
    let D := ModuleSheaf S Λ
    let I := moduleUnit S Λ
    let I₀ := (DerivedCategory.Plus.singleFunctor D 0).obj I
    let M₀ := (DerivedCategory.Plus.singleFunctor C 0).obj M
    let K := (moduleDerivedDirectImage Λ f).obj M₀
    let F := moduleInverseImage f Λ
    let u := ((F.rightDerivedFunctorPlusSingleIso 0).app I) ≪≫
      (DerivedCategory.Plus.singleFunctor C 0).mapIso (moduleUnitInverseImageIso f n)
    let t := ((DerivedCategory.Plus.singleFunctors D).shiftIso (-(q : ℤ)) (q : ℤ) 0
      (by omega)).app I
    let z := (moduleDerivedAdjunction Λ f).shiftedHomEquiv (q : ℤ) I₀ M₀ (u.hom ≫ x.homPlus)
    let j := t.inv ≫
      ((shiftEquiv' (DerivedCategory.Plus D) (-(q : ℤ)) (q : ℤ)
        (by omega)).toAdjunction.homEquiv I₀ K).symm z
    ∀ {N : D} (a : (DerivedCategory.Plus.homologyFunctor D (q : ℤ)).obj K ⟶ N),
      (moduleGlobalSections S Λ).map a
          (moduleFieldDirectImageHomologyAddEquiv Ω f n M q x) =
        moduleFieldUnitSectionsEquiv Ω Λ N
          ((DerivedCategory.singleFunctorCompHomologyFunctorIso D (q : ℤ)).inv.app I ≫
            (DerivedCategory.Plus.homologyFunctor D (q : ℤ)).map j ≫ a) := by
  dsimp only
  intro N a
  have h := moduleFieldDirectImageHomologyAddEquiv_hom_value Ω f n M q x
  dsimp only at h
  rw [moduleFieldDerivedUnitHomologyAddEquiv_symm_apply] at h
  let E := moduleFieldDerivedUnitHomologyEquiv Ω (ULift.{u + 1} (ZMod n)) (q : ℤ)
    ((moduleDerivedDirectImage (ULift.{u + 1} (ZMod n)) f).obj
      ((DerivedCategory.Plus.singleFunctor (ModuleSheaf X (ULift.{u + 1} (ZMod n))) 0).obj M))
  have he := (congrArg E h).symm
  rw [E.apply_symm_apply] at he
  dsimp only [E] at he
  rw [moduleFieldDerivedUnitHomologyEquiv_apply] at he
  unfold moduleFieldDerivedUnitHomologyMap at he
  dsimp only at he
  erw [← Category.assoc, moduleFieldUnitSectionsEquiv_comp, he]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A normalized actual field section value is the exact homogeneous trace input. -/
theorem moduleFieldDirectImageHomology_normalized_of_value
    (M : ModuleSheaf X (ULift.{u + 1} (ZMod n))) (q : ℕ)
    (x : Ext.{wE} (moduleUnit X (ULift.{u + 1} (ZMod n))) M q) :
    let Λ := ULift.{u + 1} (ZMod n)
    let S := Spec (.of Ω)
    let C := ModuleSheaf X Λ
    let D := ModuleSheaf S Λ
    let I := moduleUnit S Λ
    let I₀ := (DerivedCategory.Plus.singleFunctor D 0).obj I
    let M₀ := (DerivedCategory.Plus.singleFunctor C 0).obj M
    let K := (moduleDerivedDirectImage Λ f).obj M₀
    let F := moduleInverseImage f Λ
    let u := ((F.rightDerivedFunctorPlusSingleIso 0).app I) ≪≫
      (DerivedCategory.Plus.singleFunctor C 0).mapIso (moduleUnitInverseImageIso f n)
    let t := ((DerivedCategory.Plus.singleFunctors D).shiftIso (-(q : ℤ)) (q : ℤ) 0
      (by omega)).app I
    let z := (moduleDerivedAdjunction Λ f).shiftedHomEquiv (q : ℤ) I₀ M₀ (u.hom ≫ x.homPlus)
    let j := t.inv ≫
      ((shiftEquiv' (DerivedCategory.Plus D) (-(q : ℤ)) (q : ℤ)
        (by omega)).toAdjunction.homEquiv I₀ K).symm z
    ∀ a : (DerivedCategory.Plus.homologyFunctor D (q : ℤ)).obj K ⟶ I,
      (moduleGlobalSections S Λ).map a
          (moduleFieldDirectImageHomologyAddEquiv Ω f n M q x) =
        moduleFieldUnitSectionsEquiv Ω Λ I (𝟙 I) →
      (DerivedCategory.singleFunctorCompHomologyFunctorIso D (q : ℤ)).inv.app I ≫
        (DerivedCategory.Plus.homologyFunctor D (q : ℤ)).map j ≫ a = 𝟙 I := by
  dsimp only
  intro a ha
  apply (moduleFieldUnitSectionsEquiv Ω (ULift.{u + 1} (ZMod n)) _).injective
  exact (moduleFieldDirectImageHomology_map_value Ω f n M q x a).symm.trans ha

section Scalar

variable (k : Type u) [Field k] (n : ℕ) [NeZero n] (a : ZMod n)

set_option hygiene false in
local notation "Λ" => ULift.{u + 1} (ZMod n)
set_option hygiene false in
local notation "S" => Spec (.of k)
set_option hygiene false in
local notation "I" => moduleUnit S Λ

/-- The original field unit section of a scalar is the original multiple of
the identity, under the original unit evaluation. -/
theorem moduleFieldUnitSectionsEquiv_nsmul_id :
    let Γ := moduleGlobalSections S Λ
    let A := ModuleCat.of Λ Λ
    let η := (moduleGlobalSectionsAdjunction S Λ).unit.app A
    moduleFieldUnitSectionsEquiv k Λ I (a.val • 𝟙 I) =
      Γ.map (moduleUnitConstantIso S Λ).hom (η (ULift.up a)) := by
  intro Γ A η
  let E := moduleFieldUnitSectionsEquiv k Λ I
  let f : I ⟶ I := a.val • 𝟙 I
  let u := (moduleUnitConstantIso S Λ).hom
  let j : A ⟶ Γ.obj I := η ≫ Γ.map u
  have h₀ : E f = Γ.map f (E (𝟙 I)) := by
    rw [← Category.id_comp f]
    exact moduleFieldUnitSectionsEquiv_comp k Λ (𝟙 I) f
  have h₁ : E (𝟙 I) = j (1 : Λ) := moduleFieldUnitSectionsEquiv_id k Λ
  have h₂ : Γ.map f = a.val • 𝟙 (Γ.obj I) := by
    change Γ.map (a.val • 𝟙 I) = _
    rw [Γ.map_nsmul, Γ.map_id]
  have h₃ : a.val • (1 : Λ) = ULift.up a := by
    apply ULift.ext
    change a.val • (1 : ZMod n) = a
    exact (nsmul_one _).trans (ZMod.natCast_zmod_val a)
  calc
    _ = Γ.map f (j (1 : Λ)) := h₀.trans (congrArg (Γ.map f) h₁)
    _ = a.val • j (1 : Λ) := by
      rw [h₂]
      rfl
    _ = j (a.val • (1 : Λ)) := (map_nsmul j.hom a.val (1 : Λ)).symm
    _ = j (ULift.up a) := congrArg j h₃

end Scalar

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
