/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Monoidal.GrpObjShear
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# The whole family of translations of a group object

An isomorphism of `A ⊗ B` preserving the second projection pulls back along
any parameter map `T ⟶ B`, using the original cartesian products. Applying
this constructor to the inverse of the existing `GrpObj.shearIso` gives
right translation `(g,t) ↦ (g * f(t),t)` by a variable parameter.

The projection, inverse, unit, composition and base-map naturality laws hold
before any scheme or point evaluation. The Jacobian incidence construction
and the existing Picard translation family's second-component convention
consume this same isomorphism.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe v u

namespace CategoryTheory.CartesianMonoidalCategory

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {A B T : C}

-- Cone maps and cartesian tensor projections have their native definitionally equal forms.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original cartesian tensor product supplies the base change of a
map along a first projection, with no separate product object chosen. -/
theorem isPullback_tensorHom_fst_with_id (i : A ⟶ B) (T : C) :
    IsPullback (fst A T) (i ⊗ₘ 𝟙 T) i (fst B T) where
  w := by simp
  isLimit' := ⟨PullbackCone.isLimitAux' _ (fun s => by
    refine ⟨lift s.fst (s.snd ≫ snd B T), ?_, ?_, ?_⟩
    · simp
    · ext1 <;> simp [PullbackCone.condition]
    · intro m h₁ h₂
      dsimp at m h₁ h₂ ⊢
      apply hom_ext
      · simpa using h₁
      · simpa using congrArg (fun q => q ≫ snd B T) h₂)⟩

/-- Pull back an actual shear preserving the second projection along an
arbitrary parameter map, without choosing another product realization. -/
def baseChangeShear (e : A ⊗ B ≅ A ⊗ B)
    (he : e.hom ≫ snd A B = snd A B) (f : T ⟶ B) : A ⊗ T ≅ A ⊗ T := by
  let r := 𝟙 A ⊗ₘ f
  let a := lift (r ≫ e.hom ≫ fst A B) (snd A T)
  let b := lift (r ≫ e.inv ≫ fst A B) (snd A T)
  have hei : e.inv ≫ snd A B = snd A B := by
    calc
      e.inv ≫ snd A B = e.inv ≫ e.hom ≫ snd A B := by rw [he]
      _ = snd A B := e.inv_hom_id_assoc _
  have ha : a ≫ r = r ≫ e.hom := by
    apply hom_ext
    · simp [a, r]
    · simp [a, r, he]
  have hb : b ≫ r = r ≫ e.inv := by
    apply hom_ext
    · simp [b, r]
    · simp [b, r, hei]
  refine ⟨a, b, ?_, ?_⟩
  · apply hom_ext
    · rw [Category.assoc]
      simp only [b, lift_fst, Category.id_comp]
      rw [← Category.assoc a r, ha, Category.assoc, e.hom_inv_id_assoc]
      simp [r]
    · simp [a, b]
  · apply hom_ext
    · rw [Category.assoc]
      simp only [a, lift_fst, Category.id_comp]
      rw [← Category.assoc b r, hb, Category.assoc, e.inv_hom_id_assoc]
      simp [r]
    · simp [a, b]

@[reassoc (attr := simp)]
theorem baseChangeShear_hom_fst (e : A ⊗ B ≅ A ⊗ B)
    (he : e.hom ≫ snd A B = snd A B) (f : T ⟶ B) :
    (baseChangeShear e he f).hom ≫ fst A T = (𝟙 A ⊗ₘ f) ≫ e.hom ≫ fst A B :=
  lift_fst _ _

@[reassoc (attr := simp)]
theorem baseChangeShear_hom_snd (e : A ⊗ B ≅ A ⊗ B)
    (he : e.hom ≫ snd A B = snd A B) (f : T ⟶ B) :
    (baseChangeShear e he f).hom ≫ snd A T = snd A T := lift_snd _ _

@[reassoc (attr := simp)]
theorem baseChangeShear_inv_fst (e : A ⊗ B ≅ A ⊗ B)
    (he : e.hom ≫ snd A B = snd A B) (f : T ⟶ B) :
    (baseChangeShear e he f).inv ≫ fst A T = (𝟙 A ⊗ₘ f) ≫ e.inv ≫ fst A B :=
  lift_fst _ _

@[reassoc (attr := simp)]
theorem baseChangeShear_inv_snd (e : A ⊗ B ≅ A ⊗ B)
    (he : e.hom ≫ snd A B = snd A B) (f : T ⟶ B) :
    (baseChangeShear e he f).inv ≫ snd A T = snd A T := lift_snd _ _

end CategoryTheory.CartesianMonoidalCategory

namespace CategoryTheory.GrpObj

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  (G : C) [GrpObj G] {T T' : C}

/-- Right translation by an arbitrary parameter, obtained from the existing
group shear through the same cartesian base-change constructor. -/
def translationFamily (f : T ⟶ G) : G ⊗ T ≅ G ⊗ T :=
  baseChangeShear (shearIso G).symm (by simp [shearIso]) f

@[reassoc (attr := simp)]
theorem translationFamily_hom_fst (f : T ⟶ G) :
    (translationFamily G f).hom ≫ fst G T = fst G T * (snd G T ≫ f) := by
  simp [translationFamily, shearIso, MonObj.comp_mul]

@[reassoc (attr := simp)]
theorem translationFamily_hom_snd (f : T ⟶ G) :
    (translationFamily G f).hom ≫ snd G T = snd G T := by
  simp [translationFamily]

@[reassoc (attr := simp)]
theorem translationFamily_inv_fst (f : T ⟶ G) :
    (translationFamily G f).inv ≫ fst G T = fst G T / (snd G T ≫ f) := by
  simp [translationFamily, shearIso, GrpObj.comp_div]

@[reassoc (attr := simp)]
theorem translationFamily_inv_snd (f : T ⟶ G) :
    (translationFamily G f).inv ≫ snd G T = snd G T := by
  simp [translationFamily]

/-- The inverse is the same family evaluated at the inverse parameter. -/
theorem translationFamily_symm (f : T ⟶ G) :
    (translationFamily G f).symm = translationFamily G f⁻¹ := by
  apply Iso.ext
  ext1 <;> simp [GrpObj.comp_inv, div_eq_mul_inv]

/-- The unit parameter gives the original identity automorphism. -/
@[simp]
theorem translationFamily_one : translationFamily G (1 : T ⟶ G) = Iso.refl (G ⊗ T) := by
  apply Iso.ext
  ext1 <;> simp [MonObj.comp_one]

/-- Composition is parameter multiplication, with the order dictated by
right translation and categorical composition. -/
theorem translationFamily_mul (f g : T ⟶ G) :
    translationFamily G (f * g) = translationFamily G f ≪≫ translationFamily G g := by
  apply Iso.ext
  ext1 <;> simp [MonObj.comp_mul, Category.assoc, mul_assoc]

/-- Base-map naturality of the whole translation isomorphism, retaining the
original product map on both sides. -/
@[reassoc]
theorem translationFamily_naturality (a : T' ⟶ T) (f : T ⟶ G) :
    (𝟙 G ⊗ₘ a) ≫ (translationFamily G f).hom =
      (translationFamily G (a ≫ f)).hom ≫ (𝟙 G ⊗ₘ a) := by
  ext1 <;> simp [MonObj.comp_mul, Category.assoc]

/-- The inverse family obeys the same base-map naturality law. -/
@[reassoc]
theorem translationFamily_inv_naturality (a : T' ⟶ T) (f : T ⟶ G) :
    (𝟙 G ⊗ₘ a) ≫ (translationFamily G f).inv =
      (translationFamily G (a ≫ f)).inv ≫ (𝟙 G ⊗ₘ a) := by
  ext1 <;> simp [GrpObj.comp_div, Category.assoc]

/-- Translating an actual product inclusion is the pullback along the
inverse-translation first coordinate. This is the whole incidence square,
before any scheme specialization. -/
theorem isPullback_translationFamily {Z : C} (i : Z ⟶ G) (f : T ⟶ G) :
    IsPullback (fst Z T) ((i ⊗ₘ 𝟙 T) ≫ (translationFamily G f).hom)
      i ((translationFamily G f).inv ≫ fst G T) := by
  exact (isPullback_tensorHom_fst_with_id i T).of_iso
    (Iso.refl _) (Iso.refl _) (translationFamily G f) (Iso.refl _)
    (by simp) (by simp) (by simp)
    (by simpa only [Iso.refl_hom, Category.comp_id] using
      ((translationFamily G f).hom_inv_id_assoc (fst G T)).symm)

end CategoryTheory.GrpObj
