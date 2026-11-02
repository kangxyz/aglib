/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.Tensor.RightUnit
public import Aglib.Algebra.Category.ModuleCat.Sheaf.TensorAdditive
public import Aglib.Algebra.Category.ModuleCat.Sheaf.Tensor.Monoidal.Associator
public import Aglib.CategoryTheory.Localization.Monoidal.Induced
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Monoidal.Transport

/-! # Chosen monoidal coherence of the original ringed-site tensor

The tensor, structure-module unit, associator and unitors are the original
sheafified pointwise maps. The faithful identity into Mathlib's localized
monoidal category proves their coherence through `Monoidal.induced`.
Tensor stability of the actual localization class is an explicit hypothesis.
Site object and morphism universes are independent; the module carrier is
still the ring carrier universe `uR`. No closed structure is assumed.
-/

@[expose] public section

noncomputable section

universe uC vC uR

open CategoryTheory MonoidalCategory Localization.Monoidal

namespace SheafOfModulesOfCommRing

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{uR} RingCat.{uR})]
  (R : Sheaf J CommRingCat.{uR}) [HasSheafify J AddCommGrpCat.{uR}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{uR}]
  [(presheafLocalIso R).IsMonoidal]

local notation "𝓛" => SheafOfModulesOfCommRing.associatedSheaf R
local notation "𝓖" => SheafOfModulesOfCommRing.toPresheaf R
local notation "η" => SheafOfModulesOfCommRing.associatedSheafUnit R

/-- The sheafified presheaf tensor unit is the structure module, through the sheafification
counit; typed on the commutative-ring spelling of module sheaves. -/
def associatedSheafTensorUnitIso :
    (𝓛).obj (𝟙_ (PresheafOfModulesOfCommRing.{uR} R.obj)) ≅
      SheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat.{uR} RingCat.{uR})).obj
          R) :=
  sheafifyForgetIso R (SheafOfModules.unit
    ((sheafCompose J (forget₂ CommRingCat.{uR} RingCat.{uR})).obj R))

local notation "ε₀" => associatedSheafTensorUnitIso R

/-- The original first-variable tensor functor with its second argument fixed. -/
abbrev tensorRightFunctor (M : SheafOfModulesOfCommRing R) :
    SheafOfModulesOfCommRing R ⥤ SheafOfModulesOfCommRing R :=
  tensorFunctor R ⋙ (evaluation _ _).obj M

section Construction

/-- The existing tensor data of ringed-site module sheaves, with the general associator. -/
@[instance_reducible]
def tensorMonoidalCategoryStruct : MonoidalCategoryStruct (SheafOfModulesOfCommRing R) where
  tensorObj M N := tensorProduct R M N
  whiskerLeft M _ _ g := tensorMap R (𝟙 M) g
  whiskerRight f N := tensorMap R f (𝟙 N)
  tensorHom f g := tensorMap R f g
  tensorUnit := SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{uR} RingCat.{uR})).obj R)
  associator M N O := tensorAssociator R M N O
  leftUnitor M := (tensorLeftUnitIso R).app M
  rightUnitor M := (SheafOfModulesOfCommRing.tensorRightUnitIso R).app M

/-- The identity of the original module sheaves, into the localized monoidal category
of module presheaves at the actual local isomorphisms. -/
def toLocalizedMonoidal :
    SheafOfModulesOfCommRing R ⥤ LocalizedMonoidal (𝓛) (presheafLocalIso R) (ε₀) :=
  𝟭 (SheafOfModulesOfCommRing R)

instance : (toLocalizedMonoidal R).Faithful :=
  inferInstanceAs (𝟭 (SheafOfModulesOfCommRing R)).Faithful

local notation "L'" => toMonoidalCategory (𝓛) (presheafLocalIso R) (ε₀)

attribute [local instance] tensorMonoidalCategoryStruct

/-- The sheafification counit at a module sheaf, as an isomorphism of the localized
category. -/
def toLocalizedMonoidalCounitIso (M : SheafOfModulesOfCommRing R) :
    (L').obj ((𝓖).obj M) ≅ (toLocalizedMonoidal R).obj M :=
  sheafifyForgetIso R M

/-- The comparison of the localized tensor with the existing tensor: the localized `μ` at the
underlying presheaves, transported along the sheafification counits. -/
def toLocalizedMonoidalμIso (M N : SheafOfModulesOfCommRing R) :
    (toLocalizedMonoidal R).obj M ⊗ (toLocalizedMonoidal R).obj N ≅
      (toLocalizedMonoidal R).obj (M ⊗ N) :=
  μOf (𝓛) (presheafLocalIso R) (ε₀) (toLocalizedMonoidalCounitIso R M)
    (toLocalizedMonoidalCounitIso R N)

/-- Naturality of the sheafification counit, in the localized category. -/
theorem map_toPresheaf_comp_counitIso_hom {M N : SheafOfModulesOfCommRing R} (g : M ⟶ N) :
    (L').map ((𝓖).map g) ≫ (toLocalizedMonoidalCounitIso R N).hom =
      (toLocalizedMonoidalCounitIso R M).hom ≫ (toLocalizedMonoidal R).map g :=
  (PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat.{uR} RingCat.{uR})).obj R)
    (𝟙 _)).counit.naturality g

theorem toLocalizedMonoidal_map_tensorHom {M₁ M₂ N₁ N₂ : SheafOfModulesOfCommRing R} (f : M₁ ⟶ N₁)
    (g : M₂ ⟶ N₂) :
    (toLocalizedMonoidal R).map (f ⊗ₘ g) = (toLocalizedMonoidalμIso R M₁ M₂).inv ≫
      ((toLocalizedMonoidal R).map f ⊗ₘ (toLocalizedMonoidal R).map g) ≫
        (toLocalizedMonoidalμIso R N₁ N₂).hom :=
  map_tensorHom_eq _ _ _ _ (map_toPresheaf_comp_counitIso_hom R f)
    (map_toPresheaf_comp_counitIso_hom R g)

theorem toLocalizedMonoidal_map_whiskerLeft (M : SheafOfModulesOfCommRing R)
    {N N' : SheafOfModulesOfCommRing R} (g : N ⟶ N') :
    (toLocalizedMonoidal R).map (M ◁ g) = (toLocalizedMonoidalμIso R M N).inv ≫
      ((toLocalizedMonoidal R).obj M ◁ (toLocalizedMonoidal R).map g) ≫
        (toLocalizedMonoidalμIso R M N').hom := by
  have h := toLocalizedMonoidal_map_tensorHom R (𝟙 M) g
  rw [CategoryTheory.Functor.map_id, MonoidalCategory.id_tensorHom] at h
  exact h

theorem toLocalizedMonoidal_map_whiskerRight {M M' : SheafOfModulesOfCommRing R}
    (f : M ⟶ M') (N : SheafOfModulesOfCommRing R) :
    (toLocalizedMonoidal R).map (f ▷ N) = (toLocalizedMonoidalμIso R M N).inv ≫
      ((toLocalizedMonoidal R).map f ▷ (toLocalizedMonoidal R).obj N) ≫
        (toLocalizedMonoidalμIso R M' N).hom := by
  have h := toLocalizedMonoidal_map_tensorHom R f (𝟙 N)
  rw [CategoryTheory.Functor.map_id, MonoidalCategory.tensorHom_id] at h
  exact h

theorem toLocalizedMonoidal_map_leftUnitor (M : SheafOfModulesOfCommRing R) :
    (toLocalizedMonoidal R).map (λ_ M).hom =
      (((toLocalizedMonoidalμIso R (𝟙_ (SheafOfModulesOfCommRing R)) M).symm ≪≫
        ((Iso.refl _).symm ⊗ᵢ .refl _)) ≪≫ λ_ ((toLocalizedMonoidal R).obj M)).hom :=
  map_leftUnitor_hom_comp (toLocalizedMonoidalCounitIso R M)

theorem toLocalizedMonoidal_map_rightUnitor (M : SheafOfModulesOfCommRing R) :
    (toLocalizedMonoidal R).map (ρ_ M).hom =
      (((toLocalizedMonoidalμIso R M (𝟙_ (SheafOfModulesOfCommRing R))).symm ≪≫
        (.refl _ ⊗ᵢ (Iso.refl _).symm)) ≪≫ ρ_ ((toLocalizedMonoidal R).obj M)).hom :=
  map_rightUnitor_hom_comp (toLocalizedMonoidalCounitIso R M)

theorem toLocalizedMonoidal_map_associator (M N O : SheafOfModulesOfCommRing R) :
    (toLocalizedMonoidal R).map (α_ M N O).hom =
      (((toLocalizedMonoidalμIso R _ _).symm ≪≫ ((toLocalizedMonoidalμIso R _ _).symm ⊗ᵢ .refl _))
        ≪≫ α_ ((toLocalizedMonoidal R).obj M) ((toLocalizedMonoidal R).obj N)
          ((toLocalizedMonoidal R).obj O)
        ≪≫ ((.refl _ ⊗ᵢ toLocalizedMonoidalμIso R _ _) ≪≫ toLocalizedMonoidalμIso R _ _)).hom := by
  have h₁ := map_unit_whiskerRight_comp_tensorAssociator_hom R M N O
  have h₂ := map_whiskerRight_comp_associator_eq (L := 𝓛) (W := presheafLocalIso R) (ε := ε₀)
    (toLocalizedMonoidalCounitIso R M) (toLocalizedMonoidalCounitIso R N)
    (toLocalizedMonoidalCounitIso R O)
    ((η).app ((𝓖).obj M ⊗ (𝓖).obj N)) ((η).app ((𝓖).obj N ⊗ (𝓖).obj O))
    (toLocalizedMonoidalCounitIso R (M ⊗ N)) (toLocalizedMonoidalCounitIso R (N ⊗ O))
    ((PresheafOfModules.sheafificationAdjunction
      (R := (sheafCompose J (forget₂ CommRingCat.{uR} RingCat.{uR})).obj R)
      (𝟙 _)).left_triangle_components _)
    ((PresheafOfModules.sheafificationAdjunction
      (R := (sheafCompose J (forget₂ CommRingCat.{uR} RingCat.{uR})).obj R)
      (𝟙 _)).left_triangle_components _)
  have : IsIso ((L').map ((η).app ((𝓖).obj M ⊗ (𝓖).obj N) ▷ (𝓖).obj O)) :=
    isIso_associatedSheaf_map_unit_whiskerRight R _ _
  exact (cancel_epi ((L').map ((η).app ((𝓖).obj M ⊗ (𝓖).obj N) ▷ (𝓖).obj O))).1
    (h₁.trans h₂.symm)

/-- The inducing data of the monoidal structure: the existing tensor maps are carried to the
localized ones by the identity functor, through `toLocalizedMonoidalμIso`. -/
def toLocalizedMonoidalInducingData :
    Monoidal.InducingFunctorData (toLocalizedMonoidal R) where
  μIso := toLocalizedMonoidalμIso R
  whiskerLeft_eq := toLocalizedMonoidal_map_whiskerLeft R
  whiskerRight_eq := toLocalizedMonoidal_map_whiskerRight R
  tensorHom_eq := toLocalizedMonoidal_map_tensorHom R
  εIso := Iso.refl _
  associator_eq := toLocalizedMonoidal_map_associator R
  leftUnitor_eq := toLocalizedMonoidal_map_leftUnitor R
  rightUnitor_eq := toLocalizedMonoidal_map_rightUnitor R

/-- Ringed-site module sheaves form a monoidal category under the existing tensor maps. -/
instance monoidalCategory : MonoidalCategory (SheafOfModulesOfCommRing R) :=
  Monoidal.induced (toLocalizedMonoidal R) (toLocalizedMonoidalInducingData R)

/-- The identity into the localized monoidal category is a monoidal functor, with tensor
comparison `toLocalizedMonoidalμIso` and identity unit comparison. -/
instance instMonoidalToLocalizedMonoidal : (toLocalizedMonoidal R).Monoidal :=
  Monoidal.fromInducedMonoidal (toLocalizedMonoidal R) (toLocalizedMonoidalInducingData R)

end Construction

theorem toLocalizedMonoidal_μ (M N : SheafOfModulesOfCommRing R) :
    Functor.LaxMonoidal.μ (toLocalizedMonoidal R) M N = (toLocalizedMonoidalμIso R M N).hom :=
  rfl

/-! ### The data fields are the existing tensor maps -/

theorem tensorObj_eq_tensorProduct (M N : SheafOfModulesOfCommRing R) :
    M ⊗ N = tensorProduct R M N := rfl

theorem tensorHom_eq_tensorMap {M M' N N' : SheafOfModulesOfCommRing R} (f : M ⟶ M') (g : N ⟶ N') :
    f ⊗ₘ g = tensorMap R f g := rfl

theorem whiskerLeft_eq_tensorMap (M : SheafOfModulesOfCommRing R)
    {N N' : SheafOfModulesOfCommRing R} (g : N ⟶ N') :
    M ◁ g = tensorMap R (𝟙 M) g := rfl

theorem whiskerRight_eq_tensorMap {M M' : SheafOfModulesOfCommRing R}
    (f : M ⟶ M') (N : SheafOfModulesOfCommRing R) :
    f ▷ N = tensorMap R f (𝟙 N) := rfl

theorem tensorUnit_eq_unit :
    𝟙_ (SheafOfModulesOfCommRing R) =
      SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{uR} RingCat.{uR})).obj R) := rfl

theorem leftUnitor_eq_tensorLeftUnitIso (M : SheafOfModulesOfCommRing R) :
    λ_ M = (tensorLeftUnitIso R).app M :=
  rfl

theorem rightUnitor_eq_tensorRightUnitIso (M : SheafOfModulesOfCommRing R) :
    ρ_ M = (SheafOfModulesOfCommRing.tensorRightUnitIso R).app M := rfl

theorem associator_eq_tensorAssociator (M N O : SheafOfModulesOfCommRing R) :
    α_ M N O = tensorAssociator R M N O := rfl

/-- The existing left tensor functor is the monoidal left tensor functor. -/
theorem tensorLeftFunctor_eq_tensorLeft (M : SheafOfModulesOfCommRing R) :
    tensorLeftFunctor R M = tensorLeft M := rfl

/-- The existing right tensor functor is the monoidal right tensor functor. -/
theorem tensorRightFunctor_eq_tensorRight (M : SheafOfModulesOfCommRing R) :
    tensorRightFunctor R M = tensorRight M := rfl

/-- The components of the existing coefficient map are right whiskerings. -/
theorem tensorFunctor_map_app_eq_whiskerRight {M N : SheafOfModulesOfCommRing R} (f : M ⟶ N)
    (P : SheafOfModulesOfCommRing R) : ((tensorFunctor R).map f).app P = f ▷ P := rfl

/-- The chosen monoidal structure is preadditive because the original left and right
tensor functors are additive. -/
instance monoidalPreadditive : MonoidalPreadditive (SheafOfModulesOfCommRing R) where
  whiskerLeft_zero := (tensorLeftFunctor R _).map_zero _ _
  zero_whiskerRight := (tensorRightFunctor R _).map_zero _ _
  whiskerLeft_add _ _ := (tensorLeftFunctor R _).map_add
  add_whiskerRight _ _ := (tensorRightFunctor R _).map_add

/-- The associator on nested pure section tensors. -/
theorem associator_hom_tmul (M N O : SheafOfModulesOfCommRing R) (U : Cᵒᵖ)
    (m : M.val.obj U) (n : N.val.obj U) (o : O.val.obj U) :
    (α_ M N O).hom.val.app U
        ((tensorUnitMap R (M ⊗ N : SheafOfModulesOfCommRing R) O).app U
          ((tensorUnitMap R M N).app U (m ⊗ₜ n) ⊗ₜ o)) =
      (tensorUnitMap R M (N ⊗ O : SheafOfModulesOfCommRing R)).app U
        (m ⊗ₜ (tensorUnitMap R N O).app U (n ⊗ₜ o)) :=
  tensorAssociator_hom_tmul R M N O U m n o

/-- The inverse associator on nested pure section tensors. -/
theorem associator_inv_tmul (M N O : SheafOfModulesOfCommRing R) (U : Cᵒᵖ)
    (m : M.val.obj U) (n : N.val.obj U) (o : O.val.obj U) :
    (α_ M N O).inv.val.app U
        ((tensorUnitMap R M (N ⊗ O : SheafOfModulesOfCommRing R)).app U
          (m ⊗ₜ (tensorUnitMap R N O).app U (n ⊗ₜ o))) =
      (tensorUnitMap R (M ⊗ N : SheafOfModulesOfCommRing R) O).app U
        ((tensorUnitMap R M N).app U (m ⊗ₜ n) ⊗ₜ o) :=
  tensorAssociator_inv_tmul R M N O U m n o

end SheafOfModulesOfCommRing
