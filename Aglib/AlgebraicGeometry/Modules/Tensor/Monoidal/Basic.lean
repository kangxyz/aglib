/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.Tensor.RightUnit
public import Aglib.AlgebraicGeometry.Modules.Tensor.Monoidal.Associator
public import Aglib.CategoryTheory.Localization.Monoidal.Induced
public import Mathlib.CategoryTheory.Monoidal.Transport

/-!
# The monoidal category of scheme modules

The class `presheafLocalIso X` of module-presheaf maps inverted by module sheafification is
monoidal (`presheafLocalIso_isMonoidal`). Hence `X.Modules` is a monoidal category, with no
hypothesis on `X`, whose data are the existing tensor maps:

* `M ⊗ N` is `tensorSheaf X M N` and `f ⊗ₘ g`, `M ◁ g`, `f ▷ N` are `tensorSheafMap`;
* the unit is the structure module, `λ_` is `tensorSheafLeftUnit` and `ρ_` is
  `tensorRightUnitIso`;
* `α_` is the general `tensorSheafAssociator`.

The coherence equations are transported by `CategoryTheory.Monoidal.induced` along the identity
functor `toLocalizedMonoidal X : X.Modules ⥤ LocalizedMonoidal L W ε`, where `L` is module
sheafification and `W = presheafLocalIso X`; Mathlib's localized monoidal structure serves only
as the coherence source. Each data field agrees definitionally with its existing name
(`tensorObj_eq_tensorSheaf` and the following lemmas), and
`moduleTensorLeftFunctor X M = tensorLeft M`.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory MonoidalCategory Localization.Monoidal

namespace AlgebraicGeometry.Scheme.Modules

variable (X : Scheme.{u})

local notation "𝓛" => SheafOfModulesOfCommRing.associatedSheaf X.sheaf
local notation "𝓖" => SheafOfModulesOfCommRing.toPresheaf X.sheaf
local notation "η" => SheafOfModulesOfCommRing.associatedSheafUnit X.sheaf

/-- The sheafified presheaf tensor unit is the structure module, through the sheafification
counit; typed on the commutative-ring spelling of module sheaves. -/
def associatedSheafTensorUnitIso :
    (𝓛).obj (𝟙_ (PresheafOfModulesOfCommRing.{u} X.sheaf.obj)) ≅
      SheafOfModules.unit
        ((sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).obj
          X.sheaf) :=
  sheafifyForgetIso X (SheafOfModules.unit X.ringCatSheaf)

local notation "ε₀" => associatedSheafTensorUnitIso X

section Construction

/-- The existing tensor data of scheme modules, with the general associator. -/
@[instance_reducible]
def tensorMonoidalCategoryStruct : MonoidalCategoryStruct X.Modules where
  tensorObj M N := tensorSheaf X M N
  whiskerLeft M _ _ g := tensorSheafMap X (𝟙 M) g
  whiskerRight f N := tensorSheafMap X f (𝟙 N)
  tensorHom f g := tensorSheafMap X f g
  tensorUnit := SheafOfModules.unit X.ringCatSheaf
  associator M N O := tensorSheafAssociator X M N O
  leftUnitor M := tensorSheafLeftUnit X M
  rightUnitor M := (SheafOfModulesOfCommRing.tensorRightUnitIso X.sheaf).app M

/-- The identity of scheme modules, into Mathlib's localized monoidal category of module
presheaves at the local isomorphisms. -/
def toLocalizedMonoidal : X.Modules ⥤ LocalizedMonoidal (𝓛) (presheafLocalIso X) (ε₀) :=
  𝟭 X.Modules

instance : (toLocalizedMonoidal X).Faithful := inferInstanceAs (𝟭 X.Modules).Faithful

local notation "L'" => toMonoidalCategory (𝓛) (presheafLocalIso X) (ε₀)

attribute [local instance] tensorMonoidalCategoryStruct

/-- The sheafification counit at a module sheaf, as an isomorphism of the localized
category. -/
def toLocalizedMonoidalCounitIso (M : X.Modules) :
    (L').obj ((𝓖).obj M) ≅ (toLocalizedMonoidal X).obj M :=
  sheafifyForgetIso X M

/-- The comparison of the localized tensor with the existing tensor: the localized `μ` at the
underlying presheaves, transported along the sheafification counits. -/
def toLocalizedMonoidalμIso (M N : X.Modules) :
    (toLocalizedMonoidal X).obj M ⊗ (toLocalizedMonoidal X).obj N ≅
      (toLocalizedMonoidal X).obj (M ⊗ N) :=
  μOf (𝓛) (presheafLocalIso X) (ε₀) (toLocalizedMonoidalCounitIso X M)
    (toLocalizedMonoidalCounitIso X N)

/-- Naturality of the sheafification counit, in the localized category. -/
theorem map_toPresheaf_comp_counitIso_hom {M N : X.Modules} (g : M ⟶ N) :
    (L').map ((𝓖).map g) ≫ (toLocalizedMonoidalCounitIso X N).hom =
      (toLocalizedMonoidalCounitIso X M).hom ≫ (toLocalizedMonoidal X).map g :=
  (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit.naturality g

theorem toLocalizedMonoidal_map_tensorHom {M₁ M₂ N₁ N₂ : X.Modules} (f : M₁ ⟶ N₁)
    (g : M₂ ⟶ N₂) :
    (toLocalizedMonoidal X).map (f ⊗ₘ g) = (toLocalizedMonoidalμIso X M₁ M₂).inv ≫
      ((toLocalizedMonoidal X).map f ⊗ₘ (toLocalizedMonoidal X).map g) ≫
        (toLocalizedMonoidalμIso X N₁ N₂).hom :=
  map_tensorHom_eq _ _ _ _ (map_toPresheaf_comp_counitIso_hom X f)
    (map_toPresheaf_comp_counitIso_hom X g)

theorem toLocalizedMonoidal_map_whiskerLeft (M : X.Modules) {N N' : X.Modules} (g : N ⟶ N') :
    (toLocalizedMonoidal X).map (M ◁ g) = (toLocalizedMonoidalμIso X M N).inv ≫
      ((toLocalizedMonoidal X).obj M ◁ (toLocalizedMonoidal X).map g) ≫
        (toLocalizedMonoidalμIso X M N').hom := by
  have h := toLocalizedMonoidal_map_tensorHom X (𝟙 M) g
  rw [CategoryTheory.Functor.map_id, MonoidalCategory.id_tensorHom] at h
  exact h

theorem toLocalizedMonoidal_map_whiskerRight {M M' : X.Modules} (f : M ⟶ M') (N : X.Modules) :
    (toLocalizedMonoidal X).map (f ▷ N) = (toLocalizedMonoidalμIso X M N).inv ≫
      ((toLocalizedMonoidal X).map f ▷ (toLocalizedMonoidal X).obj N) ≫
        (toLocalizedMonoidalμIso X M' N).hom := by
  have h := toLocalizedMonoidal_map_tensorHom X f (𝟙 N)
  rw [CategoryTheory.Functor.map_id, MonoidalCategory.tensorHom_id] at h
  exact h

theorem toLocalizedMonoidal_map_leftUnitor (M : X.Modules) :
    (toLocalizedMonoidal X).map (λ_ M).hom =
      (((toLocalizedMonoidalμIso X (𝟙_ X.Modules) M).symm ≪≫
        ((Iso.refl _).symm ⊗ᵢ .refl _)) ≪≫ λ_ ((toLocalizedMonoidal X).obj M)).hom :=
  map_leftUnitor_hom_comp (toLocalizedMonoidalCounitIso X M)

theorem toLocalizedMonoidal_map_rightUnitor (M : X.Modules) :
    (toLocalizedMonoidal X).map (ρ_ M).hom =
      (((toLocalizedMonoidalμIso X M (𝟙_ X.Modules)).symm ≪≫
        (.refl _ ⊗ᵢ (Iso.refl _).symm)) ≪≫ ρ_ ((toLocalizedMonoidal X).obj M)).hom :=
  map_rightUnitor_hom_comp (toLocalizedMonoidalCounitIso X M)

theorem toLocalizedMonoidal_map_associator (M N O : X.Modules) :
    (toLocalizedMonoidal X).map (α_ M N O).hom =
      (((toLocalizedMonoidalμIso X _ _).symm ≪≫ ((toLocalizedMonoidalμIso X _ _).symm ⊗ᵢ .refl _))
        ≪≫ α_ ((toLocalizedMonoidal X).obj M) ((toLocalizedMonoidal X).obj N)
          ((toLocalizedMonoidal X).obj O)
        ≪≫ ((.refl _ ⊗ᵢ toLocalizedMonoidalμIso X _ _) ≪≫ toLocalizedMonoidalμIso X _ _)).hom := by
  have h₁ := map_unit_whiskerRight_comp_tensorSheafAssociator_hom X M N O
  have h₂ := map_whiskerRight_comp_associator_eq (L := 𝓛) (W := presheafLocalIso X) (ε := ε₀)
    (toLocalizedMonoidalCounitIso X M) (toLocalizedMonoidalCounitIso X N)
    (toLocalizedMonoidalCounitIso X O)
    ((η).app ((𝓖).obj M ⊗ (𝓖).obj N)) ((η).app ((𝓖).obj N ⊗ (𝓖).obj O))
    (toLocalizedMonoidalCounitIso X (M ⊗ N)) (toLocalizedMonoidalCounitIso X (N ⊗ O))
    ((_root_.PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).left_triangle_components _)
    ((_root_.PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).left_triangle_components _)
  have : IsIso ((L').map ((η).app ((𝓖).obj M ⊗ (𝓖).obj N) ▷ (𝓖).obj O)) :=
    isIso_associatedSheaf_map_unit_whiskerRight X _ _
  exact (cancel_epi ((L').map ((η).app ((𝓖).obj M ⊗ (𝓖).obj N) ▷ (𝓖).obj O))).1
    (h₁.trans h₂.symm)

/-- The inducing data of the monoidal structure: the existing tensor maps are carried to the
localized ones by the identity functor, through `toLocalizedMonoidalμIso`. -/
def toLocalizedMonoidalInducingData :
    Monoidal.InducingFunctorData (toLocalizedMonoidal X) where
  μIso := toLocalizedMonoidalμIso X
  whiskerLeft_eq := toLocalizedMonoidal_map_whiskerLeft X
  whiskerRight_eq := toLocalizedMonoidal_map_whiskerRight X
  tensorHom_eq := toLocalizedMonoidal_map_tensorHom X
  εIso := Iso.refl _
  associator_eq := toLocalizedMonoidal_map_associator X
  leftUnitor_eq := toLocalizedMonoidal_map_leftUnitor X
  rightUnitor_eq := toLocalizedMonoidal_map_rightUnitor X

/-- Scheme modules form a monoidal category under the existing tensor maps. -/
instance monoidalCategory : MonoidalCategory X.Modules :=
  Monoidal.induced (toLocalizedMonoidal X) (toLocalizedMonoidalInducingData X)

/-- The identity into the localized monoidal category is a monoidal functor, with tensor
comparison `toLocalizedMonoidalμIso` and identity unit comparison. -/
instance instMonoidalToLocalizedMonoidal : (toLocalizedMonoidal X).Monoidal :=
  Monoidal.fromInducedMonoidal (toLocalizedMonoidal X) (toLocalizedMonoidalInducingData X)

end Construction

theorem toLocalizedMonoidal_μ (M N : X.Modules) :
    Functor.LaxMonoidal.μ (toLocalizedMonoidal X) M N = (toLocalizedMonoidalμIso X M N).hom :=
  rfl

/-! ### The data fields are the existing tensor maps -/

theorem tensorObj_eq_tensorSheaf (M N : X.Modules) : M ⊗ N = tensorSheaf X M N := rfl

theorem tensorHom_eq_tensorSheafMap {M M' N N' : X.Modules} (f : M ⟶ M') (g : N ⟶ N') :
    f ⊗ₘ g = tensorSheafMap X f g := rfl

theorem whiskerLeft_eq_tensorSheafMap (M : X.Modules) {N N' : X.Modules} (g : N ⟶ N') :
    M ◁ g = tensorSheafMap X (𝟙 M) g := rfl

theorem whiskerRight_eq_tensorSheafMap {M M' : X.Modules} (f : M ⟶ M') (N : X.Modules) :
    f ▷ N = tensorSheafMap X f (𝟙 N) := rfl

theorem tensorUnit_eq_unit : 𝟙_ X.Modules = SheafOfModules.unit X.ringCatSheaf := rfl

theorem leftUnitor_eq_tensorSheafLeftUnit (M : X.Modules) : λ_ M = tensorSheafLeftUnit X M :=
  rfl

theorem rightUnitor_eq_tensorRightUnitIso (M : X.Modules) :
    ρ_ M = (SheafOfModulesOfCommRing.tensorRightUnitIso X.sheaf).app M := rfl

theorem associator_eq_tensorSheafAssociator (M N O : X.Modules) :
    α_ M N O = tensorSheafAssociator X M N O := rfl

/-- The existing left tensor functor is the monoidal left tensor functor. -/
theorem moduleTensorLeftFunctor_eq_tensorLeft (M : X.Modules) :
    moduleTensorLeftFunctor X M = tensorLeft M := rfl

/-- The existing right tensor functor is the monoidal right tensor functor. -/
theorem moduleTensorRightFunctor_eq_tensorRight (M : X.Modules) :
    moduleTensorRightFunctor X M = tensorRight M := rfl

/-- The components of the existing coefficient map are right whiskerings. -/
theorem moduleTensorCoefficientMap_app_eq_whiskerRight {M N : X.Modules} (f : M ⟶ N)
    (P : X.Modules) : (moduleTensorCoefficientMap X f).app P = f ▷ P := rfl

/-- The associator on nested pure section tensors. -/
theorem associator_hom_tmul (M N O : X.Modules) (U : X.Opensᵒᵖ)
    (m : M.val.obj U) (n : N.val.obj U) (o : O.val.obj U) :
    (α_ M N O).hom.val.app U
        ((tensorSheafUnit X (M ⊗ N : X.Modules) O).app U
          ((tensorSheafUnit X M N).app U (m ⊗ₜ n) ⊗ₜ o)) =
      (tensorSheafUnit X M (N ⊗ O : X.Modules)).app U
        (m ⊗ₜ (tensorSheafUnit X N O).app U (n ⊗ₜ o)) :=
  tensorSheafAssociator_hom_tmul X M N O U m n o

/-- The inverse associator on nested pure section tensors. -/
theorem associator_inv_tmul (M N O : X.Modules) (U : X.Opensᵒᵖ)
    (m : M.val.obj U) (n : N.val.obj U) (o : O.val.obj U) :
    (α_ M N O).inv.val.app U
        ((tensorSheafUnit X M (N ⊗ O : X.Modules)).app U
          (m ⊗ₜ (tensorSheafUnit X N O).app U (n ⊗ₜ o))) =
      (tensorSheafUnit X (M ⊗ N : X.Modules) O).app U
        ((tensorSheafUnit X M N).app U (m ⊗ₜ n) ⊗ₜ o) :=
  tensorSheafAssociator_inv_tmul X M N O U m n o

end AlgebraicGeometry.Scheme.Modules
