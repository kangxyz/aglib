/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.Tensor.Monoidal.Basic
public import Aglib.AlgebraicGeometry.Modules.Tensor.Monoidal.Associator

/-!
# The monoidal category of scheme modules

The class `presheafLocalIso X` of module-presheaf maps inverted by module sheafification is
monoidal (`presheafLocalIso_isMonoidal`). Hence `X.Modules` is a monoidal category, with no
hypothesis on `X`, whose data are the existing tensor maps:

* `M ⊗ N` is `tensorSheaf X M N` and `f ⊗ₘ g`, `M ◁ g`, `f ▷ N` are `tensorSheafMap`;
* the unit is the structure module, `λ_` is `tensorSheafLeftUnit` and `ρ_` is
  `tensorRightUnitIso`;
* `α_` is the general `tensorSheafAssociator`.

The generic chosen coherence construction is specialized here. It transports the equations by
`CategoryTheory.Monoidal.induced` along the identity functor
`toLocalizedMonoidal X : X.Modules ⥤ LocalizedMonoidal L W ε`, where `L` is module
sheafification and `W = presheafLocalIso X`; Mathlib's localized monoidal structure serves only
as the coherence source. Each data field agrees definitionally with its existing name
(`tensorObj_eq_tensorSheaf` and the following lemmas), and
`moduleTensorLeftFunctor X M = tensorLeft M`. The structure is preadditive
(`monoidalPreadditive`), from the additivity of the left and right tensor functors.
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
  SheafOfModulesOfCommRing.associatedSheafTensorUnitIso X.sheaf

local notation "ε₀" => associatedSheafTensorUnitIso X

section Construction

/-- The existing tensor data of scheme modules, with the general associator. -/
@[instance_reducible]
def tensorMonoidalCategoryStruct : MonoidalCategoryStruct X.Modules :=
  SheafOfModulesOfCommRing.tensorMonoidalCategoryStruct X.sheaf

/-- The identity of scheme modules, into Mathlib's localized monoidal category of module
presheaves at the local isomorphisms. -/
def toLocalizedMonoidal : X.Modules ⥤ LocalizedMonoidal (𝓛) (presheafLocalIso X) (ε₀) :=
  SheafOfModulesOfCommRing.toLocalizedMonoidal X.sheaf

instance : (toLocalizedMonoidal X).Faithful := inferInstanceAs (𝟭 X.Modules).Faithful

local notation "L'" => toMonoidalCategory (𝓛) (presheafLocalIso X) (ε₀)

attribute [local instance] tensorMonoidalCategoryStruct

/-- The sheafification counit at a module sheaf, as an isomorphism of the localized
category. -/
def toLocalizedMonoidalCounitIso (M : X.Modules) :
    (L').obj ((𝓖).obj M) ≅ (toLocalizedMonoidal X).obj M :=
  SheafOfModulesOfCommRing.toLocalizedMonoidalCounitIso X.sheaf M

/-- The comparison of the localized tensor with the existing tensor: the localized `μ` at the
underlying presheaves, transported along the sheafification counits. -/
def toLocalizedMonoidalμIso (M N : X.Modules) :
    (toLocalizedMonoidal X).obj M ⊗ (toLocalizedMonoidal X).obj N ≅
      (toLocalizedMonoidal X).obj (M ⊗ N) :=
  SheafOfModulesOfCommRing.toLocalizedMonoidalμIso X.sheaf M N

/-- Naturality of the sheafification counit, in the localized category. -/
theorem map_toPresheaf_comp_counitIso_hom {M N : X.Modules} (g : M ⟶ N) :
    (L').map ((𝓖).map g) ≫ (toLocalizedMonoidalCounitIso X N).hom =
      (toLocalizedMonoidalCounitIso X M).hom ≫ (toLocalizedMonoidal X).map g :=
  SheafOfModulesOfCommRing.map_toPresheaf_comp_counitIso_hom X.sheaf g

theorem toLocalizedMonoidal_map_tensorHom {M₁ M₂ N₁ N₂ : X.Modules} (f : M₁ ⟶ N₁)
    (g : M₂ ⟶ N₂) :
    (toLocalizedMonoidal X).map (f ⊗ₘ g) = (toLocalizedMonoidalμIso X M₁ M₂).inv ≫
      ((toLocalizedMonoidal X).map f ⊗ₘ (toLocalizedMonoidal X).map g) ≫
        (toLocalizedMonoidalμIso X N₁ N₂).hom :=
  SheafOfModulesOfCommRing.toLocalizedMonoidal_map_tensorHom X.sheaf f g

theorem toLocalizedMonoidal_map_whiskerLeft (M : X.Modules) {N N' : X.Modules} (g : N ⟶ N') :
    (toLocalizedMonoidal X).map (M ◁ g) = (toLocalizedMonoidalμIso X M N).inv ≫
      ((toLocalizedMonoidal X).obj M ◁ (toLocalizedMonoidal X).map g) ≫
        (toLocalizedMonoidalμIso X M N').hom := by
  exact SheafOfModulesOfCommRing.toLocalizedMonoidal_map_whiskerLeft X.sheaf M g

theorem toLocalizedMonoidal_map_whiskerRight {M M' : X.Modules} (f : M ⟶ M') (N : X.Modules) :
    (toLocalizedMonoidal X).map (f ▷ N) = (toLocalizedMonoidalμIso X M N).inv ≫
      ((toLocalizedMonoidal X).map f ▷ (toLocalizedMonoidal X).obj N) ≫
        (toLocalizedMonoidalμIso X M' N).hom := by
  exact SheafOfModulesOfCommRing.toLocalizedMonoidal_map_whiskerRight X.sheaf f N

theorem toLocalizedMonoidal_map_leftUnitor (M : X.Modules) :
    (toLocalizedMonoidal X).map (λ_ M).hom =
      (((toLocalizedMonoidalμIso X (𝟙_ X.Modules) M).symm ≪≫
        ((Iso.refl _).symm ⊗ᵢ .refl _)) ≪≫ λ_ ((toLocalizedMonoidal X).obj M)).hom :=
  SheafOfModulesOfCommRing.toLocalizedMonoidal_map_leftUnitor X.sheaf M

theorem toLocalizedMonoidal_map_rightUnitor (M : X.Modules) :
    (toLocalizedMonoidal X).map (ρ_ M).hom =
      (((toLocalizedMonoidalμIso X M (𝟙_ X.Modules)).symm ≪≫
        (.refl _ ⊗ᵢ (Iso.refl _).symm)) ≪≫ ρ_ ((toLocalizedMonoidal X).obj M)).hom :=
  SheafOfModulesOfCommRing.toLocalizedMonoidal_map_rightUnitor X.sheaf M

theorem toLocalizedMonoidal_map_associator (M N O : X.Modules) :
    (toLocalizedMonoidal X).map (α_ M N O).hom =
      (((toLocalizedMonoidalμIso X _ _).symm ≪≫ ((toLocalizedMonoidalμIso X _ _).symm ⊗ᵢ .refl _))
        ≪≫ α_ ((toLocalizedMonoidal X).obj M) ((toLocalizedMonoidal X).obj N)
          ((toLocalizedMonoidal X).obj O)
        ≪≫ ((.refl _ ⊗ᵢ toLocalizedMonoidalμIso X _ _) ≪≫ toLocalizedMonoidalμIso X _ _)).hom := by
  exact SheafOfModulesOfCommRing.toLocalizedMonoidal_map_associator X.sheaf M N O

/-- The inducing data of the monoidal structure: the existing tensor maps are carried to the
localized ones by the identity functor, through `toLocalizedMonoidalμIso`. -/
def toLocalizedMonoidalInducingData :
    Monoidal.InducingFunctorData (toLocalizedMonoidal X) :=
  SheafOfModulesOfCommRing.toLocalizedMonoidalInducingData X.sheaf

/-- Scheme modules form a monoidal category under the existing tensor maps. -/
instance monoidalCategory : MonoidalCategory X.Modules :=
  SheafOfModulesOfCommRing.monoidalCategory X.sheaf

/-- The identity into the localized monoidal category is a monoidal functor, with tensor
comparison `toLocalizedMonoidalμIso` and identity unit comparison. -/
instance instMonoidalToLocalizedMonoidal : (toLocalizedMonoidal X).Monoidal :=
  SheafOfModulesOfCommRing.instMonoidalToLocalizedMonoidal X.sheaf

end Construction

/-- The original Scheme structure uses the actual generic chosen tensor data. -/
theorem tensorMonoidalCategoryStruct_eq_generic :
    tensorMonoidalCategoryStruct X =
      SheafOfModulesOfCommRing.tensorMonoidalCategoryStruct X.sheaf := rfl

/-- The original Scheme monoidal category is the actual generic chosen construction. -/
theorem monoidalCategory_eq_generic :
    monoidalCategory X = SheafOfModulesOfCommRing.monoidalCategory X.sheaf := rfl

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

/-- The monoidal structure of scheme modules is preadditive: whiskering is additive, since the
left and right tensor functors are additive. -/
instance monoidalPreadditive : MonoidalPreadditive X.Modules :=
  SheafOfModulesOfCommRing.monoidalPreadditive X.sheaf

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
