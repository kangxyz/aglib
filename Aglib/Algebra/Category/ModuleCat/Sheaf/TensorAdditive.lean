/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.Tensor.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
Source: `Quillen/Algebra/Category/ModuleCat/Sheaf/TensorAdditive.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general_prerequisite;
source ranges [[1, 86]]. Actual objects, maps and hypotheses are preserved.
-/

/-!
# Additivity of sheafified tensor

The original sheafified tensor is additive in each variable. Pointwise tensor
preserves coproducts, and exact module sheafification preserves finite products.
No monoidal coherence structure on module sheaves is asserted.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace SheafOfModulesOfCommRing

variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (R : Sheaf J CommRingCat.{u}) [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
attribute [local instance] Abelian.hasFiniteBiproducts

/-- The pinned presheaf left tensor is additive by its actual preserved coproducts. -/
local instance presheafTensorLeft_additive (M : PresheafOfModulesOfCommRing.{u} R.obj) :
    (tensorLeft M).Additive := by
  let : PreservesColimitsOfSize.{0, 0} (tensorLeft M) :=
    preservesSmallestColimits_of_preservesColimits _
  let : PreservesBinaryBiproducts (tensorLeft M) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- The pinned presheaf right tensor is additive by its actual preserved coproducts. -/
local instance presheafTensorRight_additive (M : PresheafOfModulesOfCommRing.{u} R.obj) :
    (tensorRight M).Additive := by
  let : PreservesColimitsOfSize.{0, 0} (tensorRight M) :=
    preservesSmallestColimits_of_preservesColimits _
  let : PreservesBinaryBiproducts (tensorRight M) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- Forgetting to the original module presheaf is additive. -/
instance toPresheaf_additive : (toPresheaf R).Additive where
  map_add := rfl

/-- Original module sheafification is additive. -/
instance associatedSheaf_additive : (associatedSheaf R).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Tensoring sheaves in the second variable is additive. -/
instance tensorLeftFunctor_additive (M : SheafOfModulesOfCommRing R) :
    (tensorLeftFunctor R M).Additive := by
  let : (tensorLeft ((toPresheaf R).obj M)).Additive :=
    presheafTensorLeft_additive R _
  change (toPresheaf R ⋙ tensorLeft ((toPresheaf R).obj M) ⋙ associatedSheaf R).Additive
  infer_instance

/-- Tensoring sheaves in the first variable is additive. -/
instance tensorFunctor_additive : (tensorFunctor R).Additive where
  map_add {M N} f g := by
    apply NatTrans.ext
    funext P
    let : (tensorRight ((toPresheaf R).obj P)).Additive :=
      presheafTensorRight_additive R _
    change (associatedSheaf R).map
      ((toPresheaf R).map (f + g) ⊗ₘ 𝟙 ((toPresheaf R).obj P)) = _
    rw [Functor.map_add]
    change (associatedSheaf R).map ((tensorRight ((toPresheaf R).obj P)).map
      ((toPresheaf R).map f + (toPresheaf R).map g)) = _
    rw [Functor.map_add, Functor.map_add]
    rfl

end SheafOfModulesOfCommRing
