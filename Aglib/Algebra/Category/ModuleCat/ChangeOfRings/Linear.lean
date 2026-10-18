/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Additive
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Algebra

/-!
# Base-ring linearity of native scalar extension

The original scalar-extension functor along a specified algebra map is
linear over the base ring. The proof retains the original pure tensors and
the original algebra tensor-product comparison. Ring and module carrier
universes are independent. No flatness or finiteness premise, new scalar
action or alternative extension functor is introduced.

Native scalar extension on Ext at a localization is the immediate consumer.
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct ChangeOfRings ModuleCat.Algebra
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe r s m
namespace ModuleCat.Algebra
variable (R : Type r) (A : Type s) [CommRing R] [CommRing A] [Algebra R A]
/-- Native extension along the specified algebra map preserves the original base-ring scalars. -/
instance extendScalars_linear :
    (ModuleCat.extendScalars.{r,s,m} (algebraMap R A)).Linear R where
  map_smul {M N} f r := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    apply (ModuleCat.extendScalarsAlgebraObjIso R A N).toLinearEquiv.injective
    change (ModuleCat.extendScalarsAlgebraObjIso R A N).hom
        ((1 : A) ⊗ₜ[R,algebraMap R A] (r • f m)) =
      (ModuleCat.extendScalarsAlgebraObjIso R A N).hom
        (algebraMap R A r • ((1 : A) ⊗ₜ[R,algebraMap R A] f m))
    rw [(ModuleCat.extendScalarsAlgebraObjIso R A N).hom.hom.map_smul]
    rw [ModuleCat.extendScalarsAlgebraObjIso_hom_tmul,
      ModuleCat.extendScalarsAlgebraObjIso_hom_tmul]
    rw [IsScalarTower.algebraMap_smul A]
    exact TensorProduct.tmul_smul r (1 : A) (f m)

end ModuleCat.Algebra
