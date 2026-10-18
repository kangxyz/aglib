/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Tensor.Monoidal.Symmetric

/-! Focused consumer of the symmetric monoidal structure on scheme modules: the instances are
found with no option or hypothesis, the data fields are the existing tensor maps by `rfl`, and
the associator acts on nested pure section tensors. -/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

universe u

variable (X : Scheme.{u})

example : MonoidalCategory X.Modules := inferInstance

example : SymmetricCategory X.Modules := inferInstance

example : (toLocalizedMonoidal X).Braided := inferInstance

example (M N : X.Modules) : M ⊗ N = tensorSheaf X M N := rfl

example {M M' N N' : X.Modules} (f : M ⟶ M') (g : N ⟶ N') :
    f ⊗ₘ g = tensorSheafMap X f g := rfl

example (M : X.Modules) : λ_ M = tensorSheafLeftUnit X M := rfl

example (M N O : X.Modules) : α_ M N O = tensorSheafAssociator X M N O := rfl

example (M N : X.Modules) : β_ M N = tensorSheafBraiding X M N := rfl

example (M : X.Modules) : moduleTensorLeftFunctor X M = tensorLeft M := rfl

example (M N O P : X.Modules) :
    (α_ M N O).hom ▷ P ≫ (α_ M (N ⊗ O) P).hom ≫ M ◁ (α_ N O P).hom =
      (α_ (M ⊗ N) O P).hom ≫ (α_ M N (O ⊗ P)).hom :=
  MonoidalCategory.pentagon M N O P

example (M N : X.Modules) : (β_ M N).hom ≫ (β_ N M).hom = 𝟙 (M ⊗ N) :=
  SymmetricCategory.symmetry M N

example (M N O : X.Modules) (U : X.Opensᵒᵖ) (m : M.val.obj U) (n : N.val.obj U)
    (o : O.val.obj U) :
    (α_ M N O).hom.val.app U
        ((tensorSheafUnit X (M ⊗ N : X.Modules) O).app U
          ((tensorSheafUnit X M N).app U (m ⊗ₜ n) ⊗ₜ o)) =
      (tensorSheafUnit X M (N ⊗ O : X.Modules)).app U
        (m ⊗ₜ (tensorSheafUnit X N O).app U (n ⊗ₜ o)) :=
  associator_hom_tmul X M N O U m n o

/--
info: 'AlgebraicGeometry.Scheme.Modules.monoidalCategory' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms monoidalCategory

/--
info: 'AlgebraicGeometry.Scheme.Modules.braidedCategory' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms braidedCategory

/--
info: 'AlgebraicGeometry.Scheme.Modules.symmetricCategory' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms symmetricCategory

/--
info: 'AlgebraicGeometry.Scheme.Modules.instMonoidalToLocalizedMonoidal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms instMonoidalToLocalizedMonoidal

/--
info: 'AlgebraicGeometry.Scheme.Modules.instBraidedToLocalizedMonoidal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms instBraidedToLocalizedMonoidal

/--
info: 'AlgebraicGeometry.Scheme.Modules.tensorSheafAssociator' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms tensorSheafAssociator

/--
info: 'AlgebraicGeometry.Scheme.Modules.map_unit_whiskerRight_comp_tensorSheafAssociator_hom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms map_unit_whiskerRight_comp_tensorSheafAssociator_hom

/--
info: 'AlgebraicGeometry.Scheme.Modules.associatedSheafUnit_comp_tensorSheafAssociator_hom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms associatedSheafUnit_comp_tensorSheafAssociator_hom

/--
info: 'AlgebraicGeometry.Scheme.Modules.tensorSheafAssociator_hom_tmul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms tensorSheafAssociator_hom_tmul

/--
info: 'AlgebraicGeometry.Scheme.Modules.tensorSheafAssociator_inv_tmul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms tensorSheafAssociator_inv_tmul

/--
info: 'AlgebraicGeometry.Scheme.Modules.associator_hom_tmul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms associator_hom_tmul

/--
info: 'AlgebraicGeometry.Scheme.Modules.associator_inv_tmul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms associator_inv_tmul

/--
info: 'AlgebraicGeometry.Scheme.Modules.toLocalizedMonoidal_map_associator' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms toLocalizedMonoidal_map_associator

/--
info: 'AlgebraicGeometry.Scheme.Modules.toLocalizedMonoidal_map_tensorHom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms toLocalizedMonoidal_map_tensorHom

/--
info: 'AlgebraicGeometry.Scheme.Modules.toLocalizedMonoidal_map_leftUnitor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms toLocalizedMonoidal_map_leftUnitor

/--
info: 'AlgebraicGeometry.Scheme.Modules.toLocalizedMonoidal_map_rightUnitor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms toLocalizedMonoidal_map_rightUnitor

/--
info: 'AlgebraicGeometry.Scheme.Modules.toLocalizedMonoidal_μ_comp_map_braiding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms toLocalizedMonoidal_μ_comp_map_braiding

/--
info: 'AlgebraicGeometry.Scheme.Modules.moduleTensorLeftFunctor_eq_tensorLeft' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms moduleTensorLeftFunctor_eq_tensorLeft

/--
info: 'AlgebraicGeometry.Scheme.Modules.moduleTensorRightFunctor_eq_tensorRight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms moduleTensorRightFunctor_eq_tensorRight

/--
info: 'CategoryTheory.Localization.Monoidal.map_whiskerRight_comp_associator_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CategoryTheory.Localization.Monoidal.map_whiskerRight_comp_associator_eq

/--
info: 'CategoryTheory.Localization.Monoidal.map_tensorHom_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CategoryTheory.Localization.Monoidal.map_tensorHom_eq

/--
info: 'CategoryTheory.Localization.Monoidal.μOf_hom_comp_map_braiding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CategoryTheory.Localization.Monoidal.μOf_hom_comp_map_braiding
