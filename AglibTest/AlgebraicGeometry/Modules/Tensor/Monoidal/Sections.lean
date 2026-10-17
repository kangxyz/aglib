/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Tensor.Monoidal.Sections

/-! Focused consumer of the scheme-module associator on pure section tensors: nested pure tensors
determine maps out of nested tensors of arbitrary module sheaves, with no line-bundle
hypothesis. It also guards the whiskerings, inverse unitors and braiding on pure section
tensors. -/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

universe u

variable {X : Scheme.{u}}

example (M N O : X.Modules) (U : X.Opens) (m : Γ(M, U)) (n : Γ(N, U)) (o : Γ(O, U)) :
    (α_ M N O).hom.val.app (op U)
        (moduleTensorSection X (M ⊗ N) O U (moduleTensorSection X M N U m n) o) =
      moduleTensorSection X M (N ⊗ O) U m (moduleTensorSection X N O U n o) :=
  associator_hom_moduleTensorSection M N O U m n o

example (L M N G : X.Modules) {f g : L ⊗ (M ⊗ N) ⟶ G}
    (h : ∀ (U : X.Opens) (l : Γ(L, U)) (m : Γ(M, U)) (n : Γ(N, U)),
      f.val.app (op U) (moduleTensorSection X L (M ⊗ N) U l (moduleTensorSection X M N U m n)) =
        g.val.app (op U)
          (moduleTensorSection X L (M ⊗ N) U l (moduleTensorSection X M N U m n))) :
    f = g :=
  moduleTensor_nested_hom_ext L M N h

/--
info: 'AlgebraicGeometry.Scheme.Modules.associator_hom_moduleTensorSection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms associator_hom_moduleTensorSection

/--
info: 'AlgebraicGeometry.Scheme.Modules.associator_inv_moduleTensorSection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms associator_inv_moduleTensorSection

/--
info: 'AlgebraicGeometry.Scheme.Modules.moduleTensor_nested_hom_ext' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms moduleTensor_nested_hom_ext

/--
info: 'AlgebraicGeometry.Scheme.Modules.moduleTensor_nested_hom_ext_left' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms moduleTensor_nested_hom_ext_left

/--
info: 'AlgebraicGeometry.Scheme.Modules.whiskerRight_moduleTensorSection' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.whiskerRight_moduleTensorSection

/--
info: 'AlgebraicGeometry.Scheme.Modules.whiskerLeft_moduleTensorSection' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.whiskerLeft_moduleTensorSection

/--
info: 'AlgebraicGeometry.Scheme.Modules.leftUnitor_inv_moduleTensorSection' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.leftUnitor_inv_moduleTensorSection

/--
info: 'AlgebraicGeometry.Scheme.Modules.rightUnitor_inv_moduleTensorSection' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.rightUnitor_inv_moduleTensorSection

/--
info: 'AlgebraicGeometry.Scheme.Modules.braiding_hom_moduleTensorSection' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.braiding_hom_moduleTensorSection
