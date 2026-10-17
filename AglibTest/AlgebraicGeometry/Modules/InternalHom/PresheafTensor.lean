/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.InternalHom
public import Aglib.AlgebraicGeometry.Modules.InternalHom.PresheafTensor

/-! Focused consumer of the presheaf-source Hom sheaf and the presheaf tensor–Hom bijection.
The tensor product is Mathlib's pointwise tensor of `PresheafOfModulesOfCommRing X.sheaf.obj`;
the first tensor factor `P` (the source) and the second tensor factor `Q` are arbitrary module
presheaves and the target `N` is an arbitrary module sheaf on an arbitrary scheme. The first
example records that the presheaf-source construction applied to the underlying presheaf of a
module sheaf is definitionally the existing `InternalHom.sheaf`. -/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry Scheme.Modules

universe u

variable (X : Scheme.{u})

example (M N : X.Modules) : InternalHom.PresheafSource.sheaf X M.val N = InternalHom.sheaf X M N :=
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
example (P Q : PresheafOfModulesOfCommRing.{u} X.sheaf.obj) (N : X.Modules) :
    (P ⊗ Q ⟶ N.val) ≃ (Q ⟶ (InternalHom.PresheafSource.sheaf X P N).val) :=
  InternalHom.PresheafSource.tensorHomEquiv X P Q N

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
example (P Q Q' : PresheafOfModulesOfCommRing.{u} X.sheaf.obj) (N : X.Modules) (g : Q' ⟶ Q)
    (h : P ⊗ Q ⟶ N.val) :
    InternalHom.PresheafSource.tensorHomEquiv X P Q' N (P ◁ g ≫ h) =
      g ≫ InternalHom.PresheafSource.tensorHomEquiv X P Q N h :=
  InternalHom.PresheafSource.tensorHomEquiv_whiskerLeft_comp g h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
example (P Q : PresheafOfModulesOfCommRing.{u} X.sheaf.obj) (N : X.Modules)
    (k : Q ⟶ (InternalHom.PresheafSource.sheaf X P N).val) (U : X.Opensᵒᵖ) (p : P.obj U)
    (q : Q.obj U) :
    ((InternalHom.PresheafSource.tensorHomEquiv X P Q N).symm k).app U (p ⊗ₜ q) =
      (k.app U q).val.app (Opposite.op (Over.mk (𝟙 U.unop))) p :=
  InternalHom.PresheafSource.uncurry_app_tmul X P Q N k U p q

/--
info: 'AlgebraicGeometry.Scheme.Modules.InternalHom.PresheafSource.sheaf' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms InternalHom.PresheafSource.sheaf

/--
info: 'AlgebraicGeometry.Scheme.Modules.InternalHom.PresheafSource.linearity_isLocal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms InternalHom.PresheafSource.linearity_isLocal

/--
info: 'AlgebraicGeometry.Scheme.Modules.InternalHom.PresheafSource.tensorHomEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms InternalHom.PresheafSource.tensorHomEquiv

/--
info: 'AlgebraicGeometry.Scheme.Modules.InternalHom.PresheafSource.tensorHomEquiv_whiskerLeft_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms InternalHom.PresheafSource.tensorHomEquiv_whiskerLeft_comp
