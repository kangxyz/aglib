/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.InternalHom.PresheafSource
public import Aglib.Algebra.Category.ModuleCat.Sheaf.InternalHom.PresheafTensor

/-!
# The original presheaf tensor–Hom API as a Zariski realization

The constructors and value laws specialize the actual arbitrary-site presheaf-source
currying equivalence. The native Opens category is a `SmallCategory`, and its object,
morphism and coefficient universes are all `u`; the common bound remains `u`.
The original pointwise tensor, structural scalars and section formulas are retained.
No sheaf, quasicoherence or finiteness condition is imposed on either source presheaf.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules.InternalHom.PresheafSource

universe u

variable (X : Scheme.{u}) (P Q : PresheafOfModulesOfCommRing.{u} X.sheaf.obj)
  (N : SheafOfModules.{u} X.ringCatSheaf)

/-- The original currying section, from the actual generic constructor. -/
abbrev currySection (h : P ⊗ Q ⟶ N.val) (U : X.Opensᵒᵖ) (q : Q.obj U) :
    (sheaf X P N).val.obj U :=
  _root_.SheafOfModules.InternalHom.PresheafSource.currySection.{u, u, u}
    (C := X.Opens) (J := Opens.grothendieckTopology X) X.sheaf P Q N h U q

/-- The original presheaf currying morphism, from the actual generic constructor. -/
abbrev curry (h : P ⊗ Q ⟶ N.val) : Q ⟶ (sheaf X P N).val :=
  _root_.SheafOfModules.InternalHom.PresheafSource.curry.{u, u, u}
    (C := X.Opens) (J := Opens.grothendieckTopology X) X.sheaf P Q N h

/-- The original presheaf uncurrying morphism, from the actual generic constructor. -/
abbrev uncurry (k : Q ⟶ (sheaf X P N).val) : P ⊗ Q ⟶ N.val :=
  _root_.SheafOfModules.InternalHom.PresheafSource.uncurry.{u, u, u}
    (C := X.Opens) (J := Opens.grothendieckTopology X) X.sheaf P Q N k

/-- The original pure-tensor value is retained. -/
theorem uncurry_app_tmul (k : Q ⟶ (sheaf X P N).val) (U : X.Opensᵒᵖ) (p : P.obj U)
    (q : Q.obj U) :
    (uncurry X P Q N k).app U (p ⊗ₜ q) = (k.app U q).val.app (op (Over.mk (𝟙 U.unop))) p :=
  _root_.SheafOfModules.InternalHom.PresheafSource.uncurry_app_tmul.{u, u, u}
    (C := X.Opens) (J := Opens.grothendieckTopology X) X.sheaf P Q N k U p q

theorem uncurry_curry (h : P ⊗ Q ⟶ N.val) : uncurry X P Q N (curry X P Q N h) = h :=
  _root_.SheafOfModules.InternalHom.PresheafSource.uncurry_curry.{u, u, u}
    (C := X.Opens) (J := Opens.grothendieckTopology X) X.sheaf P Q N h

theorem curry_uncurry (k : Q ⟶ (sheaf X P N).val) : curry X P Q N (uncurry X P Q N k) = k :=
  _root_.SheafOfModules.InternalHom.PresheafSource.curry_uncurry.{u, u, u}
    (C := X.Opens) (J := Opens.grothendieckTopology X) X.sheaf P Q N k

/-- The original tensor–Hom equivalence is the actual generic one. -/
abbrev tensorHomEquiv : (P ⊗ Q ⟶ N.val) ≃ (Q ⟶ (sheaf X P N).val) :=
  _root_.SheafOfModules.InternalHom.PresheafSource.tensorHomEquiv.{u, u, u}
    (C := X.Opens) (J := Opens.grothendieckTopology X) X.sheaf P Q N

/-- The whole original currying map is the actual generic map on the same input. -/
theorem curry_eq_generic (h : P ⊗ Q ⟶ N.val) :
    curry X P Q N h =
      _root_.SheafOfModules.InternalHom.PresheafSource.curry.{u, u, u}
        (C := X.Opens) (J := Opens.grothendieckTopology X) X.sheaf P Q N h := rfl

/-- The whole original uncurrying map is the actual generic map on the same input. -/
theorem uncurry_eq_generic (k : Q ⟶ (sheaf X P N).val) :
    uncurry X P Q N k =
      _root_.SheafOfModules.InternalHom.PresheafSource.uncurry.{u, u, u}
        (C := X.Opens) (J := Opens.grothendieckTopology X) X.sheaf P Q N k := rfl

/-- The whole original equivalence is the actual generic equivalence. -/
theorem tensorHomEquiv_eq_generic :
    tensorHomEquiv X P Q N =
      _root_.SheafOfModules.InternalHom.PresheafSource.tensorHomEquiv.{u, u, u}
        (C := X.Opens) (J := Opens.grothendieckTopology X) X.sheaf P Q N := rfl

variable {X P Q N}

/-- Original input naturality retains the actual pointwise tensor map. -/
theorem tensorHomEquiv_whiskerLeft_comp {Q' : PresheafOfModulesOfCommRing.{u} X.sheaf.obj}
    (g : Q' ⟶ Q) (h : P ⊗ Q ⟶ N.val) :
    tensorHomEquiv X P Q' N (P ◁ g ≫ h) = g ≫ tensorHomEquiv X P Q N h :=
  _root_.SheafOfModules.InternalHom.PresheafSource.tensorHomEquiv_whiskerLeft_comp.{u, u, u}
    (C := X.Opens) (J := Opens.grothendieckTopology X) X.sheaf g h

end AlgebraicGeometry.Scheme.Modules.InternalHom.PresheafSource
