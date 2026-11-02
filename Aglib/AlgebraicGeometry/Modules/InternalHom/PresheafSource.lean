/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Aglib.Algebra.Category.ModuleCat.Sheaf.InternalHom.PresheafSource

/-!
# The structure-linear Hom sheaf from a module presheaf

For a module presheaf `P` and a module sheaf `N` on a scheme, the structure-linear Hom
sheaf `InternalHom.PresheafSource.sheaf X P N` has, over an open `U`, the additive natural
transformations from `P` to `N` on the opens below `U` whose components are linear over the
structure sheaf. Its construction is that of `InternalHom.sheaf` with an arbitrary module
presheaf as source: the raw Hom presheaf only uses the underlying abelian presheaf of the
source, and both the sheaf condition and the locality of linearity come from the target.
No sheaf condition, quasicoherence or finiteness is imposed on `P`.

All constructors delegate to the generic arbitrary-site presheaf-source Hom.
The original structure scalars, actual forgotten ring sheaf and component maps are
preserved; no sheafification or choice of a replacement source is involved.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules.InternalHom.PresheafSource
universe u
variable (X : Scheme.{u}) (P : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj)
  (N : SheafOfModules.{u} X.ringCatSheaf)

/-- Additive natural transformations on the original open slice. -/
abbrev RawHom (U : X.Opens) : Type u :=
  SheafOfModules.InternalHom.PresheafSource.RawHom
    (C := X.Opens) (J := Opens.grothendieckTopology X) X.sheaf P N U

instance rawHomTargetModule (U : X.Opens) (V : (Over U)ᵒᵖ) :
    Module Γ(X, V.unop.left) (((Over.forget U).op ⋙ N.val.presheaf).obj V) :=
  (N.val.obj (op V.unop.left)).isModule

/-- The generic target scalar action on the original scheme sections. -/
abbrev smulRawHom (U : X.Opens) (r : Γ(X, U)) (f : RawHom X P N U) : RawHom X P N U :=
  SheafOfModules.InternalHom.PresheafSource.smulRawHom X.sheaf P N U r f

instance rawHomSMul (U : X.Opens) : SMul Γ(X, U) (RawHom X P N U) :=
  SheafOfModules.InternalHom.PresheafSource.rawHomSMul X.sheaf P N U

/-- The component formula for the original target scalar action. -/
theorem smulRawHom_apply (U : X.Opens) (r : Γ(X, U)) (f : RawHom X P N U)
    (V : (Over U)ᵒᵖ) (s : P.obj (op V.unop.left)) :
    (r • f).app V s = X.presheaf.map V.unop.hom.op r • f.app V s := rfl

instance rawHomModule (U : X.Opens) : Module Γ(X, U) (RawHom X P N U) :=
  SheafOfModules.InternalHom.PresheafSource.rawHomModule X.sheaf P N U

instance rawHomModuleOp (U : X.Opensᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj U) (RawHom X P N U.unop) := rawHomModule X P N U.unop

/-- The generic additive Hom presheaf on the original Zariski site. -/
abbrev rawPresheaf : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj :=
  SheafOfModules.InternalHom.PresheafSource.rawPresheaf X.sheaf P N

/-- The generic additive Hom sheaf on the original Zariski site. -/
abbrev rawSheaf : SheafOfModules.{u} X.ringCatSheaf :=
  SheafOfModules.InternalHom.PresheafSource.rawSheaf X.sheaf P N

/-- Every component is linear over its original structure ring. -/
abbrev IsLinear (U : X.Opens) (f : RawHom X P N U) : Prop :=
  SheafOfModules.InternalHom.PresheafSource.IsLinear X.sheaf P N U f

/-- The original scalar submodule of componentwise linear transformations. -/
abbrev linearSubmodule (U : X.Opens) : Submodule Γ(X, U) (RawHom X P N U) :=
  SheafOfModules.InternalHom.PresheafSource.linearSubmodule X.sheaf P N U

/-- The subpresheaf of componentwise structure-linear transformations. -/
abbrev linearPresheaf : (rawPresheaf X P N).Submodule :=
  SheafOfModules.InternalHom.PresheafSource.linearPresheaf X.sheaf P N

/-- The arbitrary-site locality theorem on the original Zariski site. -/
theorem linearity_isLocal {U : X.Opensᵒᵖ} (f : (rawSheaf X P N).val.obj U)
    (hf : (linearPresheaf X P N).toSubfunctor.sieveOfSection f ∈
      (Opens.grothendieckTopology X) U.unop) :
    f ∈ (linearPresheaf X P N).obj U :=
  SheafOfModules.InternalHom.PresheafSource.linearity_isLocal X.sheaf P N f hf

/-- Actual ring-linear Hom, specialized from the generic construction. -/
abbrev sheaf : SheafOfModules.{u} X.ringCatSheaf :=
  SheafOfModules.InternalHom.PresheafSource.sheaf X.sheaf P N

/-- The original presheaf-source Hom is the generic constructor for the same actual inputs. -/
theorem sheaf_eq_generic :
    sheaf X P N = SheafOfModules.InternalHom.PresheafSource.sheaf X.sheaf P N := rfl

end AlgebraicGeometry.Scheme.Modules.InternalHom.PresheafSource
