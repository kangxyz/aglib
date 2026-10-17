/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Sites.SheafHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule

/-!
# The structure-linear Hom sheaf from a module presheaf

For a module presheaf `P` and a module sheaf `N` on a scheme, the structure-linear Hom
sheaf `InternalHom.PresheafSource.sheaf X P N` has, over an open `U`, the additive natural
transformations from `P` to `N` on the opens below `U` whose components are linear over the
structure sheaf. Its construction is that of `InternalHom.sheaf` with an arbitrary module
presheaf as source: the raw Hom presheaf only uses the underlying abelian presheaf of the
source, and both the sheaf condition and the locality of linearity come from the target.
No sheaf condition, quasicoherence or finiteness is imposed on `P`.

The declarations that let `Γ(X, V)` act on components of module presheaves over
`X.ringCatSheaf.obj` set `backward.isDefEq.respectTransparency false` locally: the two
coefficient rings agree only after unfolding `forget₂ CommRingCat RingCat` and the
semireducible `sheafCompose`.
-/

@[expose] public section

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules.InternalHom.PresheafSource
universe u
variable (X : Scheme.{u}) (P : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj)
  (N : SheafOfModules.{u} X.ringCatSheaf)

/-- Additive natural transformations between the underlying presheaves of `P` and `N`
restricted to the opens below `U`. -/
abbrev RawHom (U : X.Opens) :=
  (Over.forget U).op ⋙ P.presheaf ⟶ (Over.forget U).op ⋙ N.val.presheaf

instance rawHomTargetModule (U : X.Opens) (V : (Over U)ᵒᵖ) :
    Module Γ(X, V.unop.left) (((Over.forget U).op ⋙ N.val.presheaf).obj V) :=
  (N.val.obj (op V.unop.left)).isModule

set_option backward.isDefEq.respectTransparency false in
/-- Multiply each component by the restriction of `r`, acting in the target module. -/
def smulRawHom (U : X.Opens) (r : Γ(X, U)) (f : RawHom X P N U) : RawHom X P N U where
  app V := AddCommGrpCat.ofHom
    ((X.presheaf.map V.unop.hom.op r) • (f.app V).hom)
  naturality {V W} i := by
    ext s
    change (X.presheaf.map W.unop.hom.op r) •
      f.app W (P.map i.unop.left.op s) =
      N.val.map i.unop.left.op ((X.presheaf.map V.unop.hom.op r) • f.app V s)
    rw [N.val.map_smul]
    congr 1
    · change X.presheaf.map W.unop.hom.op r =
        X.presheaf.map i.unop.left.op (X.presheaf.map V.unop.hom.op r)
      rw [← Functor.map_comp_apply, ← op_comp, Over.w i.unop]
    · exact NatTrans.naturality_apply f i s

instance rawHomSMul (U : X.Opens) : SMul Γ(X, U) (RawHom X P N U) :=
  ⟨smulRawHom X P N U⟩

/-- The component formula for the target scalar action. -/
theorem smulRawHom_apply (U : X.Opens) (r : Γ(X, U)) (f : RawHom X P N U)
    (V : (Over U)ᵒᵖ) (s : P.obj (op V.unop.left)) :
    (r • f).app V s = X.presheaf.map V.unop.hom.op r • f.app V s := rfl

set_option backward.isDefEq.respectTransparency false in
instance rawHomModule (U : X.Opens) : Module Γ(X, U) (RawHom X P N U) where
  smul := smulRawHom X P N U
  one_smul f := by
    ext V s
    change X.presheaf.map V.unop.hom.op 1 • f.app V s = f.app V s
    rw [map_one, one_smul]
  mul_smul r t f := by
    ext V s
    change X.presheaf.map V.unop.hom.op (r * t) • f.app V s =
      X.presheaf.map V.unop.hom.op r • (X.presheaf.map V.unop.hom.op t • f.app V s)
    rw [map_mul, mul_smul]
  smul_zero r := by
    ext V s
    change X.presheaf.map V.unop.hom.op r • (0 : N.val.obj (op V.unop.left)) = 0
    rw [smul_zero]
  smul_add r f g := by
    ext V s
    change X.presheaf.map V.unop.hom.op r • (f.app V s + g.app V s) =
      X.presheaf.map V.unop.hom.op r • f.app V s + X.presheaf.map V.unop.hom.op r • g.app V s
    rw [smul_add]
  add_smul r t f := by
    ext V s
    change X.presheaf.map V.unop.hom.op (r + t) • f.app V s =
      X.presheaf.map V.unop.hom.op r • f.app V s + X.presheaf.map V.unop.hom.op t • f.app V s
    rw [map_add, add_smul]
  zero_smul f := by
    ext V s
    change X.presheaf.map V.unop.hom.op 0 • f.app V s = 0
    rw [map_zero, zero_smul]

instance rawHomModuleOp (U : X.Opensᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj U) (RawHom X P N U.unop) := rawHomModule X P N U.unop

set_option backward.isDefEq.respectTransparency false in
/-- The module presheaf of additive natural transformations on open restrictions,
with scalars acting in the target. -/
def rawPresheaf : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj where
  obj U := by
    exact ModuleCat.of (X.ringCatSheaf.obj.obj U) (RawHom X P N U.unop)
  map {U V} i := ModuleCat.ofHom
    (X := ModuleCat.of (X.ringCatSheaf.obj.obj U) (RawHom X P N U.unop))
    (Y := (ModuleCat.restrictScalars (X.ringCatSheaf.obj.map i).hom).obj
      (ModuleCat.of (X.ringCatSheaf.obj.obj V) (RawHom X P N V.unop))) {
    toFun (f : RawHom X P N U.unop) := Functor.whiskerLeft (Over.map i.unop).op f
    map_add' f g := by
      change Functor.whiskerLeft (Over.map i.unop).op (f + g) =
        Functor.whiskerLeft (Over.map i.unop).op f + Functor.whiskerLeft (Over.map i.unop).op g
      ext W s
      rfl
    map_smul' r f := by
      change Functor.whiskerLeft (Over.map i.unop).op (smulRawHom X P N U.unop r f) =
        smulRawHom X P N V.unop (X.presheaf.map i r)
          (show RawHom X P N V.unop from Functor.whiskerLeft (Over.map i.unop).op f)
      ext W s
      change X.presheaf.map ((Over.map i.unop).obj W.unop).hom.op r •
        (show N.val.obj (op W.unop.left) from f.app (op ((Over.map i.unop).obj W.unop)) s) =
        X.presheaf.map W.unop.hom.op (X.presheaf.map i r) •
          (show N.val.obj (op W.unop.left) from f.app (op ((Over.map i.unop).obj W.unop)) s)
      congr 1
      exact ConcreteCategory.congr_hom (X.presheaf.map_comp i W.unop.hom.op) r }
  map_id U := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    exact ConcreteCategory.congr_hom
      ((CategoryTheory.presheafHom P.presheaf N.val.presheaf).map_id U) f
  map_comp i j := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    exact ConcreteCategory.congr_hom
      ((CategoryTheory.presheafHom P.presheaf N.val.presheaf).map_comp i j) f

/-- The sheaf of all additive maps, with scalars acting in the target. -/
def rawSheaf : SheafOfModules.{u} X.ringCatSheaf where
  val := rawPresheaf X P N
  isSheaf := by
    apply Presheaf.isSheaf_of_isSheaf_comp (Opens.grothendieckTopology X)
      (s := CategoryTheory.forget AddCommGrpCat)
    change Presheaf.IsSheaf (Opens.grothendieckTopology X)
      (CategoryTheory.presheafHom P.presheaf N.val.presheaf)
    exact N.isSheaf.hom P.presheaf

set_option backward.isDefEq.respectTransparency false in
/-- Every component commutes with multiplication by sections of its structure ring. -/
def IsLinear (U : X.Opens) (f : RawHom X P N U) : Prop :=
  ∀ (V : (Over U)ᵒᵖ) (r : Γ(X, V.unop.left)) (s : P.obj (op V.unop.left)),
    f.app V (r • s) = r • (show N.val.obj (op V.unop.left) from f.app V s)

set_option backward.isDefEq.respectTransparency false in
/-- The `Γ(X, U)`-submodule of additive natural transformations with structure-linear
components on every open below `U`. -/
def linearSubmodule (U : X.Opens) : Submodule Γ(X, U) (RawHom X P N U) where
  carrier := IsLinear X P N U
  zero_mem' := by
    intro V r s
    change 0 = r • (0 : N.val.obj (op V.unop.left))
    exact (smul_zero r).symm
  add_mem' := by
    intro f g hf hg V r s
    change f.app V (r • s) + g.app V (r • s) =
      r • (show N.val.obj (op V.unop.left) from f.app V s + g.app V s)
    rw [hf, hg, smul_add]
  smul_mem' := by
    intro a f hf V r s
    change X.presheaf.map V.unop.hom.op a • (show N.val.obj (op V.unop.left) from f.app V (r • s)) =
      r • (X.presheaf.map V.unop.hom.op a • (show N.val.obj (op V.unop.left) from f.app V s))
    rw [hf, smul_comm]

/-- The subpresheaf of `rawPresheaf` cut out by componentwise structure-linearity. -/
def linearPresheaf : (rawPresheaf X P N).Submodule where
  obj U := linearSubmodule X P N U.unop
  map {U V} i := by
    intro f hf W r s
    exact hf (op ((Over.map i.unop).obj W.unop)) r s

set_option backward.isDefEq.respectTransparency false in
/-- Structure-linearity of a section of the raw Hom sheaf is local on its open. -/
theorem linearity_isLocal {U : X.Opensᵒᵖ} (f : (rawSheaf X P N).val.obj U)
    (hf : (linearPresheaf X P N).toSubfunctor.sieveOfSection f ∈
      (Opens.grothendieckTopology X) U.unop) :
    f ∈ (linearPresheaf X P N).obj U := by
  intro V r s
  apply N.isSheaf.isSeparated _ _
    ((Opens.grothendieckTopology X).pullback_stable V.unop.hom hf)
  intro W j hj
  let i : Over.mk (j ≫ V.unop.hom) ⟶ V.unop := Over.homMk j
  have hlin := hj (op (Over.mk (𝟙 W))) (X.presheaf.map j.op r) (P.map j.op s)
  change f.app (op (Over.mk (j ≫ V.unop.hom)))
      (X.presheaf.map j.op r • P.map j.op s) =
    X.presheaf.map j.op r • (show N.val.obj (op W) from
      f.app (op (Over.mk (j ≫ V.unop.hom))) (P.map j.op s)) at hlin
  change N.val.map j.op (f.app V (r • s)) =
    N.val.map j.op (r • (show N.val.obj (op V.unop.left) from f.app V s))
  rw [N.val.map_smul]
  have hnat (t : P.obj (op V.unop.left)) := NatTrans.naturality_apply f i.op t
  change ∀ t : P.obj (op V.unop.left),
    f.app (op (Over.mk (j ≫ V.unop.hom))) (P.map j.op t) = N.val.map j.op (f.app V t) at hnat
  rw [← hnat, P.map_smul]
  exact hlin.trans (congrArg (fun a : N.val.obj (op W) => X.presheaf.map j.op r • a) (hnat s))

/-- The sheaf of structure-linear homomorphisms from the module presheaf `P` to the module
sheaf `N` on all open restrictions. -/
def sheaf : SheafOfModules.{u} X.ringCatSheaf :=
  (show (rawSheaf X P N).Submodule from
    { toSubmodule := linearPresheaf X P N
      isSheaf := by intro U f hf; exact linearity_isLocal X P N f hf }).toSheafOfModules

end AlgebraicGeometry.Scheme.Modules.InternalHom.PresheafSource
