/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.CategoryTheory.Sites.SheafHom

/-!
# Ring-linear Hom from a module presheaf on a site

For a commutative ring sheaf `R`, a module presheaf `P` and a module sheaf `N`,
this constructs the sheaf of componentwise linear natural transformations on slices.
Only the target is required to be a sheaf. Scalars act by restriction followed by
multiplication in the target. All ring structures are those of the actual commutative
ring sheaf and its native forgetful image in `RingCat`.

The site-object, site-morphism, ring and module-carrier universes are independent.
The output carrier is `max uC vC uM`, the universe of the natural transformations.
Thus this construction does not assert closure in an arbitrary smaller carrier universe.

The construction generalizes the original scheme module internal Hom and its
presheaf-source variant, extracted from `R5Lab.AlgebraicGeometry.Curves.Picard.HomSheaf`
at revision `95a3772b895fbc19a81684be4ffd519d0fdcd6b3`.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Opposite

universe uC vC uR uM

namespace SheafOfModules.InternalHom.PresheafSource

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{uR} RingCat.{uR})]
  (R : Sheaf J CommRingCat.{uR})

variable
  (P : PresheafOfModules.{uM} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  (N : SheafOfModules.{uM} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))

/-- Additive natural transformations between the underlying presheaves of `P` and `N`
restricted to the slice over `U`. -/
abbrev RawHom (U : C) : Type (max uC vC uM) :=
  (Over.forget U).op ⋙ P.presheaf ⟶ (Over.forget U).op ⋙ N.val.presheaf

instance rawHomTargetModule (U : C) (V : (Over U)ᵒᵖ) :
    Module (R.obj.obj (op V.unop.left)) (((Over.forget U).op ⋙ N.val.presheaf).obj V) :=
  (N.val.obj (op V.unop.left)).isModule

/-- Multiply each component by the restriction of `r`, acting in the target module. -/
def smulRawHom (U : C) (r : R.obj.obj (op U)) (f : RawHom R P N U) : RawHom R P N U where
  app V := AddCommGrpCat.ofHom
    ((R.obj.map V.unop.hom.op r) • (f.app V).hom)
  naturality {V W} i := by
    ext s
    change (R.obj.map W.unop.hom.op r) •
      f.app W (P.map i.unop.left.op s) =
      N.val.map i.unop.left.op ((R.obj.map V.unop.hom.op r) • f.app V s)
    rw [N.val.map_smul]
    congr 1
    · change R.obj.map W.unop.hom.op r =
        R.obj.map i.unop.left.op (R.obj.map V.unop.hom.op r)
      rw [← Functor.map_comp_apply, ← op_comp, Over.w i.unop]
    · exact NatTrans.naturality_apply f i s

instance rawHomSMul (U : C) : SMul (R.obj.obj (op U)) (RawHom R P N U) :=
  ⟨smulRawHom R P N U⟩

/-- The component formula for the target scalar action. -/
theorem smulRawHom_apply (U : C) (r : R.obj.obj (op U)) (f : RawHom R P N U)
    (V : (Over U)ᵒᵖ) (s : P.obj (op V.unop.left)) :
    (r • f).app V s = R.obj.map V.unop.hom.op r • f.app V s := rfl

instance rawHomModule (U : C) : Module (R.obj.obj (op U)) (RawHom R P N U) where
  smul := smulRawHom R P N U
  one_smul f := by
    ext V s
    change R.obj.map V.unop.hom.op 1 • f.app V s = f.app V s
    rw [map_one, one_smul]
  mul_smul r t f := by
    ext V s
    change R.obj.map V.unop.hom.op (r * t) • f.app V s =
      R.obj.map V.unop.hom.op r • (R.obj.map V.unop.hom.op t • f.app V s)
    rw [map_mul, mul_smul]
  smul_zero r := by
    ext V s
    change R.obj.map V.unop.hom.op r • (0 : N.val.obj (op V.unop.left)) = 0
    rw [smul_zero]
  smul_add r f g := by
    ext V s
    change R.obj.map V.unop.hom.op r • (f.app V s + g.app V s) =
      R.obj.map V.unop.hom.op r • f.app V s + R.obj.map V.unop.hom.op r • g.app V s
    rw [smul_add]
  add_smul r t f := by
    ext V s
    change R.obj.map V.unop.hom.op (r + t) • f.app V s =
      R.obj.map V.unop.hom.op r • f.app V s + R.obj.map V.unop.hom.op t • f.app V s
    rw [map_add, add_smul]
  zero_smul f := by
    ext V s
    change R.obj.map V.unop.hom.op 0 • f.app V s = 0
    rw [map_zero, zero_smul]

instance rawHomModuleOp (U : Cᵒᵖ) :
    Module (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj.obj U)
      (RawHom R P N U.unop) := rawHomModule R P N U.unop

/-- The module presheaf of additive natural transformations on slices,
with scalars acting in the target. -/
def rawPresheaf : PresheafOfModules.{max uC vC uM}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj where
  obj U := by
    exact ModuleCat.of (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj.obj U)
      (RawHom R P N U.unop)
  map {U V} i := ModuleCat.ofHom
    (X := ModuleCat.of (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj.obj U)
      (RawHom R P N U.unop))
    (Y := (ModuleCat.restrictScalars
        (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj.map i).hom).obj
      (ModuleCat.of (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj.obj V)
        (RawHom R P N V.unop))) {
    toFun (f : RawHom R P N U.unop) := Functor.whiskerLeft (Over.map i.unop).op f
    map_add' f g := by
      change Functor.whiskerLeft (Over.map i.unop).op (f + g) =
        Functor.whiskerLeft (Over.map i.unop).op f + Functor.whiskerLeft (Over.map i.unop).op g
      ext W s
      rfl
    map_smul' r f := by
      change Functor.whiskerLeft (Over.map i.unop).op (smulRawHom R P N U.unop r f) =
        smulRawHom R P N V.unop (R.obj.map i r)
          (show RawHom R P N V.unop from Functor.whiskerLeft (Over.map i.unop).op f)
      ext W s
      change R.obj.map ((Over.map i.unop).obj W.unop).hom.op r •
        (show N.val.obj (op W.unop.left) from f.app (op ((Over.map i.unop).obj W.unop)) s) =
        R.obj.map W.unop.hom.op (R.obj.map i r) •
          (show N.val.obj (op W.unop.left) from f.app (op ((Over.map i.unop).obj W.unop)) s)
      congr 1
      exact ConcreteCategory.congr_hom (R.obj.map_comp i W.unop.hom.op) r }
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
def rawSheaf : SheafOfModules.{max uC vC uM}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) where
  val := rawPresheaf R P N
  isSheaf := by
    apply Presheaf.isSheaf_of_isSheaf_comp J
      (s := CategoryTheory.forget AddCommGrpCat)
    change Presheaf.IsSheaf J
      (CategoryTheory.presheafHom P.presheaf N.val.presheaf)
    exact N.isSheaf.hom P.presheaf

/-- Every component commutes with multiplication by sections of its structure ring. -/
def IsLinear (U : C) (f : RawHom R P N U) : Prop :=
  ∀ (V : (Over U)ᵒᵖ) (r : R.obj.obj (op V.unop.left)) (s : P.obj (op V.unop.left)),
    f.app V (r • s) = r • (show N.val.obj (op V.unop.left) from f.app V s)

/-- The `R.obj.obj (op U)`-submodule of additive natural transformations with structure-linear
components on every object over `U`. -/
def linearSubmodule (U : C) : _root_.Submodule (R.obj.obj (op U)) (RawHom R P N U) where
  carrier := IsLinear R P N U
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
    change R.obj.map V.unop.hom.op a • (show N.val.obj (op V.unop.left) from f.app V (r • s)) =
      r • (R.obj.map V.unop.hom.op a • (show N.val.obj (op V.unop.left) from f.app V s))
    rw [hf, smul_comm]

/-- The subpresheaf of `rawPresheaf` cut out by componentwise structure-linearity. -/
def linearPresheaf : (rawPresheaf R P N).Submodule where
  obj U := linearSubmodule R P N U.unop
  map {U V} i := by
    intro f hf W r s
    exact hf (op ((Over.map i.unop).obj W.unop)) r s

/-- Structure-linearity is local for the given Grothendieck topology. -/
theorem linearity_isLocal {U : Cᵒᵖ} (f : (rawSheaf R P N).val.obj U)
    (hf : (linearPresheaf R P N).toSubfunctor.sieveOfSection f ∈
      J U.unop) :
    f ∈ (linearPresheaf R P N).obj U := by
  change RawHom R P N U.unop at f
  intro V r s
  apply N.isSheaf.isSeparated _ _
    (J.pullback_stable V.unop.hom hf)
  intro W j hj
  let i : Over.mk (j ≫ V.unop.hom) ⟶ V.unop := Over.homMk j
  have hlin := hj (op (Over.mk (𝟙 W))) (R.obj.map j.op r) (P.map j.op s)
  change (Functor.whiskerLeft (Over.map (j ≫ V.unop.hom)).op f).app
      (op (Over.mk (𝟙 W))) (R.obj.map j.op r • P.map j.op s) =
    R.obj.map j.op r • (show N.val.obj (op W) from
      (Functor.whiskerLeft (Over.map (j ≫ V.unop.hom)).op f).app
        (op (Over.mk (𝟙 W))) (P.map j.op s)) at hlin
  have he (t : P.obj (op W)) :
      (Functor.whiskerLeft (Over.map (j ≫ V.unop.hom)).op f).app
          (op (Over.mk (𝟙 W))) t = f.app (op (Over.mk (j ≫ V.unop.hom))) t :=
    ConcreteCategory.congr_hom
      (CategoryTheory.presheafHom_map_app_op_mk_id (F := P.presheaf)
        (G := N.val.presheaf) (j ≫ V.unop.hom) f) t
  have hlin' : f.app (op (Over.mk (j ≫ V.unop.hom)))
      (R.obj.map j.op r • P.map j.op s) =
      R.obj.map j.op r • (show N.val.obj (op W) from
        f.app (op (Over.mk (j ≫ V.unop.hom))) (P.map j.op s)) :=
    (he _).symm.trans (hlin.trans
      (congrArg (fun a : N.val.obj (op W) => R.obj.map j.op r • a) (he _)))
  change N.val.map j.op (f.app V (r • s)) =
    N.val.map j.op (r • (show N.val.obj (op V.unop.left) from f.app V s))
  rw [N.val.map_smul]
  have hnat (t : P.obj (op V.unop.left)) := NatTrans.naturality_apply f i.op t
  change ∀ t : P.obj (op V.unop.left),
    f.app (op (Over.mk (j ≫ V.unop.hom))) (P.map j.op t) = N.val.map j.op (f.app V t) at hnat
  rw [← hnat, P.map_smul]
  exact hlin'.trans (congrArg (fun a : N.val.obj (op W) => R.obj.map j.op r • a) (hnat s))

/-- The sheaf of structure-linear homomorphisms from the module presheaf `P` to the module
sheaf `N` on all slices. -/
def sheaf : SheafOfModules.{max uC vC uM} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) :=
  (show (rawSheaf R P N).Submodule from
    { toSubmodule := linearPresheaf R P N
      isSheaf := by intro U f hf; exact linearity_isLocal R P N f hf }).toSheafOfModules

/-- Restriction is the actual whiskering map on slice natural transformations. -/
theorem sheaf_map_val {U V : Cᵒᵖ} (i : U ⟶ V)
    (s : (sheaf R P N).val.obj U) :
    ((sheaf R P N).val.map i s).val = Functor.whiskerLeft (Over.map i.unop).op s.val := rfl

/-- The component of a restricted section is its original component on the composite arrow. -/
theorem sheaf_map_app {U V : Cᵒᵖ} (i : U ⟶ V)
    (s : (sheaf R P N).val.obj U) (W : (Over V.unop)ᵒᵖ)
    (m : P.obj (op W.unop.left)) :
    ((sheaf R P N).val.map i s).val.app W m =
      s.val.app (op ((Over.map i.unop).obj W.unop)) m := rfl

end SheafOfModules.InternalHom.PresheafSource
