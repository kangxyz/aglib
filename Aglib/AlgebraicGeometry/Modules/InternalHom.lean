/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: R5Lab contributors
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Sites.SheafHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule

/-!
# The structure-linear Hom sheaf

The Hom sheaf is constructed from natural transformations of restricted
abelian sheaves, with structure-linearity imposed by a local submodule
condition. Its sections are actual restricted module-sheaf morphisms.
Open-local isomorphisms act by precomposition and postcomposition, and the
constructed Hom sheaf from the structure sheaf to a module sheaf is
isomorphic to that module sheaf. Both source and target modules are arbitrary.

Extraction source: `R5Lab.AlgebraicGeometry.Curves.Picard.HomSheaf`
at revision `95a3772b895fbc19a81684be4ffd519d0fdcd6b3`.
The primary namespace is `AlgebraicGeometry.Scheme.Modules.InternalHom`;
source names are provenance.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules.InternalHom
universe u
variable (X : Scheme.{u}) (M N : SheafOfModules.{u} X.ringCatSheaf)
/-- Additive natural transformations between the underlying presheaves of `M` and `N`
restricted to the opens below `U`. -/
abbrev RawHom (U : X.Opens) :=
  (Over.forget U).op ⋙ M.val.presheaf ⟶ (Over.forget U).op ⋙ N.val.presheaf

instance rawHomTargetModule (U : X.Opens) (V : (Over U)ᵒᵖ) :
    Module Γ(X, V.unop.left) (((Over.forget U).op ⋙ N.val.presheaf).obj V) :=
  (N.val.obj (op V.unop.left)).isModule

/-- Multiply each component by the restriction of `r`, acting in the target module. -/
def smulRawHom (U : X.Opens) (r : Γ(X, U)) (f : RawHom X M N U) : RawHom X M N U where
  app V := AddCommGrpCat.ofHom
    ((X.presheaf.map V.unop.hom.op r) • (f.app V).hom)
  naturality {V W} i := by
    ext s
    change (X.presheaf.map W.unop.hom.op r) •
      f.app W (M.val.map i.unop.left.op s) =
      N.val.map i.unop.left.op ((X.presheaf.map V.unop.hom.op r) • f.app V s)
    rw [N.val.map_smul]
    congr 1
    · change X.presheaf.map W.unop.hom.op r =
        X.presheaf.map i.unop.left.op (X.presheaf.map V.unop.hom.op r)
      rw [← Functor.map_comp_apply, ← op_comp, Over.w i.unop]
    · exact NatTrans.naturality_apply f i s

instance rawHomSMul (U : X.Opens) : SMul Γ(X, U) (RawHom X M N U) :=
  ⟨smulRawHom X M N U⟩

/-- The component formula for the target scalar action. It is an explicit rewrite lemma;
the generic morphism-coercion rules already simplify its left-hand side. -/
theorem smulRawHom_apply (U : X.Opens) (r : Γ(X, U)) (f : RawHom X M N U)
    (V : (Over U)ᵒᵖ) (s : M.val.obj (op V.unop.left)) :
    (r • f).app V s = X.presheaf.map V.unop.hom.op r • f.app V s := rfl

instance rawHomModule (U : X.Opens) : Module Γ(X, U) (RawHom X M N U) where
  smul := smulRawHom X M N U
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
    Module (X.ringCatSheaf.obj.obj U) (RawHom X M N U.unop) := rawHomModule X M N U.unop

/-- The module presheaf of additive natural transformations on open restrictions,
with scalars acting in the target. -/
def rawPresheaf : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj where
  obj U := by
    exact ModuleCat.of (X.ringCatSheaf.obj.obj U) (RawHom X M N U.unop)
  map {U V} i := ModuleCat.ofHom
    (X := ModuleCat.of (X.ringCatSheaf.obj.obj U) (RawHom X M N U.unop))
    (Y := (ModuleCat.restrictScalars (X.ringCatSheaf.obj.map i).hom).obj
      (ModuleCat.of (X.ringCatSheaf.obj.obj V) (RawHom X M N V.unop))) {
    toFun (f : RawHom X M N U.unop) := Functor.whiskerLeft (Over.map i.unop).op f
    map_add' f g := by
      change Functor.whiskerLeft (Over.map i.unop).op (f + g) =
        Functor.whiskerLeft (Over.map i.unop).op f + Functor.whiskerLeft (Over.map i.unop).op g
      ext W s
      rfl
    map_smul' r f := by
      change Functor.whiskerLeft (Over.map i.unop).op (smulRawHom X M N U.unop r f) =
        smulRawHom X M N V.unop (X.presheaf.map i r)
          (show RawHom X M N V.unop from Functor.whiskerLeft (Over.map i.unop).op f)
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
      ((CategoryTheory.presheafHom M.val.presheaf N.val.presheaf).map_id U) f
  map_comp i j := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    exact ConcreteCategory.congr_hom
      ((CategoryTheory.presheafHom M.val.presheaf N.val.presheaf).map_comp i j) f

/-- The sheaf of all additive maps, with scalars acting in the target. -/
def rawSheaf : SheafOfModules.{u} X.ringCatSheaf where
  val := rawPresheaf X M N
  isSheaf := by
    apply Presheaf.isSheaf_of_isSheaf_comp (Opens.grothendieckTopology X)
      (s := CategoryTheory.forget AddCommGrpCat)
    change Presheaf.IsSheaf (Opens.grothendieckTopology X)
      (CategoryTheory.presheafHom M.val.presheaf N.val.presheaf)
    exact N.isSheaf.hom M.val.presheaf

/-- Every component commutes with multiplication by sections of its structure ring. -/
def IsLinear (U : X.Opens) (f : RawHom X M N U) : Prop :=
  ∀ (V : (Over U)ᵒᵖ) (r : Γ(X, V.unop.left)) (s : M.val.obj (op V.unop.left)),
    f.app V (r • s) = r • (show N.val.obj (op V.unop.left) from f.app V s)

/-- The `Γ(X, U)`-submodule of additive natural transformations with structure-linear
components on every open below `U`. -/
def linearSubmodule (U : X.Opens) : Submodule Γ(X, U) (RawHom X M N U) where
  carrier := IsLinear X M N U
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
def linearPresheaf : (rawPresheaf X M N).Submodule where
  obj U := linearSubmodule X M N U.unop
  map {U V} i := by
    intro f hf W r s
    exact hf (op ((Over.map i.unop).obj W.unop)) r s

theorem linearity_isLocal {U : X.Opensᵒᵖ} (f : (rawSheaf X M N).val.obj U)
    (hf : (linearPresheaf X M N).toSubfunctor.sieveOfSection f ∈
      (Opens.grothendieckTopology X) U.unop) :
    f ∈ (linearPresheaf X M N).obj U := by
  intro V r s
  apply N.isSheaf.isSeparated _ _
    ((Opens.grothendieckTopology X).pullback_stable V.unop.hom hf)
  intro W j hj
  let i : Over.mk (j ≫ V.unop.hom) ⟶ V.unop := Over.homMk j
  have hlin := hj (op (Over.mk (𝟙 W))) (X.presheaf.map j.op r) (M.val.map j.op s)
  change f.app (op (Over.mk (j ≫ V.unop.hom)))
      (X.presheaf.map j.op r • M.val.map j.op s) =
    X.presheaf.map j.op r • (show N.val.obj (op W) from
      f.app (op (Over.mk (j ≫ V.unop.hom))) (M.val.map j.op s)) at hlin
  change N.val.map j.op (f.app V (r • s)) =
    N.val.map j.op (r • (show N.val.obj (op V.unop.left) from f.app V s))
  rw [N.val.map_smul]
  have hnat (t : M.val.obj (op V.unop.left)) := NatTrans.naturality_apply f i.op t
  change ∀ t : M.val.obj (op V.unop.left),
    f.app (op (Over.mk (j ≫ V.unop.hom))) (M.val.map j.op t) = N.val.map j.op (f.app V t) at hnat
  rw [← hnat, M.val.map_smul]
  exact hlin.trans (congrArg (fun a : N.val.obj (op W) => X.presheaf.map j.op r • a) (hnat s))

/-- Actual sheaf of structure-linear homomorphisms on all open restrictions. -/
def sheaf : SheafOfModules.{u} X.ringCatSheaf :=
  (show (rawSheaf X M N).Submodule from
    { toSubmodule := linearPresheaf X M N
      isSheaf := by intro U f hf; exact linearity_isLocal X M N f hf }).toSheafOfModules

/-- Sections are precisely actual linear sheaf morphisms on the open restriction. -/
def sectionHomEquiv (U : X.Opens) :
    (sheaf X M N).val.obj (op U) ≃ (M.over U ⟶ N.over U) where
  toFun s := ⟨_root_.PresheafOfModules.homMk s.val (by
    intro V r m
    exact s.property V r m)⟩
  invFun f := ⟨(_root_.PresheafOfModules.toPresheaf (X.ringCatSheaf.over U).obj).map f.val, by
    intro V r m
    exact (f.val.app V).hom.map_smul r m⟩
  left_inv s := by apply Subtype.ext; rfl
  right_inv f := by ext V m; rfl

variable {M N} {M' N' : SheafOfModules.{u} X.ringCatSheaf}

/-- Map internal homs over `U` by precomposition with `a` and postcomposition with `b`. -/
def overHomMap (U : X.Opens) (a : M'.over U ⟶ M.over U) (b : N.over U ⟶ N'.over U) :
    (sheaf X M N).over U ⟶ (sheaf X M' N').over U where
  val.app V := ModuleCat.ofHom {
    toFun s := ⟨Functor.whiskerLeft (Over.map V.unop.hom).op
        ((_root_.PresheafOfModules.toPresheaf _).map a.val) ≫ s.val ≫
      Functor.whiskerLeft (Over.map V.unop.hom).op
        ((_root_.PresheafOfModules.toPresheaf _).map b.val), by
      intro W r m
      change b.val.app (op ((Over.map V.unop.hom).obj W.unop))
          (s.val.app W (a.val.app (op ((Over.map V.unop.hom).obj W.unop)) (r • m))) =
        r • b.val.app (op ((Over.map V.unop.hom).obj W.unop))
          (s.val.app W (a.val.app (op ((Over.map V.unop.hom).obj W.unop)) m))
      rw [(a.val.app _).hom.map_smul, s.property, (b.val.app _).hom.map_smul]⟩
    map_add' s t := by
      apply Subtype.ext
      change (_ : RawHom X M' N' V.unop.left) = _
      ext W m
      let T := op ((Over.map V.unop.hom).obj W.unop)
      change b.val.app T (s.val.app W (a.val.app T m) + t.val.app W (a.val.app T m)) = _
      exact (b.val.app T).hom.map_add _ _
    map_smul' r s := by
      apply Subtype.ext
      change (_ : RawHom X M' N' V.unop.left) = _
      ext W m
      let T := op ((Over.map V.unop.hom).obj W.unop)
      change b.val.app T (X.presheaf.map W.unop.hom.op r • s.val.app W (a.val.app T m)) =
        X.presheaf.map W.unop.hom.op r • b.val.app T (s.val.app W (a.val.app T m))
      exact (b.val.app T).hom.map_smul _ _ }
  val.naturality {V W} i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    apply Subtype.ext
    change (_ : RawHom X M' N' W.unop.left) = _
    ext T m
    rfl

theorem overIso_hom_inv_apply {U : X.Opens} (e : M.over U ≅ M'.over U)
    (V : (Over U)ᵒᵖ) (m : (M.over U).val.obj V) :
    e.inv.val.app V (e.hom.val.app V m) = m := by
  exact congrArg (fun z : M.over U ⟶ M.over U => z.val.app V m) e.hom_inv_id

/-- Transport internal homs along isomorphisms of the source and target over `U`.
The forward map precomposes with `e.inv` and postcomposes with `f.hom`. -/
def overHomIso (U : X.Opens) (e : M.over U ≅ M'.over U) (f : N.over U ≅ N'.over U) :
    (sheaf X M N).over U ≅ (sheaf X M' N').over U where
  hom := overHomMap X U e.inv f.hom
  inv := overHomMap X U e.hom f.inv
  hom_inv_id := by
    apply SheafOfModules.hom_ext
    ext V : 1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    apply Subtype.ext
    change (_ : RawHom X M N V.unop.left) = _
    ext W m
    let T := op ((Over.map V.unop.hom).obj W.unop)
    change f.inv.val.app T (f.hom.val.app T
      (s.val.app W (e.inv.val.app T (e.hom.val.app T m)))) = s.val.app W m
    rw [overIso_hom_inv_apply X e, overIso_hom_inv_apply X f]
  inv_hom_id := by
    apply SheafOfModules.hom_ext
    ext V : 1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    apply Subtype.ext
    change (_ : RawHom X M' N' V.unop.left) = _
    ext W m
    let T := op ((Over.map V.unop.hom).obj W.unop)
    change f.hom.val.app T (f.inv.val.app T
      (s.val.app W (e.hom.val.app T (e.inv.val.app T m)))) = s.val.app W m
    have he := overIso_hom_inv_apply X e.symm T m
    have hf := overIso_hom_inv_apply X f.symm T (s.val.app W m)
    change e.hom.val.app T (e.inv.val.app T m) = m at he
    change f.hom.val.app T (f.inv.val.app T (s.val.app W m)) = s.val.app W m at hf
    rw [he]
    exact hf

variable (N)
/-- A local section of `N` defines a map from the structure sheaf by scalar multiplication
with its restrictions on every subopen. -/
def sectionFromUnit (U : X.Opens) (m : N.val.obj (op U)) :
    (sheaf X (SheafOfModules.unit X.ringCatSheaf) N).val.obj (op U) :=
  ⟨{
    app V := AddCommGrpCat.ofHom (LinearMap.toSpanSingleton Γ(X, V.unop.left)
      (N.val.obj (op V.unop.left)) (N.val.map V.unop.hom.op m)).toAddMonoidHom
    naturality {V W} i := by
      ext r
      change X.presheaf.map i.unop.left.op r • N.val.map W.unop.hom.op m =
        N.val.map i.unop.left.op (r • N.val.map V.unop.hom.op m)
      rw [N.val.map_smul]
      congr 1
      rw [← N.val.map_comp_apply, ← op_comp, Over.w i.unop]
  }, by
    intro V r s
    change Γ(X, V.unop.left) at s
    change (r * s) • N.val.map V.unop.hom.op m = r • (s • N.val.map V.unop.hom.op m)
    exact mul_smul _ _ _⟩

/-- The `Γ(X, U)`-linear equivalence between maps from the structure sheaf and sections of
`N`, given by evaluation at `1` and inverse scalar multiplication on all subopens. -/
def unitSourceSectionsEquiv (U : X.Opens) :
    (sheaf X (SheafOfModules.unit X.ringCatSheaf) N).val.obj (op U) ≃ₗ[Γ(X, U)]
      N.val.obj (op U) where
  toFun s := s.val.app (op (Over.mk (𝟙 U))) (1 : Γ(X, U))
  invFun m := sectionFromUnit X N U m
  left_inv s := by
    apply Subtype.ext
    change (_ : RawHom X (SheafOfModules.unit X.ringCatSheaf) N U) = _
    ext V r
    change Γ(X, V.unop.left) at r
    change r • N.val.map V.unop.hom.op (s.val.app (op (Over.mk (𝟙 U)))
      (1 : Γ(X, U))) = s.val.app V r
    have h := s.property V r (1 : Γ(X, V.unop.left))
    have hn := NatTrans.naturality_apply s.val (Over.homMk V.unop.hom :
      V.unop ⟶ Over.mk (𝟙 U)).op (1 : Γ(X, U))
    change s.val.app V (X.presheaf.map V.unop.hom.op 1) =
      N.val.map V.unop.hom.op (s.val.app (op (Over.mk (𝟙 U))) (1 : Γ(X, U))) at hn
    rw [map_one] at hn
    rw [← hn]
    simpa only [smul_eq_mul, mul_one] using h.symm
  right_inv m := by
    simp only [sheafCompose_obj_obj, Functor.comp_obj, CommRingCat.forgetToRingCat_obj,
      SheafOfModules.unit_val, Functor.op_obj, Over.forget_obj, Over.mk_left,
      _root_.PresheafOfModules.presheaf_obj_coe, Lean.Elab.WF.paramLet, sectionFromUnit,
      LinearMap.toSpanSingleton, Functor.comp_map, CommRingCat.forgetToRingCat_map_hom,
      Over.mk_hom, op_id, _root_.PresheafOfModules.map_id, ModuleCat.restrictScalarsId'_inv_app,
      ConcreteCategory.hom_ofHom, LinearMap.toAddMonoidHom_coe, LinearMap.coe_smulRight]
    exact one_smul Γ(X, U) m
  map_add' s t := rfl
  map_smul' r s := by
    change X.presheaf.map (𝟙 U).op r • (show N.val.obj (op U) from
      s.val.app (op (Over.mk (𝟙 U))) (1 : Γ(X, U))) = r • (show N.val.obj (op U) from
        s.val.app (op (Over.mk (𝟙 U))) (1 : Γ(X, U)))
    simp

/-- Evaluation at `1` identifies the internal hom from the structure sheaf with `N`
as an actual module-sheaf isomorphism. -/
def unitSourceIso : sheaf X (SheafOfModules.unit X.ringCatSheaf) N ≅ N :=
  (SheafOfModules.fullyFaithfulForget X.ringCatSheaf).preimageIso <|
    _root_.PresheafOfModules.isoMk (fun U => (unitSourceSectionsEquiv X N U.unop).toModuleIso) (by
      intro U V i
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro s
      have hn := NatTrans.naturality_apply s.val
        (Over.homMk i.unop : Over.mk i.unop ⟶ Over.mk (𝟙 U.unop)).op (1 : Γ(X, U.unop))
      change s.val.app (op (Over.mk i.unop)) (X.presheaf.map i 1) =
        N.val.map i (s.val.app (op (Over.mk (𝟙 U.unop))) (1 : Γ(X, U.unop))) at hn
      change s.val.app (op (Over.mk i.unop)) (1 : Γ(X, V.unop)) =
        N.val.map i (s.val.app (op (Over.mk (𝟙 U.unop))) (1 : Γ(X, U.unop)))
      simpa only [map_one] using hn)
end AlgebraicGeometry.Scheme.Modules.InternalHom
