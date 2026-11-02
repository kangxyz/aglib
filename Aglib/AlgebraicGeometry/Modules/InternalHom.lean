/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Aglib.Algebra.Category.ModuleCat.Sheaf.InternalHom.Functor

/-!
# The structure-linear Hom sheaf

The Hom sheaf specializes the generic ringed-site construction of linear
natural transformations on slices. Its carrier universe is unchanged here:
the site and module carriers lie in `u`, and the site morphisms are small.
Its sections are actual restricted module-sheaf morphisms.
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
/-- Additive natural transformations on the original open slice. -/
abbrev RawHom (U : X.Opens) : Type u :=
  SheafOfModules.InternalHom.RawHom
    (C := X.Opens) (J := Opens.grothendieckTopology X) X.sheaf M N U

instance rawHomTargetModule (U : X.Opens) (V : (Over U)ᵒᵖ) :
    Module Γ(X, V.unop.left) (((Over.forget U).op ⋙ N.val.presheaf).obj V) :=
  (N.val.obj (op V.unop.left)).isModule

/-- The generic target scalar action on the original scheme sections. -/
abbrev smulRawHom (U : X.Opens) (r : Γ(X, U)) (f : RawHom X M N U) : RawHom X M N U :=
  SheafOfModules.InternalHom.smulRawHom X.sheaf M N U r f

instance rawHomSMul (U : X.Opens) : SMul Γ(X, U) (RawHom X M N U) :=
  SheafOfModules.InternalHom.PresheafSource.rawHomSMul X.sheaf M.val N U

/-- The component formula for the original target scalar action. -/
theorem smulRawHom_apply (U : X.Opens) (r : Γ(X, U)) (f : RawHom X M N U)
    (V : (Over U)ᵒᵖ) (s : M.val.obj (op V.unop.left)) :
    (r • f).app V s = X.presheaf.map V.unop.hom.op r • f.app V s := rfl

instance rawHomModule (U : X.Opens) : Module Γ(X, U) (RawHom X M N U) :=
  SheafOfModules.InternalHom.PresheafSource.rawHomModule X.sheaf M.val N U

instance rawHomModuleOp (U : X.Opensᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj U) (RawHom X M N U.unop) := rawHomModule X M N U.unop

/-- The generic additive Hom presheaf on the original Zariski site. -/
abbrev rawPresheaf : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj :=
  SheafOfModules.InternalHom.rawPresheaf X.sheaf M N

/-- The generic additive Hom sheaf on the original Zariski site. -/
abbrev rawSheaf : SheafOfModules.{u} X.ringCatSheaf :=
  SheafOfModules.InternalHom.rawSheaf X.sheaf M N

/-- Every component is linear over its original structure ring. -/
abbrev IsLinear (U : X.Opens) (f : RawHom X M N U) : Prop :=
  SheafOfModules.InternalHom.IsLinear X.sheaf M N U f

/-- The original scalar submodule of componentwise linear transformations. -/
abbrev linearSubmodule (U : X.Opens) : Submodule Γ(X, U) (RawHom X M N U) :=
  SheafOfModules.InternalHom.linearSubmodule X.sheaf M N U

/-- The subpresheaf of componentwise structure-linear transformations. -/
abbrev linearPresheaf : (rawPresheaf X M N).Submodule :=
  SheafOfModules.InternalHom.linearPresheaf X.sheaf M N

/-- The arbitrary-site locality theorem on the original Zariski site. -/
theorem linearity_isLocal {U : X.Opensᵒᵖ} (f : (rawSheaf X M N).val.obj U)
    (hf : (linearPresheaf X M N).toSubfunctor.sieveOfSection f ∈
      (Opens.grothendieckTopology X) U.unop) :
    f ∈ (linearPresheaf X M N).obj U :=
  SheafOfModules.InternalHom.linearity_isLocal X.sheaf M N f hf

/-- Actual ring-linear Hom, specialized from the generic construction. -/
abbrev sheaf : SheafOfModules.{u} X.ringCatSheaf :=
  SheafOfModules.InternalHom.sheaf X.sheaf M N

/-- The original Hom sheaf is the actual generic constructor for the structure sheaf. -/
theorem sheaf_eq_generic :
    sheaf X M N = SheafOfModules.InternalHom.sheaf X.sheaf M N := rfl

/-- Sections are actual linear sheaf morphisms on the original open restriction. -/
abbrev sectionHomEquiv (U : X.Opens) :
    (sheaf X M N).val.obj (op U) ≃ (M.over U ⟶ N.over U) :=
  SheafOfModules.InternalHom.sectionHomEquiv X.sheaf M N U

/-- The original section comparison is the actual generic comparison. -/
theorem sectionHomEquiv_eq_generic (U : X.Opens) :
    sectionHomEquiv X M N U = SheafOfModules.InternalHom.sectionHomEquiv X.sheaf M N U := rfl

/-- The section comparison retains the original component map. -/
theorem sectionHomEquiv_apply_app (U : X.Opens) (s : (sheaf X M N).val.obj (op U))
    (V : (Over U)ᵒᵖ) (m : M.val.obj (op V.unop.left)) :
    (sectionHomEquiv X M N U s).val.app V m = s.val.app V m := rfl

/-- The original restriction is literal whiskering along the slice functor. -/
theorem sheaf_map_val {U V : X.Opensᵒᵖ} (i : U ⟶ V)
    (s : (sheaf X M N).val.obj U) :
    ((sheaf X M N).val.map i s).val = Functor.whiskerLeft (Over.map i.unop).op s.val := rfl

variable {M N} {M' N' : SheafOfModules.{u} X.ringCatSheaf}

/-- The generic map by precomposition and postcomposition on the original open restriction. -/
abbrev overHomMap (U : X.Opens) (a : M'.over U ⟶ M.over U) (b : N.over U ⟶ N'.over U) :
    (sheaf X M N).over U ⟶ (sheaf X M' N').over U :=
  SheafOfModules.InternalHom.overHomMap X.sheaf U a b

/-- The original restricted Hom map is the generic map for the same actual arrows. -/
theorem overHomMap_eq_generic (U : X.Opens)
    (a : M'.over U ⟶ M.over U) (b : N.over U ⟶ N'.over U) :
    overHomMap X U a b = SheafOfModules.InternalHom.overHomMap X.sheaf U a b := rfl

theorem overIso_hom_inv_apply {U : X.Opens} (e : M.over U ≅ M'.over U)
    (V : (Over U)ᵒᵖ) (m : (M.over U).val.obj V) :
    e.inv.val.app V (e.hom.val.app V m) = m :=
  SheafOfModules.InternalHom.overIso_hom_inv_apply X.sheaf e V m

/-- The generic transport along the original source and target isomorphisms. -/
abbrev overHomIso (U : X.Opens) (e : M.over U ≅ M'.over U) (f : N.over U ≅ N'.over U) :
    (sheaf X M N).over U ≅ (sheaf X M' N').over U :=
  SheafOfModules.InternalHom.overHomIso X.sheaf U e f

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
    change Γ(X, V.unop.left) at r
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
