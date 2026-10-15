/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# Pullback and scalar extension of group schemes

Source: the base-change interface used by
`K2-018#prop:k2018-integrality-test`, `research/exposes/K2/018/expose.tex`,
at mathematical snapshot `e73d98b1b5c1e5abcdebf7d058e436d792b87982`, SHA256
`e716cfb3c6eaba82370c5b46b806df5705ad4583df0ed41b1a576e419f3bd299`.
The categorical constructions use mathlib revision
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

The generic interface allows a supplied group-object functor together with an
explicit underlying pullback comparison. Its canonical constructor is actual
scheme pullback lifted by `mapGrp`. Only that canonical constructor is given
the identity and composition natural isomorphisms below: these lift
`Over.pullbackId` and `Over.pullbackComp`, rather than asserting strict equality
of chosen pullbacks. Component, scheme-projection and multiplicative point-fibre
formulas expose the comparison maps.

The projected formulas are explicit rewrite lemmas, including reassociated
versions. The underlying-map simp rules already normalize their left sides
to canonical `Over` maps; their proofs then compute those maps and use the
ordinary pullback projection laws.

Field scalar extension is a specialization of this single generic interface
along the contravariant map `Spec F₂ ⟶ Spec F₁`. This module supplies neither
local-field embeddings nor identifications of an isogeny with a local
representative. No isogeny extension or discriminant criterion is proved here.
Each declaration's source pointer refers to this auxiliary categorical subset
on the module's mathematical source basis.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.Group.BaseChange

universe u
attribute [local instance] Over.cartesianMonoidalCategory
variable {S T U R : Scheme.{u}}

/-- General group-scheme base change with its underlying pullback comparison,
for `K2-018#prop:k2018-integrality-test`, on the module source basis. -/
structure GroupSchemeBaseChange (f : S ⟶ T) where
  /-- The supplied group-object functor in the auxiliary base-change subset
  of `K2-018#prop:k2018-integrality-test`, on the module source basis. -/
  functor : Grp (Over T) ⥤ Grp (Over S)
  /-- The explicit underlying pullback comparison in the auxiliary subset
  of `K2-018#prop:k2018-integrality-test`, on the module source basis. -/
  underlying : functor ⋙ Grp.forget (Over S) ≅
    Grp.forget (Over T) ⋙ Over.pullback f

/-- Actual scheme pullback lifted to group objects, for the auxiliary subset
of `K2-018#prop:k2018-integrality-test`, on the module source basis. -/
def groupSchemeBaseChange (f : S ⟶ T) : GroupSchemeBaseChange f where
  functor := (Over.pullback f).mapGrp
  underlying := Iso.refl _

/-- The canonical functor formula for the auxiliary base-change subset of
`K2-018#prop:k2018-integrality-test`, on the module source basis. -/
theorem groupSchemeBaseChange_functor (f : S ⟶ T) :
    (groupSchemeBaseChange f).functor = (Over.pullback f).mapGrp := rfl

/-- The underlying object is actual pullback, in the auxiliary subset of
`K2-018#prop:k2018-integrality-test`, on the module source basis. -/
@[simp] theorem groupSchemeBaseChange_obj_X (f : S ⟶ T) (A : Grp (Over T)) :
    ((groupSchemeBaseChange f).functor.obj A).X = (Over.pullback f).obj A.X := rfl

/-- The underlying scheme is the fibre product, in the auxiliary subset of
`K2-018#prop:k2018-integrality-test`, on the module source basis. -/
@[simp] theorem groupSchemeBaseChange_obj_left (f : S ⟶ T) (A : Grp (Over T)) :
    ((groupSchemeBaseChange f).functor.obj A).X.left = Limits.pullback A.X.hom f := rfl

/-- The structural morphism is the second projection, in the auxiliary subset
of `K2-018#prop:k2018-integrality-test`, on the module source basis. -/
@[simp] theorem groupSchemeBaseChange_obj_hom (f : S ⟶ T) (A : Grp (Over T)) :
    ((groupSchemeBaseChange f).functor.obj A).X.hom = Limits.pullback.snd A.X.hom f := rfl

/-- The underlying morphism is actual pullback, in the auxiliary subset of
`K2-018#prop:k2018-integrality-test`, on the module source basis. -/
@[simp] theorem groupSchemeBaseChange_map_hom_hom (f : S ⟶ T)
    {A B : Grp (Over T)} (h : A ⟶ B) :
    ((groupSchemeBaseChange f).functor.map h).hom.hom =
      (Over.pullback f).map h.hom.hom := rfl

/-- The actual scheme-map formula, in the auxiliary base-change subset of
`K2-018#prop:k2018-integrality-test`, on the module source basis. -/
theorem groupSchemeBaseChange_map_left (f : S ⟶ T)
    {A B : Grp (Over T)} (h : A ⟶ B) :
    ((groupSchemeBaseChange f).functor.map h).hom.hom.left =
      Limits.pullback.lift (Limits.pullback.fst A.X.hom f ≫ h.hom.hom.left)
        (Limits.pullback.snd A.X.hom f) (by simp [Limits.pullback.condition]) := rfl

/-- The first projection of an extended morphism, in the auxiliary subset of
`K2-018#prop:k2018-integrality-test`, on the module source basis. -/
@[reassoc] theorem groupSchemeBaseChange_map_left_fst (f : S ⟶ T)
    {A B : Grp (Over T)} (h : A ⟶ B) :
    ((groupSchemeBaseChange f).functor.map h).hom.hom.left ≫ Limits.pullback.fst B.X.hom f =
      Limits.pullback.fst A.X.hom f ≫ h.hom.hom.left := by
  simp

/-- The second projection of an extended morphism, in the auxiliary subset of
`K2-018#prop:k2018-integrality-test`, on the module source basis. -/
@[reassoc] theorem groupSchemeBaseChange_map_left_snd (f : S ⟶ T)
    {A B : Grp (Over T)} (h : A ⟶ B) :
    ((groupSchemeBaseChange f).functor.map h).hom.hom.left ≫ Limits.pullback.snd B.X.hom f =
      Limits.pullback.snd A.X.hom f := by
  simp

/-- The strict forgetful comparison for the canonical functor, in the auxiliary
subset of `K2-018#prop:k2018-integrality-test`, on the module source basis. -/
theorem groupSchemeBaseChange_forget (f : S ⟶ T) :
    (groupSchemeBaseChange f).functor ⋙ Grp.forget (Over S) =
      Grp.forget (Over T) ⋙ Over.pullback f := rfl

/-- The forward underlying comparison is identity, in the auxiliary subset
of `K2-018#prop:k2018-integrality-test`, on the module source basis. -/
@[simp] theorem groupSchemeBaseChange_underlying_hom_app (f : S ⟶ T)
    (A : Grp (Over T)) :
    (groupSchemeBaseChange f).underlying.hom.app A = 𝟙 _ := rfl

/-- The inverse underlying comparison is identity, in the auxiliary subset
of `K2-018#prop:k2018-integrality-test`, on the module source basis. -/
@[simp] theorem groupSchemeBaseChange_underlying_inv_app (f : S ⟶ T)
    (A : Grp (Over T)) :
    (groupSchemeBaseChange f).underlying.inv.app A = 𝟙 _ := rfl

/-- Pullback along the identity is naturally isomorphic to identity on group
schemes, in the auxiliary subset of `K2-018#prop:k2018-integrality-test`, on the
module source basis. This lifts the actual pullback natural isomorphism. -/
def groupSchemeBaseChangeId :
    (groupSchemeBaseChange (𝟙 S)).functor ≅ 𝟭 (Grp (Over S)) :=
  Functor.mapGrpNatIso Over.pullbackId ≪≫ Functor.mapGrpIdIso

/-- The forward identity component forgets to mathlib's pullback comparison,
in the auxiliary subset of `K2-018#prop:k2018-integrality-test`, on the source basis. -/
@[simp] theorem groupSchemeBaseChangeId_hom_app_hom_hom (A : Grp (Over S)) :
    (groupSchemeBaseChangeId.hom.app A).hom.hom = Over.pullbackId.hom.app A.X := by
  change _ ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- The inverse identity component forgets to mathlib's pullback comparison,
in the auxiliary subset of `K2-018#prop:k2018-integrality-test`, on the source basis. -/
@[simp] theorem groupSchemeBaseChangeId_inv_app_hom_hom (A : Grp (Over S)) :
    (groupSchemeBaseChangeId.inv.app A).hom.hom = Over.pullbackId.inv.app A.X := by
  change 𝟙 _ ≫ _ = _
  exact Category.id_comp _

/-- The identity component is the first scheme projection, in the auxiliary
subset of `K2-018#prop:k2018-integrality-test`, on the module source basis. -/
theorem groupSchemeBaseChangeId_hom_app_left (A : Grp (Over S)) :
    (groupSchemeBaseChangeId.hom.app A).hom.hom.left =
      Limits.pullback.fst A.X.hom (𝟙 S) := by
  rw [groupSchemeBaseChangeId_hom_app_hom_hom]
  simp [Over.pullbackId, conjugateEquiv_apply_app, Over.mapId]

/-- The inverse identity component is the diagonal lift, in the auxiliary
subset of `K2-018#prop:k2018-integrality-test`, on the module source basis. -/
theorem groupSchemeBaseChangeId_inv_app_left (A : Grp (Over S)) :
    (groupSchemeBaseChangeId.inv.app A).hom.hom.left =
      Limits.pullback.lift (𝟙 A.X.left) A.X.hom (by simp) := by
  rw [groupSchemeBaseChangeId_inv_app_hom_hom]
  apply Limits.pullback.hom_ext <;>
    simp [Over.pullbackId, conjugateEquiv_apply_app, Over.mapId, Category.assoc]

/-- Naturality of the forward identity comparison, in the auxiliary subset
of `K2-018#prop:k2018-integrality-test`, on the module source basis. -/
@[reassoc] theorem groupSchemeBaseChangeId_hom_naturality
    {A B : Grp (Over S)} (h : A ⟶ B) :
    (groupSchemeBaseChange (𝟙 S)).functor.map h ≫ groupSchemeBaseChangeId.hom.app B =
      groupSchemeBaseChangeId.hom.app A ≫ h :=
  groupSchemeBaseChangeId.hom.naturality h

/-- Naturality of the inverse identity comparison, in the auxiliary subset
of `K2-018#prop:k2018-integrality-test`, on the module source basis. -/
@[reassoc] theorem groupSchemeBaseChangeId_inv_naturality
    {A B : Grp (Over S)} (h : A ⟶ B) :
    h ≫ groupSchemeBaseChangeId.inv.app B =
      groupSchemeBaseChangeId.inv.app A ≫ (groupSchemeBaseChange (𝟙 S)).functor.map h :=
  groupSchemeBaseChangeId.inv.naturality h

/-- Pullback along a composite is naturally isomorphic to successive group
pullback, in the auxiliary subset of `K2-018#prop:k2018-integrality-test`, on the
module source basis. The order is contravariant. -/
def groupSchemeBaseChangeComp (f : S ⟶ T) (g : T ⟶ U) :
    (groupSchemeBaseChange (f ≫ g)).functor ≅
      (groupSchemeBaseChange g).functor ⋙ (groupSchemeBaseChange f).functor :=
  Functor.mapGrpNatIso (Over.pullbackComp f g) ≪≫ Functor.mapGrpCompIso

/-- The forward composition component forgets to actual pullback coherence,
in the auxiliary subset of `K2-018#prop:k2018-integrality-test`, on the source basis. -/
@[simp] theorem groupSchemeBaseChangeComp_hom_app_hom_hom (f : S ⟶ T)
    (g : T ⟶ U) (A : Grp (Over U)) :
    ((groupSchemeBaseChangeComp f g).hom.app A).hom.hom =
      (Over.pullbackComp f g).hom.app A.X := by
  change _ ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- The inverse composition component forgets to actual pullback coherence,
in the auxiliary subset of `K2-018#prop:k2018-integrality-test`, on the source basis. -/
@[simp] theorem groupSchemeBaseChangeComp_inv_app_hom_hom (f : S ⟶ T)
    (g : T ⟶ U) (A : Grp (Over U)) :
    ((groupSchemeBaseChangeComp f g).inv.app A).hom.hom =
      (Over.pullbackComp f g).inv.app A.X := by
  change 𝟙 _ ≫ _ = _
  exact Category.id_comp _

/-- The composition comparison retains the original scheme projection, in the
auxiliary subset of `K2-018#prop:k2018-integrality-test`, on the source basis. -/
@[reassoc] theorem groupSchemeBaseChangeComp_hom_left_fst_fst
    (f : S ⟶ T) (g : T ⟶ U) (A : Grp (Over U)) :
    ((groupSchemeBaseChangeComp f g).hom.app A).hom.hom.left ≫
      Limits.pullback.fst (Limits.pullback.snd A.X.hom g) f ≫ Limits.pullback.fst A.X.hom g =
        Limits.pullback.fst A.X.hom (f ≫ g) := by
  rw [groupSchemeBaseChangeComp_hom_app_hom_hom]
  simp [Over.pullbackComp, conjugateEquiv_apply_app, Over.mapComp,
    Adjunction.comp_unit_app, Category.assoc]

/-- The composition comparison retains the new base projection, in the
auxiliary subset of `K2-018#prop:k2018-integrality-test`, on the source basis. -/
@[reassoc] theorem groupSchemeBaseChangeComp_hom_left_snd
    (f : S ⟶ T) (g : T ⟶ U) (A : Grp (Over U)) :
    ((groupSchemeBaseChangeComp f g).hom.app A).hom.hom.left ≫
      Limits.pullback.snd (Limits.pullback.snd A.X.hom g) f =
        Limits.pullback.snd A.X.hom (f ≫ g) := by
  rw [groupSchemeBaseChangeComp_hom_app_hom_hom]
  simp [Over.pullbackComp, conjugateEquiv_apply_app, Over.mapComp,
    Adjunction.comp_unit_app, Category.assoc]

/-- The middle-base projection of the composition comparison, in the
auxiliary subset of `K2-018#prop:k2018-integrality-test`, on the source basis. -/
@[reassoc] theorem groupSchemeBaseChangeComp_hom_left_fst_snd
    (f : S ⟶ T) (g : T ⟶ U) (A : Grp (Over U)) :
    ((groupSchemeBaseChangeComp f g).hom.app A).hom.hom.left ≫
      Limits.pullback.fst (Limits.pullback.snd A.X.hom g) f ≫ Limits.pullback.snd A.X.hom g =
        Limits.pullback.snd A.X.hom (f ≫ g) ≫ f := by
  rw [Limits.pullback.condition]
  exact groupSchemeBaseChangeComp_hom_left_snd_assoc f g A f

/-- The inverse composition comparison retains the original scheme
projection, in the auxiliary subset of `K2-018#prop:k2018-integrality-test`,
on the module source basis. -/
@[reassoc] theorem groupSchemeBaseChangeComp_inv_left_fst
    (f : S ⟶ T) (g : T ⟶ U) (A : Grp (Over U)) :
    ((groupSchemeBaseChangeComp f g).inv.app A).hom.hom.left ≫
      Limits.pullback.fst A.X.hom (f ≫ g) =
        Limits.pullback.fst (Limits.pullback.snd A.X.hom g) f ≫ Limits.pullback.fst A.X.hom g := by
  rw [← groupSchemeBaseChangeComp_hom_left_fst_fst f g A]
  have h :
      ((groupSchemeBaseChangeComp f g).inv.app A).hom.hom.left ≫
        ((groupSchemeBaseChangeComp f g).hom.app A).hom.hom.left = 𝟙 _ :=
    congrArg (fun k => k.hom.hom.left) ((groupSchemeBaseChangeComp f g).inv_hom_id_app A)
  rw [← Category.assoc, ← Category.assoc, h]
  simp

/-- The inverse composition comparison retains the new base projection, in the
auxiliary subset of `K2-018#prop:k2018-integrality-test`, on the source basis. -/
@[reassoc] theorem groupSchemeBaseChangeComp_inv_left_snd
    (f : S ⟶ T) (g : T ⟶ U) (A : Grp (Over U)) :
    ((groupSchemeBaseChangeComp f g).inv.app A).hom.hom.left ≫
      Limits.pullback.snd A.X.hom (f ≫ g) =
        Limits.pullback.snd (Limits.pullback.snd A.X.hom g) f := by
  rw [← groupSchemeBaseChangeComp_hom_left_snd f g A]
  have h :
      ((groupSchemeBaseChangeComp f g).inv.app A).hom.hom.left ≫
        ((groupSchemeBaseChangeComp f g).hom.app A).hom.hom.left = 𝟙 _ :=
    congrArg (fun k => k.hom.hom.left) ((groupSchemeBaseChangeComp f g).inv_hom_id_app A)
  rw [← Category.assoc, h]
  simp

/-- Naturality of the forward composition comparison on group morphisms, in
the auxiliary subset of `K2-018#prop:k2018-integrality-test`, on the source basis. -/
@[reassoc] theorem groupSchemeBaseChangeComp_hom_naturality (f : S ⟶ T)
    (g : T ⟶ U) {A B : Grp (Over U)} (h : A ⟶ B) :
    (groupSchemeBaseChange (f ≫ g)).functor.map h ≫
        (groupSchemeBaseChangeComp f g).hom.app B =
      (groupSchemeBaseChangeComp f g).hom.app A ≫
        (groupSchemeBaseChange f).functor.map ((groupSchemeBaseChange g).functor.map h) :=
  (groupSchemeBaseChangeComp f g).hom.naturality h

/-- Naturality of the inverse composition comparison on group morphisms, in
the auxiliary subset of `K2-018#prop:k2018-integrality-test`, on the source basis. -/
@[reassoc] theorem groupSchemeBaseChangeComp_inv_naturality (f : S ⟶ T)
    (g : T ⟶ U) {A B : Grp (Over U)} (h : A ⟶ B) :
    (groupSchemeBaseChange f).functor.map ((groupSchemeBaseChange g).functor.map h) ≫
        (groupSchemeBaseChangeComp f g).inv.app B =
      (groupSchemeBaseChangeComp f g).inv.app A ≫
        (groupSchemeBaseChange (f ≫ g)).functor.map h :=
  (groupSchemeBaseChangeComp f g).inv.naturality h

/-- Actual pullback identifies point groups multiplicatively, for any
scheme-valued point, in the auxiliary subset of
`K2-018#prop:k2018-integrality-test`, on the module source basis. -/
def pullbackFiberMulEquiv (f : S ⟶ T) (x : R ⟶ S) (A : Grp (Over T)) :
    (Over.mk (x ≫ f) ⟶ A.X) ≃*
      (Over.mk x ⟶ ((groupSchemeBaseChange f).functor.obj A).X) where
  __ := (Over.mapPullbackAdj f).homEquiv (Over.mk x) A.X
  map_mul' p q := by
    let : GrpObj ((Over.pullback f).obj A.X) := ((Over.pullback f).mapGrp.obj A).grp
    change (Over.mapPullbackAdj f).unit.app (Over.mk x) ≫
        (Over.pullback f).map (p * q) =
      ((Over.mapPullbackAdj f).unit.app (Over.mk x) ≫ (Over.pullback f).map p) *
        ((Over.mapPullbackAdj f).unit.app (Over.mk x) ≫ (Over.pullback f).map q)
    rw [(Over.pullback f).map_mul, MonObj.comp_mul]

/-- The forward point-fibre equivalence is the actual pullback lift, in the
auxiliary subset of `K2-018#prop:k2018-integrality-test`, on the source basis. -/
theorem pullbackFiberMulEquiv_apply_left (f : S ⟶ T) (x : R ⟶ S)
    (A : Grp (Over T)) (p : Over.mk (x ≫ f) ⟶ A.X) :
    (pullbackFiberMulEquiv f x A p).left =
      Limits.pullback.lift p.left x (by exact p.w) := by
  simp only [pullbackFiberMulEquiv, Over.mapPullbackAdj, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

/-- The transported point has its original scheme projection, in the
auxiliary subset of `K2-018#prop:k2018-integrality-test`, on the source basis. -/
@[reassoc] theorem pullbackFiberMulEquiv_apply_left_fst
    (f : S ⟶ T) (x : R ⟶ S) (A : Grp (Over T))
    (p : Over.mk (x ≫ f) ⟶ A.X) :
    (pullbackFiberMulEquiv f x A p).left ≫ Limits.pullback.fst A.X.hom f = p.left := by
  rw [pullbackFiberMulEquiv_apply_left]
  simp

/-- The transported point has its prescribed base projection, in the
auxiliary subset of `K2-018#prop:k2018-integrality-test`, on the source basis. -/
@[reassoc] theorem pullbackFiberMulEquiv_apply_left_snd
    (f : S ⟶ T) (x : R ⟶ S) (A : Grp (Over T))
    (p : Over.mk (x ≫ f) ⟶ A.X) :
    (pullbackFiberMulEquiv f x A p).left ≫ Limits.pullback.snd A.X.hom f = x := by
  rw [pullbackFiberMulEquiv_apply_left]
  simp

/-- The inverse point-fibre equivalence is the first projection, in the
auxiliary subset of `K2-018#prop:k2018-integrality-test`, on the source basis. -/
theorem pullbackFiberMulEquiv_symm_apply_left (f : S ⟶ T) (x : R ⟶ S)
    (A : Grp (Over T))
    (q : Over.mk x ⟶ ((groupSchemeBaseChange f).functor.obj A).X) :
    ((pullbackFiberMulEquiv f x A).symm q).left =
      q.left ≫ Limits.pullback.fst A.X.hom f := rfl

/-- Naturality of multiplicative point-fibre transport under group morphisms,
in the auxiliary subset of `K2-018#prop:k2018-integrality-test`, on the source basis. -/
theorem pullbackFiberMulEquiv_naturality (f : S ⟶ T) (x : R ⟶ S)
    {A B : Grp (Over T)} (h : A ⟶ B) (p : Over.mk (x ≫ f) ⟶ A.X) :
    pullbackFiberMulEquiv f x B (p ≫ h.hom.hom) =
      pullbackFiberMulEquiv f x A p ≫ ((groupSchemeBaseChange f).functor.map h).hom.hom :=
  by
    ext1
    apply Limits.pullback.hom_ext
    · simp only [Over.comp_left, Category.assoc, groupSchemeBaseChange_map_left_fst]
      rw [pullbackFiberMulEquiv_apply_left_fst f x B (p ≫ h.hom.hom),
        pullbackFiberMulEquiv_apply_left_fst_assoc f x A p h.hom.hom.left]
      rfl
    · simp only [Over.comp_left, Category.assoc, groupSchemeBaseChange_map_left_snd]
      rw [pullbackFiberMulEquiv_apply_left_snd f x B (p ≫ h.hom.hom),
        pullbackFiberMulEquiv_apply_left_snd f x A p]

/-- Equal base morphisms induce isomorphic canonical group pullbacks, in the
auxiliary subset of `K2-018#prop:k2018-integrality-test`, on the source basis. -/
def groupSchemeBaseChangeCongr {f g : S ⟶ T} (h : f = g) :
    (groupSchemeBaseChange f).functor ≅ (groupSchemeBaseChange g).functor :=
  eqToIso (congrArg (fun k => (groupSchemeBaseChange k).functor) h)

section Fields
variable {F₁ F₂ F₃ : Type u} [Field F₁] [Field F₂] [Field F₃]

/-- The contravariant scheme map for field scalar extension, in the auxiliary
subset of `K2-018#prop:k2018-integrality-test`, on the module source basis. -/
abbrev scalarExtensionMap (embedding : F₁ →+* F₂) :
    Spec (CommRingCat.of F₂) ⟶ Spec (CommRingCat.of F₁) :=
  Spec.map (CommRingCat.ofHom embedding)

/-- Field scalar extension specializes the single generic base-change
interface, in the auxiliary subset of `K2-018#prop:k2018-integrality-test`,
on the module source basis. This is an abbreviation, not a second record. -/
abbrev GroupSchemeScalarExtension (embedding : F₁ →+* F₂) :=
  GroupSchemeBaseChange (scalarExtensionMap embedding)

/-- Canonical field scalar extension is the canonical group pullback, in the
auxiliary subset of `K2-018#prop:k2018-integrality-test`, on the source basis. -/
def groupSchemeScalarExtension (embedding : F₁ →+* F₂) :
    GroupSchemeScalarExtension embedding :=
  groupSchemeBaseChange (scalarExtensionMap embedding)

/-- Identity field scalar extension is naturally identity on group schemes,
in the auxiliary subset of `K2-018#prop:k2018-integrality-test`, on the source basis. -/
def groupSchemeScalarExtensionId :
    (groupSchemeScalarExtension (RingHom.id F₁)).functor ≅
      𝟭 (Grp (Over (Spec (CommRingCat.of F₁)))) :=
  groupSchemeBaseChangeCongr (by exact Spec.map_id _) ≪≫ groupSchemeBaseChangeId

/-- Successive field embeddings give successive canonical scalar extensions,
in the auxiliary subset of `K2-018#prop:k2018-integrality-test`, on the source basis. -/
def groupSchemeScalarExtensionComp (i : F₁ →+* F₂) (j : F₂ →+* F₃) :
    (groupSchemeScalarExtension (j.comp i)).functor ≅
      (groupSchemeScalarExtension i).functor ⋙ (groupSchemeScalarExtension j).functor :=
  groupSchemeBaseChangeCongr (Spec.map_comp (CommRingCat.ofHom i) (CommRingCat.ofHom j)) ≪≫
    groupSchemeBaseChangeComp (scalarExtensionMap j) (scalarExtensionMap i)

end Fields
end AlgebraicGeometry.Scheme.Group.BaseChange
