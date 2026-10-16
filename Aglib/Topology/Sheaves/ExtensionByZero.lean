/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.KanExtension.ClosedImage
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Over

/-!
# Exact extension by zero for abelian sheaves on an open subspace

The native restriction functor has a native left adjoint, constructed by
opposite left Kan extension along the inclusion of opens and sheafification.
That Kan extension preserves monomorphisms because the image consists of
opens contained in the specified open. Sheafification preserves them as well,
so the actual extension-by-zero left adjoint is exact.

No scheme, coefficient module, quasicoherence or compactness premise is used.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace TopCat.Sheaf

universe u

variable {X : TopCat.{u}} (U : Opens X)

/-- The native left adjoint of restriction to an open subspace. -/
def extensionByZero :
    CategoryTheory.Sheaf (Opens.grothendieckTopology U) AddCommGrpCat.{u} ⥤
      CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  (U.sheafRestrict (C := AddCommGrpCat.{u})).leftAdjoint

/-- The original native extension-by-zero/restriction adjunction. -/
def extensionByZeroRestrictAdjunction :
    extensionByZero U ⊣ U.sheafRestrict (C := AddCommGrpCat.{u}) :=
  Adjunction.ofIsRightAdjoint _

instance extensionByZero_isLeftAdjoint : (extensionByZero U).IsLeftAdjoint :=
  (extensionByZeroRestrictAdjunction U).isLeftAdjoint

/-- The native construction is opposite Kan extension followed by sheafification. -/
def extensionByZeroConstructionIso :
    extensionByZero U ≅
      sheafToPresheaf (Opens.grothendieckTopology U) AddCommGrpCat.{u} ⋙
        U.isOpenEmbedding.functor.op.lan ⋙
          presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} := by
  letI : U.isOpenEmbedding.functor.IsContinuous (Opens.grothendieckTopology U)
      (Opens.grothendieckTopology X) := U.isOpenEmbedding.functor_isContinuous
  exact Functor.sheafPullbackConstruction.sheafPullbackIso U.isOpenEmbedding.functor
    AddCommGrpCat.{u} (Opens.grothendieckTopology U) (Opens.grothendieckTopology X)

/-- Native extension by zero preserves the actual monomorphisms of abelian sheaves. -/
instance extensionByZero_preservesMonomorphisms : (extensionByZero U).PreservesMonomorphisms where
  preserves {F G} f hf := by
    let := hf
    let : Mono U.inclusion' := (TopCat.mono_iff_injective _).mpr Subtype.val_injective
    have hclosed : ∀ {V : Opens X} {W : Opens U},
        (V ⟶ U.isOpenEmbedding.functor.obj W) →
          ∃ W', Nonempty (U.isOpenEmbedding.functor.obj W' ≅ V) := by
      intro V W i
      have hV : V ≤ U := by
        intro x hx
        obtain ⟨y, _, rfl⟩ := i.le hx
        exact y.property
      refine ⟨(Opens.map U.inclusion').obj V, ⟨eqToIso ?_⟩⟩
      rw [Opens.functor_map_eq_inf, inf_eq_left.mpr hV]
    let : (U.isOpenEmbedding.functor.op.lan
        (H := AddCommGrpCat.{u})).PreservesMonomorphisms :=
      ⟨fun a _ => Functor.lan_op_map_mono_of_closed_under_domains
        U.isOpenEmbedding.functor hclosed a⟩
    let L := sheafToPresheaf (Opens.grothendieckTopology U) AddCommGrpCat.{u} ⋙
      U.isOpenEmbedding.functor.op.lan ⋙
        presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}
    have : Mono (L.map f) := inferInstance
    have he : (extensionByZero U).map f =
        (extensionByZeroConstructionIso U).hom.app F ≫ L.map f ≫
          (extensionByZeroConstructionIso U).inv.app G := by
      rw [← NatTrans.naturality_assoc, Iso.hom_inv_id_app, Category.comp_id]
    rw [he]
    infer_instance

instance extensionByZero_additive : (extensionByZero U).Additive := by
  let := preservesBinaryBiproducts_of_preservesBinaryCoproducts (extensionByZero U)
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- The original abelian extension-by-zero functor is exact. -/
instance extensionByZero_preservesFiniteLimits : PreservesFiniteLimits (extensionByZero U) := by
  have := Functor.preservesHomology_of_preservesMonos_and_cokernels (extensionByZero U)
  exact Functor.preservesFiniteLimits_of_preservesHomology _

/-- Restriction to an open subspace preserves finite colimits of actual abelian sheaves. -/
instance openRestrict_preservesFiniteColimits :
    PreservesFiniteColimits (U.sheafRestrict (C := AddCommGrpCat.{u})) := by
  let : (pullback AddCommGrpCat.{u} U.inclusion').IsLeftAdjoint :=
    (pullbackPushforwardAdjunction AddCommGrpCat.{u} U.inclusion').isLeftAdjoint
  exact preservesFiniteColimits_of_natIso
    (U.isOpenEmbedding.sheafPullbackIso AddCommGrpCat.{u})

end TopCat.Sheaf
