/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Quotient.Descent
public import Aglib.AlgebraicGeometry.Modules.ClosedImmersion.Killed
public import Aglib.AlgebraicGeometry.Modules.Pullback.StalkUnit
public import Aglib.AlgebraicGeometry.Modules.Stalk.Reflection

/-!
# The original closed-immersion counit on actual stalks

The native pullback and pushforward stalk comparisons identify the original
geometric counit with the original scalar-extension counit. For a closed
immersion the scalar ring map is surjective, so this proves invertibility of
the actual geometric counit on every coefficient module sheaf. No
quasicoherence, finite generation or Noetherian hypothesis is used.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct ChangeOfRings

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- The original geometric unit becomes the original scalar-extension unit
under the original inducing-map and pullback stalk comparisons. -/
theorem pullbackPushforwardUnit_moduleStalk (f : X ⟶ Y)
    (hf : Topology.IsInducing f) (x : X) (M : Y.Modules) :
    (moduleStalk Y (f x)).map ((pullbackPushforwardAdjunction f).unit.app M) ≫
        (pushforwardModuleStalkIso f hf x).hom.app ((pullback f).obj M) ≫
        (ModuleCat.restrictScalars (f.stalkMap x).hom).map
          ((pullbackModuleStalkIso f x).hom.app M) =
      (ModuleCat.extendRestrictScalarsAdj (f.stalkMap x).hom).unit.app
        ((moduleStalk Y (f x)).obj M) := by
  ext m
  obtain ⟨U, hx, s, rfl⟩ := M.presheaf.exists_germ_eq m
  change (pullbackModuleStalkIso f x).hom.app M
      (pushforwardModuleStalkMap f x ((pullback f).obj M)
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f x)).map
          ((pullbackPushforwardAdjunction f).unit.app M).mapPresheaf
          (M.presheaf.germ U (f x) hx s))) =
    (1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (f x),(f.stalkMap x).hom]
      M.presheaf.germ U (f x) hx s
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply, pushforwardModuleStalkMap_germ]
  exact pullbackModuleStalkIso_unit_germ f x M U hx s

/-- The original geometric counit becomes the original scalar counit under
the original inducing-map and pullback stalk comparisons. -/
theorem pullbackPushforwardCounit_moduleStalk (f : X ⟶ Y)
    (hf : Topology.IsInducing f) (x : X) (M : X.Modules) :
    (moduleStalk X x).map ((pullbackPushforwardAdjunction f).counit.app M) =
      (pullbackModuleStalkIso f x).hom.app ((pushforward f).obj M) ≫
        (ModuleCat.extendScalars (f.stalkMap x).hom).map
          ((pushforwardModuleStalkIso f hf x).hom.app M) ≫
        (ModuleCat.extendRestrictScalarsAdj (f.stalkMap x).hom).counit.app
          ((moduleStalk X x).obj M) := by
  let A := (pushforward f).obj M
  let ε := (pullbackPushforwardAdjunction f).counit.app M
  let e := (pullbackModuleStalkIso f x).app A
  let t := (pushforwardModuleStalkIso f hf x).hom.app M
  let adj := ModuleCat.extendRestrictScalarsAdj (f.stalkMap x).hom
  apply (cancel_epi e.inv).mp
  change e.inv ≫ (moduleStalk X x).map ε =
    e.inv ≫ e.hom ≫ (ModuleCat.extendScalars (f.stalkMap x).hom).map t ≫
      adj.counit.app ((moduleStalk X x).obj M)
  rw [Iso.inv_hom_id_assoc]
  erw [← adj.homEquiv_counit]
  apply (adj.homEquiv _ _).injective
  erw [Equiv.apply_symm_apply]
  ext m
  rw [ModuleCat.extendRestrictScalarsAdj_homEquiv_apply]
  obtain ⟨U, hx, s, rfl⟩ := A.presheaf.exists_germ_eq m
  have he : e.inv
      ((1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (f x),(f.stalkMap x).hom]
        A.presheaf.germ U (f x) hx s) =
      ((pullback f).obj A).presheaf.germ (f ⁻¹ᵁ U) x hx
        (((pullbackPushforwardAdjunction f).unit.app A).app U s) := by
    rw [← pullbackModuleStalkIso_unit_germ f x A U hx s]
    exact ConcreteCategory.congr_hom e.hom_inv_id _
  change (moduleStalk X x).map ε
      (e.inv ((1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (f x),(f.stalkMap x).hom]
        A.presheaf.germ U (f x) hx s)) =
    pushforwardModuleStalkMap f x M (A.presheaf.germ U (f x) hx s)
  rw [he]
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map ε.mapPresheaf
      (((pullback f).obj A).presheaf.germ (f ⁻¹ᵁ U) x hx
        (((pullbackPushforwardAdjunction f).unit.app A).app U s)) = _
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply, pushforwardModuleStalkMap_germ]
  have h := congrArg (fun q => q.app U s)
    ((pullbackPushforwardAdjunction f).right_triangle_components M)
  exact congrArg (fun q => M.presheaf.germ (f ⁻¹ᵁ U) x hx q) h

/-- The original pullback/pushforward counit of a closed immersion is
invertible on every actual module sheaf. -/
theorem pullbackPushforwardCounit_isIso_of_closedImmersion (f : X ⟶ Y)
    [IsClosedImmersion f] (M : X.Modules) :
    IsIso ((pullbackPushforwardAdjunction f).counit.app M) := by
  apply isIso_of_moduleStalk
  intro x
  let := ModuleCat.extendRestrictScalarsAdj_counit_isIso_of_surjective
    (f.stalkMap x).hom (f.stalkMap_surjective x) ((moduleStalk X x).obj M)
  rw [pullbackPushforwardCounit_moduleStalk f f.isClosedEmbedding.isInducing x M]
  infer_instance

/-- Closed pushforward is fully faithful on all actual module sheaves,
using the original geometric counit. -/
def fullyFaithfulPushforwardOfClosedImmersion (f : X ⟶ Y) [IsClosedImmersion f] :
    (pushforward f).FullyFaithful := by
  let (M : X.Modules) := pullbackPushforwardCounit_isIso_of_closedImmersion f M
  let : IsIso (pullbackPushforwardAdjunction f).counit :=
    NatIso.isIso_of_isIso_app _
  exact (pullbackPushforwardAdjunction f).fullyFaithfulROfIsIsoCounit

end AlgebraicGeometry.Scheme.Modules
