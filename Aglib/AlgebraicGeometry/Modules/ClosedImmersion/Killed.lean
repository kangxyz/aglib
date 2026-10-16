/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pushforward.Stalk

/-!
# Ideal annihilation of actual module sheaves

An ideal-sheaf datum acts on the original affine sections of every module
sheaf. Its annihilation property uses those actual actions, without a
quasicoherence or finiteness hypothesis. The original pushforward of every
module is annihilated by the actual scheme-map kernel ideal. At an inducing
map, the original stalk comparison also retains the actual scalar action
and therefore the kernel-annihilation formula on original pushforward stalks.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- An ideal-sheaf datum annihilates a module sheaf when its actual affine
section ideals annihilate all original module sections. -/
def killedByIdealSheaf (I : X.IdealSheafData) : ObjectProperty X.Modules :=
  fun M => ∀ (U : X.affineOpens) (a : Γ(X, U.1)), a ∈ I.ideal U →
    ∀ m : Γ(M, U.1), a • m = 0

/-- Actual affine annihilation is containment in the original section-module
annihilator, with no finite-generation premise. -/
theorem killedByIdealSheaf_iff_le_annihilator (I : X.IdealSheafData) (M : X.Modules) :
    killedByIdealSheaf I M ↔
      ∀ U : X.affineOpens, I.ideal U ≤ Module.annihilator Γ(X, U.1) Γ(M, U.1) := by
  simp only [killedByIdealSheaf, SetLike.le_def, Module.mem_annihilator]

/-- Annihilation by an ideal implies annihilation by each smaller ideal. -/
theorem killedByIdealSheaf_of_le {I J : X.IdealSheafData} (hIJ : I ≤ J)
    {M : X.Modules} (hM : killedByIdealSheaf J M) : killedByIdealSheaf I M :=
  fun U a ha m => hM U a (hIJ U ha) m

/-- The actual annihilation condition is invariant under original module
isomorphisms. -/
theorem killedByIdealSheaf_of_iso (I : X.IdealSheafData) {M N : X.Modules}
    (e : M ≅ N) (hM : killedByIdealSheaf I M) : killedByIdealSheaf I N := by
  intro U a ha m
  have hm : e.hom.app U.1 (e.inv.app U.1 m) = m := by
    have h := congrArg (fun f => (f.app U.1) m) e.inv_hom_id
    exact h
  rw [← hm, ← Hom.app_smul, hM U a ha, map_zero]

instance killedByIdealSheaf_isClosedUnderIsomorphisms (I : X.IdealSheafData) :
    (killedByIdealSheaf I).IsClosedUnderIsomorphisms where
  of_iso e hM := killedByIdealSheaf_of_iso I e hM

/-- Every original pushforward module is annihilated by the actual scheme
map kernel. This holds for every scheme morphism, without a closed-immersion
or quasicoherence premise. -/
theorem killedByIdealSheaf_pushforward_ker (f : X ⟶ Y) (M : X.Modules) :
    killedByIdealSheaf f.ker ((Scheme.Modules.pushforward f).obj M) := by
  intro U a ha m
  have hfa : (f.app U.1).hom a = 0 := f.ideal_ker_le U ha
  change (f.app U.1).hom a • (show Γ(M, f ⁻¹ᵁ U.1) from m) = 0
  rw [hfa, zero_smul]

/-- The original inducing-map stalk comparison retains the actual
restriction of scalars along the original structure-sheaf stalk map. -/
theorem pushforwardModuleStalkIso_smul (f : X ⟶ Y) (hf : Topology.IsInducing f)
    (x : X) (M : X.Modules) (a : Y.presheaf.stalk (f x))
    (m : (moduleStalk Y (f x)).obj ((Scheme.Modules.pushforward f).obj M)) :
    (pushforwardModuleStalkIso f hf x).hom.app M (a • m) =
      f.stalkMap x a • (show (moduleStalk X x).obj M from
        (pushforwardModuleStalkIso f hf x).hom.app M m) :=
  ((pushforwardModuleStalkIso f hf x).hom.app M).hom.map_smul a m

/-- A kernel element of the original stalk ring map annihilates the actual
pushforward stalk whenever the underlying map is inducing. -/
theorem pushforward_stalk_smul_eq_zero_of_isInducing (f : X ⟶ Y)
    (hf : Topology.IsInducing f) (x : X) (M : X.Modules)
    (a : Y.presheaf.stalk (f x)) (ha : f.stalkMap x a = 0)
    (m : (moduleStalk Y (f x)).obj ((Scheme.Modules.pushforward f).obj M)) :
    a • m = 0 := by
  apply ((pushforwardModuleStalkIso f hf x).app M).toLinearEquiv.injective
  change (pushforwardModuleStalkIso f hf x).hom.app M (a • m) =
    (pushforwardModuleStalkIso f hf x).hom.app M 0
  rw [pushforwardModuleStalkIso_smul, ha, zero_smul, map_zero]

/-- Closed pushforward satisfies the original stalk-kernel annihilation
formula for every coefficient module sheaf. -/
theorem closedImmersion_pushforward_stalk_smul_eq_zero (f : X ⟶ Y)
    [IsClosedImmersion f] (x : X) (M : X.Modules)
    (a : Y.presheaf.stalk (f x)) (ha : f.stalkMap x a = 0)
    (m : (moduleStalk Y (f x)).obj ((Scheme.Modules.pushforward f).obj M)) :
    a • m = 0 :=
  pushforward_stalk_smul_eq_zero_of_isInducing f f.isClosedEmbedding.isInducing x M a ha m

end AlgebraicGeometry.Scheme.Modules
