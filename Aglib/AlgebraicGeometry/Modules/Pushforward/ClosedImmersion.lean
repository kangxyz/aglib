/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pushforward.Stalk
public import Aglib.AlgebraicGeometry.Modules.Stalk.Reflection

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/ClosedPushforwardExactness.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general;
source ranges [[1, 83]]. Actual objects, maps and hypotheses are preserved.
-/

/-!
# Exact closed pushforward on arbitrary module sheaves

The scalar-compatible stalk comparison and off-image vanishing prove exactness
of the actual geometric pushforward, without quasicoherence or finiteness.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology
attribute [local instance] Abelian.hasFiniteBiproducts

open CategoryTheory.ExactCategory
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

/-- A topologically closed embedding preserves epimorphisms under actual pushforward. -/
theorem epi_pushforward_of_isClosedEmbedding {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : IsClosedEmbedding f) {M N : X.Modules} (p : M ⟶ N) [Epi p] :
    Epi ((Scheme.Modules.pushforward f).map p) := by
  apply epi_of_moduleStalk
  intro y
  by_cases hy : y ∈ Set.range f
  · obtain ⟨x, rfl⟩ := hy
    let e := pushforwardModuleStalkIso f hf.isInducing x
    have : Epi (e.inv.app M ≫ ((Scheme.Modules.pushforward f ⋙ moduleStalk Y (f x)).map p)) := by
      rw [← e.inv.naturality]
      infer_instance
    let : Epi (e.inv.app M ≫ (moduleStalk Y (f x)).map
      ((Scheme.Modules.pushforward f).map p)) := this
    exact epi_of_epi (e.inv.app M) ((moduleStalk Y (f x)).map
      ((Scheme.Modules.pushforward f).map p))
  · exact (isZero_pushforward_moduleStalk_of_not_mem f hf.isClosed_range y hy N).epi _

instance pushforward_preservesEpimorphisms_of_closedImmersion {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsClosedImmersion f] :
    (Scheme.Modules.pushforward f).PreservesEpimorphisms where
  preserves p hp := by
    let := hp
    exact epi_pushforward_of_isClosedEmbedding f f.isClosedEmbedding p

/-- The original closed pushforward is exact on all module sheaves. -/
instance pushforward_preservesFiniteColimits_of_closedImmersion {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsClosedImmersion f] :
    PreservesFiniteColimits (Scheme.Modules.pushforward f) := by
  have := Functor.preservesHomology_of_preservesEpis_and_kernels (Scheme.Modules.pushforward f)
  exact Functor.preservesFiniteColimits_of_preservesHomology (Scheme.Modules.pushforward f)

/-- Every original short exact sequence remains short exact under closed pushforward. -/
theorem shortExact_pushforward_of_closedImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsClosedImmersion f] {S : ShortComplex X.Modules} (hS : S.ShortExact) :
    (S.map (Scheme.Modules.pushforward f)).ShortExact := hS.map_of_exact _

/-- Exact pushforward on the actual ambient categories of scheme module sheaves. -/
def closedImmersionExactPushforward {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsClosedImmersion f] : ExactFunctor (sheafExactStructure X) (sheafExactStructure Y) where
  toFunctor := Scheme.Modules.pushforward f
  map_conflation _ h := h.map_of_exact _

end AlgebraicGeometry.Scheme.Modules
