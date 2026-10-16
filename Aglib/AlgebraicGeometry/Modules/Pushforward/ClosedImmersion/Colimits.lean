/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pushforward.ClosedImmersion
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits

/-!
# Colimits of actual closed pushforwards

Geometric pushforward along a topologically closed embedding preserves
colimits on all module sheaves. At an image point the original stalk
comparison is scalar restriction; off the image the whole stalk functor
is zero. Native joint stalk reflection then detects the original colimit
cocone. No quasicoherence or finiteness condition is required.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

universe u vJ uJ

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- A topologically closed embedding preserves any colimit whose image diagram
has a colimit. Both the original cocone and stalk maps are retained. -/
theorem pushforward_preservesColimit_of_isClosedEmbedding (f : X ⟶ Y)
    (hf : IsClosedEmbedding f) {J : Type uJ} [Category.{vJ} J] (K : J ⥤ X.Modules)
    [HasColimit (K ⋙ pushforward f)] : PreservesColimit K (pushforward f) := by
  have hstalk : JointlyReflectIsomorphisms (moduleStalk Y) :=
    ⟨fun p => isIso_of_moduleStalk p (fun _ => inferInstance)⟩
  have hpres (y : Y) : PreservesColimit K (pushforward f ⋙ moduleStalk Y y) := by
    by_cases hy : y ∈ Set.range f
    · obtain ⟨x, rfl⟩ := hy
      exact preservesColimit_of_natIso K
        (pushforwardModuleStalkIso f hf.isInducing x).symm
    · have hz : IsZero (pushforward f ⋙ moduleStalk Y y) :=
        Functor.isZero _ (fun M =>
          isZero_pushforward_moduleStalk_of_not_mem f hf.isClosed_range y hy M)
      let := Functor.preservesColimitsOfShape_of_isZero _ hz J
      infer_instance
  exact ⟨fun {c} hc => ⟨hstalk.jointlyReflectsColimit (fun y => by
    let := hpres y
    exact isColimitOfPreserves (pushforward f ⋙ moduleStalk Y y) hc)⟩⟩

/-- The actual closed-immersion pushforward preserves all small colimits of
module sheaves in the scheme universe. -/
instance pushforward_preservesColimits_of_closedImmersion (f : X ⟶ Y)
    [IsClosedImmersion f] : PreservesColimitsOfSize.{u, u} (pushforward f) where
  preservesColimitsOfShape {_J} _ :=
    { preservesColimit := fun {K} =>
        pushforward_preservesColimit_of_isClosedEmbedding f f.isClosedEmbedding K }

end AlgebraicGeometry.Scheme.Modules
