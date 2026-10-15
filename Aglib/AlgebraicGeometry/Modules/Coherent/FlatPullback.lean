/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Pullback
public import Aglib.AlgebraicGeometry.Modules.Coherent.FinitePresentation
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FlatPullback

/-!
# Flat exact pullback of coherent sheaves

Flatness supplies actual ambient short-exact-sequence preservation. The
restricted functor retains the locally Noetherian source and target.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open CategoryTheory.ExactCategory
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules.Coherent

/-- Actual coherent pullback is exact under genuine scheme-theoretic flatness. -/
def coherentExactPullback {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y) [Flat f] :
    ExactFunctor (coherentExactStructure Y) (coherentExactStructure X) where
  toFunctor := coherentPullback f
  map_conflation S hS := by
    apply (coherent_shortExact_iff X (S.map (coherentPullback f))).mpr
    change ((S.map (finiteTypeSheavesToModules Y)).map (Scheme.Modules.pullback f)).ShortExact
    have : (S.map (finiteTypeSheavesToModules Y)).X₁.IsQuasicoherent := coherent_obj_quasicoherent
      S.X₁
    have : (S.map (finiteTypeSheavesToModules Y)).X₂.IsQuasicoherent := coherent_obj_quasicoherent
      S.X₂
    exact shortExact_pullback_of_flat f ((coherent_shortExact_iff Y S).mp hS)

end AlgebraicGeometry.Scheme.Modules.Coherent
