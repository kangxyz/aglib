/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Module-sheaf pullback along a scheme isomorphism

The inverse functor is the original pullback along the inverse morphism.
Native composition, congruence, and identity comparisons supply both
quasi-inverse isomorphisms.
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

universe u
variable {X Y : Scheme.{u}}

/-- Pullback along an isomorphism is an equivalence on actual module sheaves. -/
instance isEquivalence_pullback_of_isIso (f : X ⟶ Y) [IsIso f] :
    (pullback f).IsEquivalence := by
  let e := asIso f
  exact Functor.IsEquivalence.mk' (pullback e.inv)
    ((pullbackComp e.inv e.hom ≪≫ pullbackCongr e.inv_hom_id ≪≫ pullbackId Y).symm)
    (pullbackComp e.hom e.inv ≪≫ pullbackCongr e.hom_inv_id ≪≫ pullbackId X)

end AlgebraicGeometry.Scheme.Modules
