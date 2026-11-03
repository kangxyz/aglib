/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.FlatMorphism
public import Mathlib.CategoryTheory.Functor.EpiMono

/-!
# Original pointwise epimorphisms under module-sheaf pullback

The existing pullback/stalk natural isomorphism identifies the actual map with
extension of scalars along the original stalk homomorphism. Its native left
adjoint preserves epimorphisms. No flatness, quasicoherence or finiteness is used.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- An epimorphism at the original image stalk remains epi after the actual
pullback at the selected source point. No flatness or quasicoherence is used. -/
theorem epi_moduleStalk_pullback_of_epi_moduleStalk
    {Z X : Scheme.{u}} (g : Z ⟶ X) (z : Z)
    {M N : X.Modules} (φ : M ⟶ N)
    [Epi ((moduleStalk X (g z)).map φ)] :
    Epi ((moduleStalk Z z).map ((pullback g).map φ)) := by
  let e := pullbackModuleStalkIso g z
  change Epi ((pullback g ⋙ moduleStalk Z z).map φ)
  apply (epi_comp_iff_of_isIso _ (e.hom.app N)).mp
  rw [e.hom.naturality]
  change Epi (e.hom.app M ≫ (ModuleCat.extendScalars (g.stalkMap z).hom).map
    ((moduleStalk X (g z)).map φ))
  infer_instance

end AlgebraicGeometry.Scheme.Modules
