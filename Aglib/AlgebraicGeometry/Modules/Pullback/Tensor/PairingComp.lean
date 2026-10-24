/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Pairing

/-!
# Pulled-back pairings and maps into the first factor

Let `p : X ⟶ P` be a morphism of schemes, `ε : N ⊗ L ⟶ 𝒪_P` a pairing and `a : N' ⟶ N`. The
pullback of the pairing `(a ⊗ 𝟙) ≫ ε` is `p^* a ⊗ 𝟙` followed by the pullback of `ε`
(`pullbackPairing_tensorSheafMap_comp`), by the naturality of the tensor comparison
(`pullbackTensorMapIso_inv_naturality`). No hypothesis on `p` or the modules is needed.

Consumer: the closed subscheme `C_T ⊆ P^n_A ×_{Spec A} T` cut out by sections of `𝒪(r)`
(`HilbertScheme/ClosedSubscheme/Containment`).
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X P : Scheme.{u}} (p : X ⟶ P) {N N' L : P.Modules}

/-- **The pullback of a pairing precomposed in the first factor**: for `a : N' ⟶ N`,
`pullbackPairing p ((a ⊗ 𝟙) ≫ ε) = (p^* a ⊗ 𝟙) ≫ pullbackPairing p ε`. -/
theorem pullbackPairing_tensorSheafMap_comp (a : N' ⟶ N)
    (ε : (show P.Modules from tensorSheaf P N L) ⟶
      (show P.Modules from SheafOfModules.unit P.ringCatSheaf)) :
    pullbackPairing p (tensorSheafMap P a (𝟙 L) ≫ ε) =
      tensorSheafMap X ((pullback p).map a) (𝟙 ((pullback p).obj L)) ≫ pullbackPairing p ε := by
  have h := pullbackTensorMapIso_inv_naturality p a (𝟙 L)
  rw [CategoryTheory.Functor.map_id] at h
  rw [pullbackPairing, pullbackPairing, CategoryTheory.Functor.map_comp, ← Category.assoc,
    ← Category.assoc, h]
  simp only [Category.assoc]

end AlgebraicGeometry.Scheme.Modules
