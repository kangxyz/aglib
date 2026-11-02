/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Galois.FiberCompatibleComponent
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.GaloisInstances
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange

/-! # The actual connected component of an original Galois base change

The whole pullback may be disconnected. The supplied original connected
subcover is Galois and its deck group injects into the original deck group,
with the complete inclusion/translation law and original cardinal bound.
-/

@[expose] public noncomputable section

open CategoryTheory PreGaloisCategory

namespace AlgebraicGeometry.Scheme.FiniteEtale

universe u

/-- Restrict the original Galois deck action to the unchanged connected
subcover after arbitrary connected base change. -/
theorem baseChange_component_galois_and_aut_embedding
    {X S : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace S]
    (g : S ⟶ X) (Y : FiniteEtale X) [IsGalois Y]
    {Z : FiniteEtale S} [IsConnected Z]
    (i : Z ⟶ (baseChange g).obj Y) [Mono i] :
    IsGalois Z ∧ ∃ δ : Aut Z →* Aut Y, Function.Injective δ ∧
      (∀ σ, σ.hom ≫ i = i ≫ (Functor.mapAut Y (baseChange g) (δ σ)).hom) ∧
      Nat.card (Aut Z) ∣ Nat.card (Aut Y) := by
  let s := algebraicClosureResiduePoint S (Classical.choice (inferInstance : Nonempty S))
  exact component_galois_and_aut_embedding_of_fiberCompatible
    (fiberToFinite (s ≫ g)) (fiberToFinite s) (baseChange g)
    (fiberToFiniteBaseChangeIso g s) Y i

end AlgebraicGeometry.Scheme.FiniteEtale
