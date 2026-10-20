/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Module.Automorphism.ScalarGraph
public import Aglib.RingTheory.Localization.LengthSurjective

/-!
Equality of the local lengths of the ORIGINAL tensor module and its
one-torus original module, through the surjective scalar graph pullback.
Neither a local-length identity nor a comparison map is an input.
-/
/-!
## Migration source

Native extraction from `lean/R5Lab/Aglib/Algebra/Module/Automorphism/ScalarGraphLengths.lean` at R5
revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`e1a5b95c4ec9317074fe4ddd8bc3164872969c3dec357440403233aeab40e611`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped _root_.TensorProduct
namespace Module.Automorphism.ScalarGraph
open Module.CommutingAutomorphisms CommutingAutomorphisms.LaurentSupport
universe u
variable {R : Type u} [CommRing R]

/-- Original weight-one carrier, tagged to fix the one-torus action. -/
def OneRealization (X : Object R) : Type u := X.carrier
instance oneRealizationAddCommGroup (X : Object R) :
    AddCommGroup (OneRealization X) := X.instAddCommGroup
instance oneRealizationBaseModule (X : Object R) :
    Module R (OneRealization X) := X.instModule
instance oneRealizationModule (X : Object R) :
    Module (OneLaurent R) (OneRealization X) :=
  Module.compHom X.carrier (oneRepresentation X).toRingHom

/-- The original one-variable realization localized at the prime ideal `q`. -/
abbrev OneLocalRealization (X : Object R) (q : Ideal (OneLaurent R)) [q.IsPrime] :=
  Localization.AtPrime q ⊗[OneLaurent R] OneRealization X

/-- The module length of the one-variable realization at the prime ideal `q`. -/
def oneAmbientLength (X : Object R) (q : Ideal (OneLaurent R)) [q.IsPrime] : ℕ∞ :=
  Module.length (Localization.AtPrime q) (OneLocalRealization X q)

/-- The same original graph-object carrier also carries the one-torus action. -/
@[instance_reducible]
def graphRealizationOneModule (X : Object R) (f : Rˣ) :
    Module (OneLaurent R) (CommutingAutomorphisms.Realization (graphObject X f)) :=
  Module.compHom X.carrier (oneRepresentation X).toRingHom

/-- The identity equivalence between the graph carrier and its one-variable realization. -/
def graphRealizationOneEquiv (X : Object R) (f : Rˣ) :
    letI := graphRealizationOneModule X f
    CommutingAutomorphisms.Realization (graphObject X f) ≃ₗ[OneLaurent R] OneRealization X := by
  letI := graphRealizationOneModule X f
  exact { toEquiv := Equiv.refl _, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

theorem graphRealizationTower (X : Object R) (f : Rˣ) :
    letI : Algebra (Laurent R) (OneLaurent R) := (graphMap f).toRingHom.toAlgebra
    letI := graphRealizationOneModule X f
    IsScalarTower (Laurent R) (OneLaurent R)
      (CommutingAutomorphisms.Realization (graphObject X f)) := by
  let : Algebra (Laurent R) (OneLaurent R) := (graphMap f).toRingHom.toAlgebra
  let := graphRealizationOneModule X f
  refine ⟨fun p q x => ?_⟩
  change oneRepresentation X (graphMap f p * q) x =
    representation (graphObject X f) p (oneRepresentation X q x)
  rw [map_mul, representation_graph]
  rfl

/-- The graph does not alter ANY original local module length, including
infinite lengths; no finiteness premise is needed for the identity. -/
theorem ambientLength_graph_eq_one (X : Object R) (f : Rˣ)
    (q : Ideal (OneLaurent R)) [q.IsPrime] :
    CommutingAutomorphisms.ambientLength (graphObject X f) (q.comap (graphMap f).toRingHom) =
      oneAmbientLength X q := by
  let : Algebra (Laurent R) (OneLaurent R) := (graphMap f).toRingHom.toAlgebra
  let := graphRealizationOneModule X f
  let := graphRealizationTower X f
  have h := _root_.Module.length_localization_of_surjective
    (CommutingAutomorphisms.Realization (graphObject X f)) (graphMap_surjective f) q
  let e := (graphRealizationOneEquiv X f).baseChange
    (OneLaurent R) (Localization.AtPrime q) _ _
  exact h.trans e.length_eq

/-- This equality concerns the ACTUAL right tensor module, using its genuine
intertwining tensor-unit isomorphism, at the literal graph prime. -/
theorem ambientLength_tensor_eq_one (X : Object R) (f : Rˣ)
    (q : Ideal (OneLaurent R)) [q.IsPrime] :
    CommutingAutomorphisms.ambientLength (X.tensor (Object.unit f))
        (q.comap (graphMap f).toRingHom) =
      oneAmbientLength X q :=
  (CommutingAutomorphisms.ambientLength_iso (tensorGraphIso X f)
    (q.comap (graphMap f).toRingHom)).trans (ambientLength_graph_eq_one X f q)

end Module.Automorphism.ScalarGraph
