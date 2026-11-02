/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Topology.Connected.Clopen

/-!
# A rational section of a connected etale field scheme

The actual section is an etale monomorphism, hence an open immersion. Its
image is closed because it is a section over the one-point field spectrum;
no global separatedness assumption on arbitrary etale morphisms is used.
Connectedness makes that nonempty open and closed image the whole scheme.
The original section and structure morphism are therefore inverse.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {X : Scheme.{u}} [PreconnectedSpace X]
  (p : X ⟶ Spec (.of k)) [Etale p] (s : Spec (.of k) ⟶ X)
  (hs : s ≫ p = 𝟙 _)

include hs in
/-- A rational section of a connected etale scheme over a field is an
isomorphism. The field need not be algebraically closed. -/
theorem isIso_section_of_etale_of_preconnected : IsIso s := by
  have : Etale (s ≫ p) := by rw [hs]; infer_instance
  have : Etale s := Etale.of_comp s p
  have : IsClosedImmersion s := isClosedImmersion_of_comp_eq_id p s hs
  have : IsOpenImmersion s := IsOpenImmersion.of_flat_of_mono s
  have hr : IsClopen (Set.range s) :=
    ⟨s.isClosedEmbedding.isClosed_range, s.isOpenEmbedding.isOpenMap.isOpen_range⟩
  have hsurj : Function.Surjective s := Set.range_eq_univ.mp
    (hr.eq_univ ⟨s (IsLocalRing.closedPoint k), Set.mem_range_self _⟩)
  have : Epi s.base := ConcreteCategory.epi_of_surjective _ hsurj
  exact IsOpenImmersion.isIso s

include hs in
/-- The original structure morphism followed by its section is the identity. -/
theorem comp_section_eq_id_of_etale_of_preconnected : p ≫ s = 𝟙 X := by
  have := isIso_section_of_etale_of_preconnected p s hs
  apply (cancel_epi s).mp
  rw [← Category.assoc, hs, Category.id_comp, Category.comp_id]

/-- The isomorphism to the original field spectrum, with the original
structure morphism and supplied rational section as its two maps. -/
def isoSpecOfEtaleOfPreconnected : X ≅ Spec (.of k) where
  hom := p
  inv := s
  hom_inv_id := comp_section_eq_id_of_etale_of_preconnected p s hs
  inv_hom_id := hs

@[simp]
theorem isoSpecOfEtaleOfPreconnected_hom :
    (isoSpecOfEtaleOfPreconnected p s hs).hom = p := rfl

@[simp]
theorem isoSpecOfEtaleOfPreconnected_inv :
    (isoSpecOfEtaleOfPreconnected p s hs).inv = s := rfl

end AlgebraicGeometry.Scheme
