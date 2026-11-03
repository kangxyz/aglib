/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Stalk.SpecLocalRing

/-! # The original scalar retraction at a section's closed point

For a scheme over a local ring, an actual section makes its native closed-point
stalk map a retraction of the original structural scalar map. The complete
ring-map equality follows from the existing complete spectrum triangles.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u

/-- The canonical closed-point stalk map of an actual section retracts the
original structural scalar map, as an equality of whole ring maps. -/
theorem stalkClosedPointTo_comp_stalkScalar_of_section
    {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of R)) (s : Spec (.of R) ⟶ X)
    (hs : s ≫ p = 𝟙 (Spec (.of R))) :
    (stalkClosedPointTo s).hom.comp (p.stalkScalar (s (IsLocalRing.closedPoint R))) =
      RingHom.id R := by
  have h : CommRingCat.ofHom (p.stalkScalar (s (IsLocalRing.closedPoint R))) ≫
      stalkClosedPointTo s = 𝟙 (CommRingCat.of R) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_id,
      ← fromSpecStalk_comp_eq_spec_map_stalkScalar p,
      ← Category.assoc, Spec_stalkClosedPointTo_fromSpecStalk, hs]
  exact congrArg CommRingCat.Hom.hom h

/-- The original structural parameter evaluates to that same base parameter
under the original section's canonical local factorization. -/
@[simp] theorem stalkClosedPointTo_stalkScalar_of_section
    {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of R)) (s : Spec (.of R) ⟶ X)
    (hs : s ≫ p = 𝟙 (Spec (.of R))) (t : R) :
    (stalkClosedPointTo s).hom (p.stalkScalar (s (IsLocalRing.closedPoint R)) t) = t :=
  RingHom.congr_fun (stalkClosedPointTo_comp_stalkScalar_of_section p s hs) t

end AlgebraicGeometry.Scheme
