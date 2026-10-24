/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.Monomorphism

/-!
# A closed subscheme and its image over a base

Let `j : X ⟶ Y` and `q : Y ⟶ T` be morphisms of schemes with `j ≫ q = p`, and let `I` be a closed
subscheme of `X` that is closed in `Y`: `I.subscheme ⟶ X ⟶ Y` is a closed immersion. Then `I` is
isomorphic over `Y` to its image `I.map j` (`Scheme.IdealSheafData.mapSubschemeIso`,
`IdealSheaf/Monomorphism`), hence also over `T`:

* `Scheme.IdealSheafData.range_map_subschemeι_comp`: `I.map j` and `I` have the same image in `T`;
* `Scheme.IdealSheafData.map_subschemeι_comp_iff`: for a property `P` of morphisms that respects
  isomorphisms (for example flat, proper or surjective), `(I.map j).subscheme ⟶ Y ⟶ T` has `P`
  if and only if `I.subscheme ⟶ X ⟶ T` has `P`.

No hypothesis on `j`, `q` or the schemes is needed. Present consumer: the Hilbert functor of an
immersed scheme `Y ⊆ P^n_A` (`HilbertScheme/Coproduct/Functor`), where `j` is the base change
`Y ×_{Spec A} T ⟶ P^n_A ×_{Spec A} T` of the immersion and `q` the projection to `T`.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y T : Scheme.{u}} (I : X.IdealSheafData) {j : X ⟶ Y} {q : Y ⟶ T} {p : X ⟶ T}
  (hp : j ≫ q = p) [IsClosedImmersion (I.subschemeι ≫ j)]

include hp in
/-- The isomorphism `I.subscheme ≅ (I.map j).subscheme` is compatible with the maps to `T`. -/
theorem mapSubschemeIso_hom_subschemeι_comp :
    (I.mapSubschemeIso j).hom ≫ (I.map j).subschemeι ≫ q = I.subschemeι ≫ p := by
  rw [mapSubschemeIso_hom_subschemeι_assoc, hp]

include hp in
/-- **A closed subscheme and its image have the same image in the base**: if `I` is closed in `Y`
and `j ≫ q = p`, the images of `(I.map j).subscheme ⟶ T` and `I.subscheme ⟶ T` agree. -/
theorem range_map_subschemeι_comp :
    Set.range ((I.map j).subschemeι ≫ q) = Set.range (I.subschemeι ≫ p) := by
  rw [← I.mapSubschemeIso_hom_subschemeι_comp hp]
  ext t
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨(I.mapSubschemeIso j).inv x, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  · rintro ⟨x, rfl⟩
    exact ⟨(I.mapSubschemeIso j).hom x, (Scheme.Hom.comp_apply _ _ x).symm⟩

include hp in
/-- **A closed subscheme and its image have the same properties over the base**: if `I` is closed
in `Y` and `j ≫ q = p`, then for a property `P` of morphisms that respects isomorphisms,
`(I.map j).subscheme ⟶ T` has `P` exactly when `I.subscheme ⟶ T` has `P`. -/
theorem map_subschemeι_comp_iff (P : MorphismProperty Scheme.{u}) [P.RespectsIso] :
    P ((I.map j).subschemeι ≫ q) ↔ P (I.subschemeι ≫ p) := by
  rw [← I.mapSubschemeIso_hom_subschemeι_comp hp,
    P.cancel_left_of_respectsIso (I.mapSubschemeIso j).hom]

end AlgebraicGeometry.Scheme.IdealSheafData
