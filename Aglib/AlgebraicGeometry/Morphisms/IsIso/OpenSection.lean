/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# An open section of a separated integral source

Source: `R5Lab.Aglib.AlgebraicGeometry.Morphisms.IsIso.OpenSection`.
R5 packet revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256: `7d9441ad71a4a9a7988dd3640d8b302ae920091d1ec82afe2d389ee9516894b5`.
Actual objects, maps, universes and hypotheses are retained.
Native declaration ownership replaces the source application namespaces.
-/

@[expose] public section

/- Component: OpenSection; declaration bodies preserved. -/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
namespace AlgebraicGeometry.Scheme
universe u

/-- A nonempty open section of a separated map from an integral scheme exhausts
the inverse image of its domain. Thus the actual restricted map is an isomorphism. -/
theorem isIso_restrict_of_open_section {Y X : Scheme.{u}} [IsIntegral Y]
    (p : Y ⟶ X) [IsSeparated p] (U : X.Opens) [Nonempty U]
    (s : U.toScheme ⟶ Y) [IsOpenImmersion s] (hs : s ≫ p = U.ι) :
    IsIso (p ∣_ U) := by
  let V := p ⁻¹ᵁ U
  let t : U.toScheme ⟶ V.toScheme :=
    (isPullback_morphismRestrict p U).lift (𝟙 _) s (by simpa using hs.symm)
  have ht : t ≫ V.ι = s := (isPullback_morphismRestrict p U).lift_snd _ _ _
  have htp : t ≫ p ∣_ U = 𝟙 _ := (isPullback_morphismRestrict p U).lift_fst _ _ _
  let : Nonempty V.toScheme := Nonempty.map t inferInstance
  let : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  let : IsOpenImmersion (t ≫ V.ι) := ht ▸ inferInstance
  let : IsOpenImmersion t := IsOpenImmersion.of_comp t V.ι
  let : IsClosedImmersion (t ≫ p ∣_ U) := htp ▸ inferInstance
  let : IsClosedImmersion t := IsClosedImmersion.of_comp t (p ∣_ U)
  have hd : DenseRange t := t.isOpenMap.denseRange_of_isPreirreducibleSpace
  have hr : Set.range t = Set.univ := by
    rw [← t.isClosedEmbedding.isClosed_range.closure_eq]
    exact hd.closure_range
  let : Surjective t := ⟨Set.range_eq_univ.mp hr⟩
  let : IsIso t := isIso_of_isClosedImmersion_of_surjective t
  let : IsIso (t ≫ p ∣_ U) := htp ▸ inferInstance
  exact IsIso.of_isIso_comp_left (f := t) (p ∣_ U)
end AlgebraicGeometry.Scheme
end
