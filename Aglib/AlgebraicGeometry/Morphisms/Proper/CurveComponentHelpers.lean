/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.AffineCharts
public import Aglib.AlgebraicGeometry.Curves.Divisors.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Component restrictions and proper curve images

The restriction criterion proves an isomorphism on the actual open subscheme. Its function-field
consequence is the original generic stalk map. Proper dominant curve images retain integrality,
Noetherianity and dimension at most one; nondense images are actual closed singletons.

R5 revision `f8a3314ddecffcada2ec721d26d56a937bed9690`.
`Curves/LocalModels/CyclicModelComparison/PresentationComponents.lean`: source ranges [[161,
250]];
SHA-256 `77de4d0bb9d6dc601d58a053264a6559eaf17efb65cc7177282388708ff2cf7c`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.OverField.Curve
universe u
namespace AlgebraicGeometry.Scheme.Hom

theorem closed_component_isIso_restrict
    {D X Y : Scheme.{u}} [IsIntegral Y] (j : D ⟶ X) [IsClosedImmersion j]
    (f : X ⟶ Y) (V : Y.Opens) (hV : (V : Set Y).Nonempty) [IsIso (f ∣_ V)]
    (hcover : f ⁻¹' (V : Set Y) ⊆ Set.range j) : IsIso ((j ≫ f) ∣_ V) := by
  let : Nonempty V := ⟨⟨hV.choose, hV.choose_spec⟩⟩
  let : IsIntegral V := isIntegral_of_isOpenImmersion V.ι
  let : IsIntegral (f ⁻¹ᵁ V).toScheme := IsIntegral.of_isIso (inv (f ∣_ V))
  have : Surjective (j ∣_ (f ⁻¹ᵁ V)) := by
    constructor
    intro x
    obtain ⟨z, hz⟩ := hcover x.property
    have hzV : z ∈ j ⁻¹ᵁ (f ⁻¹ᵁ V) := by
      change f (j z) ∈ V
      rw [hz]
      exact x.property
    refine ⟨⟨z, hzV⟩, ?_⟩
    apply Subtype.ext
    simpa only [morphismRestrict_base_coe] using hz
  have : IsIso (j ∣_ (f ⁻¹ᵁ V)) := isIso_of_isClosedImmersion_of_surjective _
  rw [morphismRestrict_comp]
  infer_instance

/-- An actual open-isomorphism witness induces an isomorphism on the original
map's actual function fields. -/
theorem functionField_iso_of_isIso_restrict
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] (V : Y.Opens)
    (hV : (V : Set Y).Nonempty) [IsIso (f ∣_ V)] :
    IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f)) := by
  let : Nonempty V := ⟨⟨hV.choose, hV.choose_spec⟩⟩
  let : Nonempty (f ⁻¹ᵁ V).toScheme := Nonempty.map (inv (f ∣_ V)) inferInstance
  let : IsIntegral (f ⁻¹ᵁ V).toScheme := isIntegral_of_isOpenImmersion (f ⁻¹ᵁ V).ι
  let a := (f ⁻¹ᵁ V).ι
  let b := (f ∣_ V) ≫ V.ι
  let : IsOpenImmersion a := inferInstance
  let : IsOpenImmersion b := inferInstance
  let := Scheme.isDominant_of_isOpenImmersion a
  let := Scheme.isDominant_of_isOpenImmersion b
  let := Scheme.FunctionField.fieldMap_isIso a
  let := Scheme.FunctionField.fieldMap_isIso b
  have hab : a ≫ f = b := (morphismRestrict_ι f V).symm
  have : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f) ≫
      CommRingCat.ofHom (Scheme.functionFieldMap a)) := by
    change IsIso (CommRingCat.ofHom
      ((Scheme.functionFieldMap a).comp
        (Scheme.functionFieldMap f)))
    rw [← Scheme.functionFieldMap_comp]
    simpa only [hab] using Scheme.FunctionField.fieldMap_isIso b
  exact IsIso.of_isIso_comp_right
    (CommRingCat.ofHom (Scheme.functionFieldMap f))
    (CommRingCat.ofHom (Scheme.functionFieldMap a))

/-- Proper dominant images of integral curves of dimension at most one have
no nongeneric nonclosed points. This is proved by lifting points and properness. -/
theorem nongeneric_closed_of_proper_dominant_curve
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsProper f] [IsDominant f]
    [IsNoetherian X] (hdim : topologicalKrullDim X ≤ 1) (y : Y) (hy : y ≠ genericPoint Y) :
    IsClosed ({y} : Set Y) := by
  have : Surjective f := surjective_of_isDominant_of_isClosed_range f f.isClosedMap.isClosed_range
  obtain ⟨x, rfl⟩ := f.surjective y
  rcases Divisors.point_eq_generic_or_isClosed X hdim x with hx | hx
  · exact False.elim (hy (hx ▸ Scheme.map_genericPoint_of_isDominant X f))
  · simpa only [Set.image_singleton] using f.isClosedMap _ hx

/-- An integral source with nondense image in such a curve maps to an actual
closed singleton, obtained from the image of its own generic point. -/
theorem nondense_range_eq_closed_singleton
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
    (hclosed : ∀ y : Y, y ≠ genericPoint Y → IsClosed ({y} : Set Y))
    (hnd : ¬ Dense (Set.range f)) :
    ∃ y : Y, IsClosed ({y} : Set Y) ∧ Set.range f = {y} := by
  have hgen := (genericPoint_spec X).image f.continuous
  simp only [Set.image_univ] at hgen
  have hne : f (genericPoint X) ≠ genericPoint Y := by
    intro he
    apply hnd
    rw [dense_iff_closure_eq, ← hgen.def, he, genericPoint_closure]
  have hc := hclosed _ hne
  refine ⟨f (genericPoint X), hc, Set.Subset.antisymm ?_ ?_⟩
  · have he : closure (Set.range f) = {f (genericPoint X)} := by
      rw [← hgen.def, hc.closure_eq]
    exact subset_closure.trans_eq he
  · exact Set.singleton_subset_iff.mpr ⟨genericPoint X, rfl⟩


end AlgebraicGeometry.Scheme.Hom
