/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Proper.BirationalInterfaces
public import Aglib.AlgebraicGeometry.Morphisms.Proper.GenericExtension

/-!
# The proper birational isomorphism locus at a valuation-ring stalk

The inverse of the actual function-field map extends by properness to the
actual valuation-ring stalk, then spreads to an open neighborhood of its point.
The resulting section is dominant. Separatedness and reducedness prove that
it is also an inverse on the whole inverse image of that neighborhood.

This proves `ProperBirationalDVRIsomorphismLocus`. The intermediate theorem
needs only a valuation-ring stalk and does not need local Noetherianity.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

universe u

/-- A dominant section over an open subset of a separated morphism with reduced
source is an inverse on the entire inverse image of that open subset. -/
theorem isIso_restrict_of_dominant_section {X Y : Scheme.{u}} [IsReduced X]
    (f : X ⟶ Y) [IsSeparated f] (U : Y.Opens)
    (s : U.toScheme ⟶ X) [IsDominant s] (hs : s ≫ f = U.ι) :
    IsIso (f ∣_ U) := by
  let V := f ⁻¹ᵁ U
  let t : U.toScheme ⟶ V.toScheme :=
    (isPullback_morphismRestrict f U).lift (𝟙 _) s (by simpa using hs.symm)
  have ht : t ≫ V.ι = s := (isPullback_morphismRestrict f U).lift_snd _ _ _
  have htf : t ≫ f ∣_ U = 𝟙 _ := (isPullback_morphismRestrict f U).lift_fst _ _ _
  let : IsDominant (t ≫ V.ι) := ht ▸ inferInstance
  let : IsDominant t := IsDominant.of_comp_of_isOpenImmersion t V.ι
  let : IsReduced V.toScheme := isReduced_of_isOpenImmersion V.ι
  have hft : (f ∣_ U) ≫ t = 𝟙 _ :=
    ext_of_isDominant_of_isSeparated (f ∣_ U)
      (by simp [Category.assoc, htf]) t (by simp [← Category.assoc, htf])
  exact ⟨⟨t, hft, htf⟩⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A proper dominant map of integral schemes which induces an isomorphism on
their actual function fields is an isomorphism on a neighborhood of every point
whose actual stalk is a valuation ring. -/
theorem exists_isIso_restrict_of_isProper_birational_at_valuationRing
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsProper f] [IsDominant f]
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f)))
    (y : Y) [ValuationRing (Y.presheaf.stalk y)] :
    ∃ U : Y.Opens, y ∈ U ∧ IsIso (f ∣_ U) := by
  let : IsIso (CommRingCat.ofHom (functionFieldMap f)) := hff
  let g : Spec Y.functionField ⟶ X :=
    inv (Spec.map (CommRingCat.ofHom (functionFieldMap f))) ≫
      X.fromSpecStalk (genericPoint X)
  have hg : g ≫ f = Y.fromSpecStalk (genericPoint Y) ≫ 𝟙 Y := by
    dsimp only [g]
    rw [Category.assoc, fromSpecStalk_genericPoint_naturality f,
      IsIso.inv_hom_id_assoc, Category.comp_id]
  let : IsDominant g := by dsimp [g]; infer_instance
  obtain ⟨U, hy, s, hsg, hsf⟩ := exists_open_extension (𝟙 Y) f g hg y
  have : IsDominant (genericToOpen U ⟨y, hy⟩ ≫ s) := hsg ▸ inferInstance
  let : IsDominant s := IsDominant.of_comp (genericToOpen U ⟨y, hy⟩) s
  exact ⟨U, hy, isIso_restrict_of_dominant_section f U s (by simpa using hsf)⟩

/-- The unconditional supplier for the original proper-birational DVR
isomorphism-locus interface, with its actual function-field map and target open. -/
theorem properBirationalDVRIsomorphismLocus : ProperBirationalDVRIsomorphismLocus := by
  intro X Y _ _ _ f _ _ hff y _
  exact exists_isIso_restrict_of_isProper_birational_at_valuationRing f hff y

end AlgebraicGeometry.Scheme
