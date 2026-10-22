/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Stalk.Scalar
public import Aglib.AlgebraicGeometry.Modules.IdealPowers.AffineSections
public import Aglib.AlgebraicGeometry.Modules.IdealPowers.Thickening
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Proper structural ideals at points over the closed point

The original section scalars followed by their germ equal the original
structural stalk scalars. At a point over the closed point of a local base,
that structural map is local, so every proper base ideal remains proper.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

universe u
variable {A : Type u} [CommRing A] [IsLocalRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) (x : X)

omit [IsLocalRing A] in
/-- The original germ of structural section constants is the structural
stalk scalar map, on every neighborhood of the point. -/
theorem germ_comp_idealSectionRingHom (U : X.Opens) (hxU : x ∈ U) :
    (X.presheaf.germ U x hxU).hom.comp
      (Modules.idealSectionRingHom X (Modules.idealThickeningBaseScalar f) U) =
        f.stalkScalar x := by
  ext a
  exact ConcreteCategory.congr_hom
    (X.presheaf.germ_res (homOfLE (le_top : U ≤ ⊤)) x hxU)
    (Modules.idealThickeningBaseScalar f a)

/-- Over the closed point, the original structural map to the stalk is local. -/
theorem stalkScalar_isLocalHom_of_closedPoint
    (hx : f x = IsLocalRing.closedPoint A) : IsLocalHom (f.stalkScalar x) := by
  have hb (y : Spec (.of A)) (hy : y = IsLocalRing.closedPoint A) :
      IsLocalHom (((Spec (.of A)).presheaf.germ ⊤ y trivial).hom.comp
        (Scheme.ΓSpecIso (.of A)).inv.hom) := by
    subst y
    change IsLocalHom (((Scheme.ΓSpecIso (.of A)).inv ≫
      (Spec (.of A)).presheaf.germ ⊤ (IsLocalRing.closedPoint A) trivial).hom)
    rw [← ΓSpecIso_hom_stalkClosedPointIso_inv]
    simpa only [Iso.inv_hom_id_assoc, Iso.symm_hom] using
      isLocalHom_of_iso (stalkClosedPointIso (.of A)).symm
  have := hb (f x) hx
  rw [stalkScalar_eq_local]
  infer_instance

/-- A proper base ideal stays proper in the actual stalk above the closed point. -/
theorem map_stalkScalar_ne_top_of_closedPoint (I : Ideal A) (hI : I ≠ ⊤)
    (hx : f x = IsLocalRing.closedPoint A) : I.map (f.stalkScalar x) ≠ ⊤ := by
  have := stalkScalar_isLocalHom_of_closedPoint f x hx
  exact ((Ideal.map_mono (IsLocalRing.le_maximalIdeal hI)).trans_lt
    (IsLocalRing.map_maximalIdeal_lt_top (f.stalkScalar x))).ne

/-- The original affine-section ideal, mapped by the actual germ, is proper.
No henselianity, completeness, or flatness hypothesis is required. -/
theorem map_sectionIdeal_germ_ne_top_of_closedPoint (I : Ideal A) (hI : I ≠ ⊤)
    (hx : f x = IsLocalRing.closedPoint A) (U : X.Opens) (hxU : x ∈ U) :
    (I.map (Modules.idealSectionRingHom X (Modules.idealThickeningBaseScalar f) U)).map
      (X.presheaf.germ U x hxU).hom ≠ ⊤ := by
  rw [Ideal.map_map, germ_comp_idealSectionRingHom]
  exact map_stalkScalar_ne_top_of_closedPoint f x I hI hx

end AlgebraicGeometry.Scheme.Hom
