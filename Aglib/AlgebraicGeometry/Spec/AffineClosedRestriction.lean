/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.IdealPowers.IdealSheaf
public import Aglib.AlgebraicGeometry.IdealSheaf.Closed.OpenRestriction

/-! # The original closed restriction and its generated kernel

The native image of an affine closed map restricted to an arbitrary open is
its actual generated ideal subscheme. The isomorphism retains the original
restricted immersion, rather than replacing the ambient open by a pullback.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

open Modules
universe u

variable {A B : Type u} [CommRing A] [CommRing B]
  (ε : B →+* A) (V : (Spec (.of B)).Opens)

/-- The actual restricted affine map has the original generated kernel sheaf. -/
theorem affineRestriction_ker :
    (Spec.map (CommRingCat.ofHom ε) ∣_ V).ker =
      idealThickeningIdealSheaf V.ι (RingHom.ker ε) := by
  rw [← IdealSheafData.kernel_comap_open_pullback
    (Spec.map (CommRingCat.ofHom ε)) (Spec.map (CommRingCat.ofHom ε) ∣_ V)
    (Spec.map (CommRingCat.ofHom ε) ⁻¹ᵁ V).ι V.ι
    (isPullback_morphismRestrict (Spec.map (CommRingCat.ofHom ε)) V)]
  ext U : 2
  rw [IdealSheafData.ideal_comap_eq_map_appLE _ V.ι
    ⟨⊤, isAffineOpen_top _⟩ U (by simp), IdealSheafData.specMap_kernel_top]
  have he : (RingHom.ker ε).comap (Scheme.ΓSpecIso (.of B)).hom.hom =
      (RingHom.ker ε).map (Scheme.ΓSpecIso (.of B)).inv.hom :=
    (Ideal.map_comap_of_equiv (Scheme.ΓSpecIso (.of B)).commRingCatIsoToRingEquiv.symm).symm
  rw [he, Ideal.map_map, idealThickeningIdealSheaf_ideal]
  rfl

/-- The original restricted closed source is its native generated ideal subscheme. -/
def affineClosedRestrictionIso (hε : Function.Surjective ε) :
    (Spec.map (CommRingCat.ofHom ε) ⁻¹ᵁ V).toScheme ≅
      (idealThickeningIdealSheaf V.ι (RingHom.ker ε)).subscheme := by
  let : IsClosedImmersion (Spec.map (CommRingCat.ofHom ε)) :=
    IsClosedImmersion.spec_of_surjective _ hε
  exact asIso (Spec.map (CommRingCat.ofHom ε) ∣_ V).toImage ≪≫
    eqToIso (congrArg IdealSheafData.subscheme (affineRestriction_ker ε V))

private theorem subscheme_eqToHom_ι {X : Scheme.{u}} {I J : X.IdealSheafData} (h : I = J) :
    eqToHom (congrArg IdealSheafData.subscheme h) ≫ J.subschemeι = I.subschemeι := by
  subst J
  simp

/-- The comparison triangle is the original restricted scheme map. -/
@[reassoc]
theorem affineClosedRestrictionIso_hom_ι (hε : Function.Surjective ε) :
    (affineClosedRestrictionIso ε V hε).hom ≫
      (idealThickeningIdealSheaf V.ι (RingHom.ker ε)).subschemeι =
        Spec.map (CommRingCat.ofHom ε) ∣_ V := by
  have ht :
      eqToHom (congrArg IdealSheafData.subscheme (affineRestriction_ker ε V)) ≫
        (idealThickeningIdealSheaf V.ι (RingHom.ker ε)).subschemeι =
      (Spec.map (CommRingCat.ofHom ε) ∣_ V).ker.subschemeι :=
    subscheme_eqToHom_ι (affineRestriction_ker ε V)
  simp only [affineClosedRestrictionIso, Iso.trans_hom, Category.assoc, eqToIso.hom,
    asIso_hom]
  exact (congrArg (fun k : (Spec.map (CommRingCat.ofHom ε) ∣_ V).ker.subscheme ⟶
      V.toScheme => (Spec.map (CommRingCat.ofHom ε) ∣_ V).toImage ≫ k) ht).trans
    (Spec.map (CommRingCat.ofHom ε) ∣_ V).toImage_imageι

end AlgebraicGeometry.Scheme
