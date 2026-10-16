/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Structure
public import Aglib.AlgebraicGeometry.Modules.Invertible.Gluing.Sections

/-!
# Structural constants on the standard projective scheme

The structural map to `Spec R`, its restriction to every positive homogeneous basic open,
and the canonical section-to-homogeneous-localization isomorphism retain the same coefficient
map. The final formula compares the original restriction of a global structural constant
with the actual homogeneous fraction of that constant.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace AlgebraicGeometry.ProjectiveSpace

variable (R : Type u) [CommRing R] (ι : Type u)

/-- The restriction of the structural morphism to a positive homogeneous basic open is
induced by the original coefficient map into its homogeneous localization. -/
theorem basicOpen_toSpec (f : MvPolynomial ι R) {m : ℕ}
    (hf : f ∈ MvPolynomial.homogeneousSubmodule ι R m) (hm : 0 < m) :
    (Proj.basicOpen (MvPolynomial.homogeneousSubmodule ι R) f).ι ≫ toSpec R ι =
      (Proj.basicOpenIsoSpec (MvPolynomial.homogeneousSubmodule ι R) f hf hm).hom ≫
        Spec.map (CommRingCat.ofHom
          ((HomogeneousLocalization.fromZeroRingHom (MvPolynomial.homogeneousSubmodule ι R)
            (Submonoid.powers f)).comp (MvPolynomial.toHomogeneousSubmoduleZero R ι))) := by
  apply (cancel_epi
    (Proj.basicOpenIsoSpec (MvPolynomial.homogeneousSubmodule ι R) f hf hm).inv).mp
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rw [Proj.basicOpenIsoSpec_inv_ι, toSpec, ← Category.assoc,
    Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

/-- The restriction of an actual global structural constant agrees with its homogeneous
localization image under the canonical map to sections. -/
theorem constant_restriction (f : MvPolynomial ι R) {m : ℕ}
    (hf : f ∈ MvPolynomial.homogeneousSubmodule ι R m) (hm : 0 < m) (r : R) :
    Scheme.Modules.Invertible.sectionRestrict (ProjectiveSpace R ι)
      (show Proj.basicOpen (MvPolynomial.homogeneousSubmodule ι R) f ≤ ⊤ from le_top)
      (((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) r) =
    (Proj.awayToSection (MvPolynomial.homogeneousSubmodule ι R) f).hom
      (HomogeneousLocalization.fromZeroRingHom (MvPolynomial.homogeneousSubmodule ι R)
        (Submonoid.powers f) (MvPolynomial.toHomogeneousSubmoduleZero R ι r)) := by
  let U := Proj.basicOpen (MvPolynomial.homogeneousSubmodule ι R) f
  let c := (HomogeneousLocalization.fromZeroRingHom (MvPolynomial.homogeneousSubmodule ι R)
    (Submonoid.powers f)).comp (MvPolynomial.toHomogeneousSubmoduleZero R ι)
  have hb : (Proj.basicOpenToSpec (MvPolynomial.homogeneousSubmodule ι R) f).appTop =
      (Scheme.ΓSpecIso _).hom ≫ Proj.awayToSection (MvPolynomial.homogeneousSubmodule ι R) f ≫
        U.topIso.inv := Proj.basicOpenToSpec_app_top (MvPolynomial.homogeneousSubmodule ι R) f
  have he : (Scheme.ΓSpecIso (.of R)).inv ≫ (U.ι ≫ toSpec R ι).appTop =
      CommRingCat.ofHom c ≫ Proj.awayToSection (MvPolynomial.homogeneousSubmodule ι R) f ≫
        U.topIso.inv := by
    rw [basicOpen_toSpec R ι f hf hm, Scheme.Hom.comp_appTop,
      ← Scheme.ΓSpecIso_inv_naturality_assoc, Proj.basicOpenIsoSpec_hom]
    rw [hb]
    simp only [Iso.inv_hom_id_assoc]
    rfl
  have ht : U.ι.appTop ≫ U.topIso.hom =
      (ProjectiveSpace R ι).presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op := by
    rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom, ← Functor.map_comp]
    rfl
  have h := congrArg (fun t => t ≫ U.topIso.hom) he
  simp only [Scheme.Hom.comp_appTop, Category.assoc, Iso.inv_hom_id, Category.comp_id] at h
  rw [ht] at h
  have hr := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h) r
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at hr
  exact hr

end AlgebraicGeometry.ProjectiveSpace
