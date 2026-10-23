/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.AffineSheafification
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.OriginalPresheaf

/-! # Original higher direct images from affine-test cohomology

The native sheafification formula avoids passing to a strict-local limit.
Vanishing and multiplication are checked on original represented cohomology
of actual affine etale tests, with the input Ext universe retained.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

attribute [local instance] hasSheafifyLarge

variable {D X : Scheme.{u}} (j : D ⟶ X)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} D)]
  (F : AbelianSheaf.{u, u + 1} D) (q : ℕ)

/-- Vanishing on the affine-test basis kills the actual original higher direct image. -/
theorem higherDirectImage_isZero_of_affine
    (h : ∀ U : X.Etale, IsAffine U.left →
      Subsingleton (Sheaf.LargeCohomology.H.{w, u + 1, u, u + 1}
        D.smallEtaleTopology F q ((siteBaseChange j).obj U))) :
    IsZero ((higherDirectImage j q).obj F) := by
  let P := (resolutionCohomologyPresheaf j q).obj F
  have hP : IsZero ((presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj P) :=
    Etale.isZero_sheafify_of_affine X (fun U hU => by
      let := h U hU
      exact (originalCohomologyResolutionEquiv j U F q).surjective.subsingleton)
  exact hP.of_iso ((resolutionCohomologySheafificationIso j q).app F).symm

/-- Multiplication by n on original affine-test cohomology gives the actual
multiplication isomorphism on the original higher direct-image object. -/
theorem higherDirectImage_nsmul_isIso_of_affine (n : ℕ)
    (h : ∀ U : X.Etale, IsAffine U.left → Function.Bijective
      (fun x : Sheaf.LargeCohomology.H.{w, u + 1, u, u + 1}
        D.smallEtaleTopology F q ((siteBaseChange j).obj U) => n • x)) :
    IsIso (n • 𝟙 ((higherDirectImage j q).obj F)) := by
  let P := (resolutionCohomologyPresheaf j q).obj F
  let L := presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}
  have hP : IsIso (L.map (n • 𝟙 P)) :=
    Etale.isIso_sheafify_map_of_affine X _ (fun U hU => by
      let e := originalCohomologyResolutionEquiv j U F q
      change Function.Bijective (fun x : P.obj (op U) => n • x)
      constructor
      · intro x y hxy
        apply e.symm.injective
        apply (h U hU).injective
        change n • e.symm x = n • e.symm y
        change n • x = n • y at hxy
        rw [← map_nsmul, ← map_nsmul, hxy]
      · intro y
        obtain ⟨x, hx⟩ := (h U hU).surjective (e.symm y)
        refine ⟨e x, ?_⟩
        change n • e x = y
        change n • x = e.symm y at hx
        rw [← map_nsmul, hx, e.apply_symm_apply])
  have hmap : L.map (n • 𝟙 P) = n • 𝟙 (L.obj P) := by simp
  let : IsIso (n • 𝟙 (L.obj P)) := by rw [← hmap]; exact hP
  let e : L.obj P ≅ (higherDirectImage j q).obj F :=
    (resolutionCohomologySheafificationIso j q).app F
  have he : n • 𝟙 ((higherDirectImage j q).obj F) =
      e.inv ≫ (n • 𝟙 (L.obj P)) ≫ e.hom := by
    simp only [Preadditive.comp_nsmul, Preadditive.nsmul_comp,
      Category.id_comp, Iso.inv_hom_id]
  rw [he]
  infer_instance

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
