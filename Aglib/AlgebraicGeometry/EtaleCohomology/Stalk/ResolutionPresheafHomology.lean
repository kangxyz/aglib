/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ResolutionPresheaf
public import
  Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.DerivedPostcompResolution

/-! # The original presheaf-to-higher-image map on resolution homology

The existing sheafification comparison is normalized on any supplied actual
integer resolution. Both the original sheafification unit and the actual
termwise counit are retained. No sections-versus-cohomology isomorphism is
assumed in positive degree.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The original comparison into the higher-image sheaf is the actual
sheafification unit on resolution homology, followed by native exact
sheafification and the original termwise direct-image counit. -/
theorem resolutionCohomologyToHigherDirectImage_resolution
    {F : AbelianSheaf.{u, u + 1} X} (I : InjectiveResolution F) (q : ℕ) :
    (resolutionCohomologyToHigherDirectImage f q).app F ≫
        (I.isoRightDerivedObjCochain (directImage f) q).hom.hom =
      (I.isoRightDerivedObjCochain (directImagePresheaf f) q).hom ≫
        toSheafify (Scheme.smallEtaleTopology S)
          ((((directImagePresheaf f).mapHomologicalComplex (.up ℤ)).obj
            I.cochainComplex).homology (q : ℤ)) ≫
        (((((directImagePresheaf f).mapHomologicalComplex (.up ℤ)).obj
          I.cochainComplex).sc (q : ℤ)).mapHomologyIso
            (presheafToSheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1})).inv.hom ≫
        (homologyMap ((NatTrans.mapHomologicalComplex
          (directImagePresheafSheafificationIso f).hom (.up ℤ)).app I.cochainComplex)
            (q : ℤ)).hom := by
  let P := directImagePresheaf f
  let L := presheafToSheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1}
  let U := sheafToPresheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1}
  let d := Sheaf.ModuleCoefficients.rightDerivedPostcompIso P L q
  let K := (P.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
  let e := (K.sc (q : ℤ)).mapHomologyIso L
  have hp := Sheaf.ModuleCoefficients.rightDerivedPostcompIso_hom_resolution_cochain
    P L I q
  have hi : d.inv.app F ≫ (I.isoRightDerivedObjCochain (P ⋙ L) q).hom =
      L.map (I.isoRightDerivedObjCochain P q).hom ≫ e.inv := by
    apply (cancel_mono e.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← hp, Iso.inv_hom_id_app_assoc]
  have hn := InjectiveResolution.isoRightDerivedObjCochain_hom_natTrans
    (directImagePresheafSheafificationIso f).hom I q
  have hu := (sheafificationAdjunction (Scheme.smallEtaleTopology S)
    AddCommGrpCat.{u + 1}).unit.naturality
      (I.isoRightDerivedObjCochain P q).hom
  change (I.isoRightDerivedObjCochain P q).hom ≫
      toSheafify (Scheme.smallEtaleTopology S) (K.homology (q : ℤ)) =
    toSheafify (Scheme.smallEtaleTopology S) ((P.rightDerived q).obj F) ≫
      U.map (L.map (I.isoRightDerivedObjCochain P q).hom) at hu
  change toSheafify (Scheme.smallEtaleTopology S) ((P.rightDerived q).obj F) ≫
      U.map (d.inv.app F ≫
        (NatTrans.rightDerived (directImagePresheafSheafificationIso f).hom q).app F) ≫
      U.map (I.isoRightDerivedObjCochain (directImage f) q).hom = _
  rw [U.map_comp, Category.assoc, ← U.map_comp, hn, U.map_comp]
  rw [← U.map_comp_assoc, hi, U.map_comp]
  simp only [Category.assoc]
  rw [← reassoc_of% hu]
  rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
