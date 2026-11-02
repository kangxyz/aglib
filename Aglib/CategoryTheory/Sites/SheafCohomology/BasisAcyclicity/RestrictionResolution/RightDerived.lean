/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.BasisAcyclicity.RestrictionResolution
public import Mathlib.CategoryTheory.Abelian.RightDerived

/-! # Native higher-image acyclicity from original represented Ext

The existing restricted-resolution exactness theorem applies to the literal
continuous sheaf precomposition. Its original mapped resolution computes the
native right-derived object. Site object and hom universes are independent;
only the source category needs injective resolutions.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory.Sheaf.BasisAcyclicity

universe c h c' h' t e

variable {C : Type c} [Category.{h} C] {D : Type c'} [Category.{h'} D]
  (G : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [G.IsContinuous J K]
  [HasSheafify J AddCommGrpCat.{max h h' t}]
  [HasSheafify K AddCommGrpCat.{max h h' t}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max h h' t})]
  [(G.sheafPushforwardContinuous AddCommGrpCat.{max h h' t} J K).Additive]
  [HasExt.{e} (Sheaf K AddCommGrpCat.{max h h' t})]
  [HasInjectiveResolutions (Sheaf K AddCommGrpCat.{max h h' t})]

/-- Original represented Ext vanishing on the objects seen by precomposition
annihilates its positive native right-derived objects. -/
theorem isZero_rightDerived_pushforward_obj_of_representedExt_vanishing
    (F : Sheaf K AddCommGrpCat.{max h h' t})
    (hF : ∀ (W : C) (q : ℕ),
      ∀ x : Ext.{e} (Hypercohomology.freeAbelianSheaf.{max h t} K (G.obj W)) F (q + 1),
        x = 0) (q : ℕ) :
    IsZero (((G.sheafPushforwardContinuous AddCommGrpCat.{max h h' t} J K).rightDerived
      (q + 1)).obj F) := by
  let I := injectiveResolution F
  have hB : ∀ W : C, ∃ (ι : Type) (U : ι → Over W),
      Sieve.ofArrows (fun i => (U i).left) (fun i => (U i).hom) ∈ J W ∧
        ∀ i, (fun _ : C => True) (U i).left := by
    intro W
    refine ⟨PUnit, fun _ => Over.mk (𝟙 W), ?_, fun _ => trivial⟩
    apply J.superset_covering _ (J.top_mem W)
    intro V g _
    exact (Sieve.mem_ofArrows_iff _ _ _).mpr ⟨PUnit.unit, g, (Category.comp_id g).symm⟩
  have hK := restriction_resolution_exactAt_succ G J K (fun _ : C => True) hB I
    (fun W _ n => hF W n) q
  exact IsZero.of_iso hK.isZero_homology
    (I.isoRightDerivedObj (G.sheafPushforwardContinuous AddCommGrpCat J K) (q + 1))

end CategoryTheory.Sheaf.BasisAcyclicity
