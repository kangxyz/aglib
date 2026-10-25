/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.DirectImage
public import Aglib.CategoryTheory.Sites.SheafCohomology.BasisAcyclicity.ResolutionSections
public import Aglib.CategoryTheory.Sites.SheafCohomology.BasisAcyclicity.SectionExactness

/-! # Relative higher-image acyclicity from original represented Ext

Vanishing of the original positive Ext groups from every free representable
makes the original direct-image complex of a supplied injective resolution
exact in positive degrees. The comparison with the native right-derived
functor uses that same resolution. No injectivity after scalar forgetting,
base-change assertion, or properness hypothesis is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open CategoryTheory.Sheaf.Hypercohomology

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper.Reduction

universe u e

attribute [local instance] hasSheafifyLarge

/-- Original represented Ext vanishing supplies positive acyclicity for the
actual direct image along every scheme morphism, with independent Ext universe. -/
theorem higherDirectImage_isZero_of_representedExt_vanishing
    {X S : Scheme.{u}} [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]
    (f : X ⟶ S) (F : AbelianSheaf.{u, u + 1} X)
    (hF : ∀ (U : X.Etale) (n : ℕ),
      Subsingleton (Ext.{e} (freeAbelianSheaf.{u + 1} X.smallEtaleTopology U) F (n + 1)))
    (n : ℕ) : IsZero ((higherDirectImage f (n + 1)).obj F) := by
  let I := injectiveResolution F
  let K := ((directImage f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  have hB : ∀ W : S.Etale, ∃ (ι : Type) (U : ι → Over W),
      Sieve.ofArrows (fun i => (U i).left) (fun i => (U i).hom)
        ∈ S.smallEtaleTopology W ∧ ∀ i, (fun _ : S.Etale => True) (U i).left := by
    intro W
    refine ⟨PUnit, fun _ => Over.mk (𝟙 W), ?_, fun _ => trivial⟩
    apply S.smallEtaleTopology.superset_covering _ (S.smallEtaleTopology.top_mem W)
    intro V g _
    exact (Sieve.mem_ofArrows_iff _ _ _).mpr ⟨PUnit.unit, g, (Category.comp_id g).symm⟩
  have hK : K.ExactAt (n + 1) := by
    apply Sheaf.BasisAcyclicity.exactAt_of_sections_on_basis
      (fun _ : S.Etale => True) hB K (n + 1)
    intro U _
    change (((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
      (CategoryTheory.evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj
        (op ((siteBaseChange f).obj U))).mapHomologicalComplex (.up ℕ)).obj
          I.cocomplex).ExactAt (n + 1)
    exact Sheaf.BasisAcyclicity.resolution_sections_exactAt_succ.{u + 1, u, u + 1, e}
      X.smallEtaleTopology I ((siteBaseChange f).obj U) n
      (fun x => (hF ((siteBaseChange f).obj U) n).elim x 0)
  exact IsZero.of_iso hK.isZero_homology (I.isoRightDerivedObj (directImage f) (n + 1))

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper.Reduction
