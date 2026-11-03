/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.HigherOuterSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.H0.ClosedMapZeroNeighborhood

/-! # A fixed class near a whole finite target fibre

The same-class finite outer comparison and the closed-image zero neighborhood
produce vanishing of the original higher-image section downstairs. The
hypothesis concerns every point of the finite fibre; supplying this hypothesis
in smooth base change remains a separate mathematical step.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite

universe u w
attribute [local instance] hasSheafifyLarge

/-- Whole-fibre local vanishing of the original inner edge section implies
vanishing of the same original composite edge section on a target open. -/
theorem exists_finiteOuter_edge_zero_neighborhood
    {Y X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f] (k : Y ⟶ X)
    [HasExt.{w} (AbelianSheaf.{u, u + 1} Y)]
    (M : AbelianSheaf.{u, u + 1} Y) (q : ℕ) (c : Sheaf.H.{w} M q) (x : S)
    (hx : ∀ y : X, f y = x →
      y ∈ sectionZeroOpen ((higherDirectImage k q).obj M)
        (cohomologyToHigherSections k M q c)) :
    ∃ U : S.Opens, x ∈ U ∧
      globalSectionsPullback U.ι ((higherDirectImage (k ≫ f) q).obj M)
        (cohomologyToHigherSections (k ≫ f) M q c) = 0 := by
  let e := (higherDirectImageFiniteOuterIso f k q).app M
  let ξ := cohomologyToHigherSections (k ≫ f) M q c
  let a := (globalSections S).map e.hom ξ
  have ha : (directImageGlobalSectionsIso f).hom.app
      ((higherDirectImage k q).obj M) a =
      cohomologyToHigherSections k M q c :=
    finiteOuterHigherGlobalSectionsIso_cohomologyToHigherSections f k M q c
  obtain ⟨U, hxU, _, hz⟩ := exists_closedMap_section_zero_neighborhood
    f f.isClosedMap ((higherDirectImage k q).obj M) a x
    (by simpa only [ha] using hx)
  refine ⟨U, hxU, ?_⟩
  let E := (globalSections U.toScheme).mapIso ((inverseImage U.ι).mapIso e)
  apply (ConcreteCategory.bijective_of_isIso E.hom).injective
  have hn := ConcreteCategory.congr_hom
    (globalSectionsPullback_naturality U.ι e.hom) ξ
  exact (hn.symm.trans hz).trans (map_zero E.hom.hom).symm

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
