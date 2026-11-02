/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.OpenLocalization

/-!
# The open-closed sequence on an open subscheme, with compact supports

The examples restate the isomorphism `jU_! ∘ i_* ≅ (i ≫ jU)_*`, the identification of the
first map with the extension map of the point-removal sequence, the exact sequence
`0 → H^0_c(V, F|_V) → H^0_c(U, F) → H^0(pointScheme U D, i^* F) → H^1_c(V, F|_V) →
H^1_c(U, F)` for a finite set `D` of points of `U` closed in `X`, and the vanishing of its third
term in positive degree, and guard the axioms of every public declaration.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme.EtaleCohomology
open AlgebraicGeometry.Scheme.EtaleCohomology.Curves.FiniteClosedSupport

universe w w' u

namespace AglibTest.CompactSupportOpenLocalization

attribute [local instance] hasSheafifyLarge

variable {V U X : Scheme.{u}} (jV : V ⟶ U) [IsOpenImmersion jV] (jU : U ⟶ X)
  [IsOpenImmersion jU] (F : AbelianSheaf.{u, u + 1} U) [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- Extension by zero of a direct image from a part closed in `X` is a direct image. -/
example {Z : Scheme.{u}} (i : Z ⟶ U) [IsClosedImmersion (i ≫ jU)]
    (M : AbelianSheaf.{u, u + 1} Z) :
    (etaleLowerShriek jU).obj ((directImage i).obj M) ≅ (directImage (i ≫ jU)).obj M :=
  (etaleLowerShriekDirectImageIso jU i).app M

/-- The first map of the sequence on `U` is the extension map of the point-removal sequence. -/
example (r : ℕ) (x : CompactSupport.H.{w} (jV ≫ jU) ((inverseImage jV).obj F) r) :
    CompactSupport.extensionCohomologyMap jV jU F r x =
      CompactSupport.H.map jU ((etaleLowerShriekAdjunction jV).counit.app F) r
        ((CompactSupport.lowerShriekAddEquiv jV jU ((inverseImage jV).obj F) r).symm x) :=
  CompactSupport.extensionCohomologyMap_eq_map_counit jV jU F r x

variable (D : Set U) (hD : Set.range jV = Dᶜ) (hfin : D.Finite)
  (hclosed : ∀ x ∈ D, IsClosed ({jU x} : Set X))
  (hsep : ∀ x : D, IsSepClosed (U.residueField x.val))
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} (pointScheme U D))]

/-- The low-degree exact sequence through the point scheme of `D ⊆ U`. -/
example :
    Function.Injective (CompactSupport.extensionCohomologyMap.{w} jV jU F 0) ∧
      Function.Exact (CompactSupport.extensionCohomologyMap.{w} jV jU F 0)
        (CompactSupport.compactPointRestriction.{w, w'} jU D hfin hclosed F 0) ∧
      Function.Exact (CompactSupport.compactPointRestriction.{w, w'} jU D hfin hclosed F 0)
        (CompactSupport.compactPointBoundary.{w, w'} jV jU D hfin hclosed hD F 0 1 rfl) ∧
      Function.Exact (CompactSupport.compactPointBoundary.{w, w'} jV jU D hfin hclosed hD F 0 1 rfl)
        (CompactSupport.extensionCohomologyMap.{w} jV jU F 1) := by
  let := CompactSupport.isClosedImmersion_inclusion_comp jU D hfin hclosed
  let := inclusion_isClosedImmersion U D hfin
    (CompactSupport.isClosed_singleton_of_isClosed_image jU D hclosed)
  exact ⟨CompactSupport.extensionCohomologyMap_zero_injective_of_closedImmersion jV jU
      (inclusion U D) (CompactSupport.range_eq_compl_range_inclusion D jV hD) F,
    CompactSupport.exact_extensionCohomologyMap_compactPointRestriction jV jU D hfin hclosed hD F 0,
    CompactSupport.exact_compactPointRestriction_compactPointBoundary jV jU D hfin hclosed hD F
      0 1 rfl,
    CompactSupport.exact_compactPointBoundary_extensionCohomologyMap jV jU D hfin hclosed hD F
      0 1 rfl⟩

/-- The third term vanishes in positive degree. -/
example (r : ℕ) (hr : 0 < r) :
    Subsingleton (Sheaf.H.{w'} ((inverseImage (inclusion U D)).obj F) r) :=
  CompactSupport.subsingleton_H_inverseImage_inclusion_of_sepClosed D hfin F hsep r hr

end AglibTest.CompactSupportOpenLocalization

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.etaleLowerShriek_counit_directImage_isIso_of_range_subset' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.etaleLowerShriek_counit_directImage_isIso_of_range_subset

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.inverseImageDirectImageCompIso' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.inverseImageDirectImageCompIso

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.etaleLowerShriekDirectImageIso' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.etaleLowerShriekDirectImageIso

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.directImageAddEquiv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.directImageAddEquiv

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.directImageAddEquiv_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.directImageAddEquiv_apply

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.lowerShriekAddEquiv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.lowerShriekAddEquiv

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.lowerShriekAddEquiv_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.lowerShriekAddEquiv_apply

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.lowerShriekAddEquiv_symm_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.lowerShriekAddEquiv_symm_apply

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.extensionMap_eq_compIso_counit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.extensionMap_eq_compIso_counit

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.extensionCohomologyMap_eq_map_counit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.extensionCohomologyMap_eq_map_counit

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.compactRestriction' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.compactRestriction

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.compactRestriction_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.compactRestriction_apply

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.compactBoundary' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.compactBoundary

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.compactBoundary_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.compactBoundary_apply

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.exact_extensionCohomologyMap_compactRestriction' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.exact_extensionCohomologyMap_compactRestriction

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.exact_compactRestriction_compactBoundary' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.exact_compactRestriction_compactBoundary

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.exact_compactBoundary_extensionCohomologyMap' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.exact_compactBoundary_extensionCohomologyMap

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.extensionCohomologyMap_zero_injective_of_closedImmersion' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.extensionCohomologyMap_zero_injective_of_closedImmersion

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.isClosed_singleton_of_isClosed_image' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.isClosed_singleton_of_isClosed_image

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.isClosedImmersion_inclusion_comp' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.isClosedImmersion_inclusion_comp

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.subsingleton_H_inverseImage_inclusion_of_sepClosed' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.subsingleton_H_inverseImage_inclusion_of_sepClosed

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.compactPointRestriction' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.compactPointRestriction

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.compactPointBoundary' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.compactPointBoundary

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.exact_extensionCohomologyMap_compactPointRestriction' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.exact_extensionCohomologyMap_compactPointRestriction

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.exact_compactPointRestriction_compactPointBoundary' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.exact_compactPointRestriction_compactPointBoundary

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.exact_compactPointBoundary_extensionCohomologyMap' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.exact_compactPointBoundary_extensionCohomologyMap
