/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.HilbertScheme.Representability

/-! Focused consumer of the representability of the Hilbert functor of `P^n_A` on locally
Noetherian test schemes (Nitsure, arXiv:math/0504590v1, §5, pp. 25–27), with axiom guards for the
bridges "⇒" and "⇐" and the shared leaves of phases 2e–2f. -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open scoped Polynomial

universe u

/-- **The Hilbert scheme represents the Hilbert functor** and is a locally closed subscheme of
the Grassmannian. -/
example {A : Type u} [CommRing A] [IsNoetherianRing A] (ι : Type u) (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (Φ : ℚ[X]) (r : ℕ) (hr : hilbertRegularityBound n Φ ≤ r) :
    Nonempty ((locallyNoetherianHilbertFunctor ι A Φ).RepresentableBy
        (hilbertSchemeOver ι n e A Φ r)) ∧
      IsImmersion (hilbertSchemeι ι n e A Φ r) :=
  ⟨⟨locallyNoetherianHilbertFunctorRepresentableBy ι n e A Φ r hr⟩, inferInstance⟩

/-- **"⇒"**: a Hilbert family is the pullback of the universal subscheme along its Grassmannian
point. -/
example {A : Type u} [CommRing A] (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1)) {Φ : ℚ[X]}
    {T : Scheme.{u}} [IsLocallyNoetherian T] {g : T ⟶ Spec (CommRingCat.of A)}
    {Z : (pullback (toSpec A ι) g).IdealSheafData} (hZ : IsHilbertFamily ι Φ g Z) (r : ℕ)
    (hr : hilbertRegularityBound n Φ ≤ r) :
    (universalHilbertSubscheme ι r ⌊Φ.eval (r : ℚ)⌋₊ n e).comap
        (baseChangeMap ι
          (Grassmannian.schemeOver (CommRingCat.of A) ⌊Φ.eval (r : ℚ)⌋₊ ((n + r).choose r)).hom g
          (hZ.grassmannianMap ι n e r hr).left (Over.w (hZ.grassmannianMap ι n e r hr))) = Z :=
  hZ.universalHilbertSubscheme_comap_grassmannianMap ι n e r hr

/-- The two monomial evaluations agree by definition. -/
example {A : Type u} [CommRing A] (ι : Type u) (r : ℕ) :
    homogeneousEvaluation ι r (monomialFamily (A := A) ι r) = monomialMap ι A r :=
  rfl

/--
info: 'AlgebraicGeometry.ProjectiveSpace.locallyNoetherianHilbertFunctorRepresentableBy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.locallyNoetherianHilbertFunctorRepresentableBy

/--
info: 'AlgebraicGeometry.ProjectiveSpace.locallyNoetherianGrassmannianNatTrans_app_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.locallyNoetherianGrassmannianNatTrans_app_injective

/--
info: 'AlgebraicGeometry.ProjectiveSpace.isHilbertFamily_universalHilbertFamily' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.isHilbertFamily_universalHilbertFamily

/--
info: 'AlgebraicGeometry.ProjectiveSpace.exists_lift_hilbertSchemeι_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.exists_lift_hilbertSchemeι_iff

/--
info: 'AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.grassmannianMap_eq_of_comap_universalHilbertSubscheme' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.grassmannianMap_eq_of_comap_universalHilbertSubscheme

/--
info: 'AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.universalHilbertSubscheme_comap_grassmannianMap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.universalHilbertSubscheme_comap_grassmannianMap

/--
info: 'AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.evaluationIdeal_kernel_directImageQuotientMap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.evaluationIdeal_kernel_directImageQuotientMap

/--
info: 'AlgebraicGeometry.ProjectiveSpace.monomialEvaluation_comp_twistedRestriction_evaluationIdeal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.ProjectiveSpace.monomialEvaluation_comp_twistedRestriction_evaluationIdeal

/--
info: 'AlgebraicGeometry.ProjectiveSpace.epi_directImageMonomialMap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.epi_directImageMonomialMap

/--
info: 'AlgebraicGeometry.ProjectiveSpace.directImageQuotientMap_eq_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.directImageQuotientMap_eq_comp

/--
info: 'AlgebraicGeometry.ProjectiveSpace.ιFree_monomialMap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.ιFree_monomialMap

/--
info: 'AlgebraicGeometry.Scheme.Modules.isIso_of_epi_of_sheafHasRank' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.isIso_of_epi_of_sheafHasRank

/--
info: 'AlgebraicGeometry.Scheme.Modules.exists_iso_of_kernel_ι_comp_eq_zero_of_sheafHasRank' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.exists_iso_of_kernel_ι_comp_eq_zero_of_sheafHasRank

/--
info: 'AlgebraicGeometry.Scheme.Modules.Hom.comp_toQuotientModule_imageIdealData_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.Hom.comp_toQuotientModule_imageIdealData_eq_zero

/--
info: 'CategoryTheory.MonoidalCategory.comp_rightUnitor_inv_whiskerLeft_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.MonoidalCategory.comp_rightUnitor_inv_whiskerLeft_eq_zero

/--
info: 'AlgebraicGeometry.Grassmannian.classifyingMap_pullback_universalQuotientRep' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Grassmannian.classifyingMap_pullback_universalQuotientRep

/--
info: 'AlgebraicGeometry.ProjectiveSpace.locallyNoetherianGrassmannianNatTrans_app_homEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.locallyNoetherianGrassmannianNatTrans_app_homEquiv

/--
info: 'AlgebraicGeometry.ProjectiveSpace.locallyNoetherianHilbertFunctorRepresentableBy_homEquiv_id' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.ProjectiveSpace.locallyNoetherianHilbertFunctorRepresentableBy_homEquiv_id

/--
info: 'AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.epi_directImageQuotientMap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.epi_directImageQuotientMap

/--
info: 'AlgebraicGeometry.ProjectiveSpace.isNoetherian_hilbertScheme' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.isNoetherian_hilbertScheme
