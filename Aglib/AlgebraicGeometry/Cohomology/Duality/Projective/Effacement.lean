/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.TwistExt
public import Aglib.AlgebraicGeometry.Cohomology.Projective.Coproduct
public import Aglib.Algebra.Homology.Simplex.Relative.Weights.NegativeTop
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Vanishing for actual negative-twist presentation terms

Original negative-twist cohomology is concentrated in the projective top degree. Finite
coproducts retain this vanishing, including degree zero when the dimension is positive.
Native Ext commutes with the actual finite biproduct, so the original sufficiently
negative presentation terms have zero positive Ext into the dualizing twist.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open AlgebraicGeometry.ProjectiveSpace

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable (R : Type u) [CommRing R] (ι : Type u)

/-- Original cohomology of a negative twist vanishes in every degree different from the
projective dimension. Dimension zero is retained as its possible nonzero degree. -/
theorem twistingCohomology_subsingleton_of_neg_degree (n : ℕ) (e : ι ≃ Fin (n + 1))
    (d : ℤ) (hd : d < 0) (q : ℕ) (hq : q ≠ n) :
    Subsingleton
      (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι) (twistingSheaf R ι d)) q) := by
  let := ModuleCat.subsingleton_of_isZero
    (MvPolynomial.coordinateLaurentTupleHomology_isZero_of_neg_degree_of_ne_top R n e d hd q hq)
  exact (twistingLaurentCohomologyLinearEquiv R ι d q).symm.injective.subsingleton

/-- The same vanishing holds for the actual finite coproduct used in coherent presentations. -/
theorem twistingCoproductCohomology_subsingleton_of_neg_degree
    {I : Type u} [Finite I] (n : ℕ) (e : ι ≃ Fin (n + 1))
    (d : I → ℤ) (hd : ∀ a, d a < 0) (q : ℕ) (hq : q ≠ n) :
    Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
      (∐ fun a => twistingSheaf R ι (d a))) q) := by
  let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let : ∀ a, Subsingleton ((moduleCohomologyFunctorOfHom (ProjectiveSpace R ι) α q).obj
      (twistingSheaf R ι (d a))) := fun a =>
    twistingCohomology_subsingleton_of_neg_degree R ι n e (d a) (hd a) q hq
  exact (twistingCoproductCohomologyLinearEquiv R ι d q).injective.subsingleton

/-- Positive native Ext from an actual finite coproduct of sufficiently negative twists
into the dualizing twist vanishes over an arbitrary commutative base ring. -/
theorem negativeTwistCoproductExt_dualizing_subsingleton [Fintype ι]
    {I : Type u} [Finite I] (n : ℕ) (e : ι ≃ Fin (n + 1))
    (N : I → ℕ) (hN : ∀ a, Fintype.card ι ≤ N a) (q : ℕ) (hq : q ≠ 0) :
    Subsingleton (Ext.{u + 1} (C := (ProjectiveSpace R ι).Modules)
      (∐ fun a => twistingSheaf R ι (-(N a : ℤ)))
      (twistingSheaf R ι (-(Fintype.card ι : ℤ))) q) := by
  let : Fintype I := Fintype.ofFinite I
  let d := fun a => twistingSheaf R ι (-(N a : ℤ))
  let : HasBiproduct d := HasBiproduct.of_hasCoproduct d
  let ω := twistingSheaf R ι (-(Fintype.card ι : ℤ))
  let : ∀ a, Subsingleton (Ext.{u + 1} (C := (ProjectiveSpace R ι).Modules) (d a) ω q) :=
    fun a => negativeTwistExt_dualizing_subsingleton R ι n e (N a) (hN a) q hq
  let E := (((extFunctor (C := (ProjectiveSpace R ι).Modules) q).mapIso
    (biproduct.isoCoproduct d).op).app ω).addCommGroupIsoToAddEquiv.trans
      (Ext.biproductAddEquiv (biproduct.isBilimit d) ω q)
  exact E.injective.subsingleton

end AlgebraicGeometry.Scheme.Cohomology
