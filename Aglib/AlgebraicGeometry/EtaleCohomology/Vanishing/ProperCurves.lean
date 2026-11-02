/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Vanishing.IntegralCurves
public import Aglib.AlgebraicGeometry.EtaleCohomology.Vanishing.FiniteModification
public import Aglib.AlgebraicGeometry.EtaleCohomology.Vanishing.ClosedImmersion
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.CoproductCohomology
public import Aglib.AlgebraicGeometry.EtaleCohomology.Torsion.InverseImage
public import Aglib.AlgebraicGeometry.Dimension.IntegralComponentCover

/-! # Original torsion cohomological dimension of proper curves

The actual finite cover by integral components is an isomorphism off a
zero-dimensional closed boundary. Original finite-coproduct cohomology and
the original finite-modification sequence descend the integral-curve bound.
The native nilradical closed immersion removes reducedness. All coefficients
are internally torsion, without a common annihilator or invertible-order
hypothesis, and the final original Ext universe is arbitrary.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Vanishing

universe u e

attribute [local instance] hasSheafifyLarge

/-- Every internally torsion coefficient on a reduced proper curve over a
separably closed field has zero original cohomology above degree two. -/
theorem subsingleton_H_of_isTorsion_of_proper_reduced_curve
    {k : Type u} [Field k] [IsSepClosed k]
    {X : Scheme.{u}} [IsReduced X] (p : X ⟶ Spec (.of k)) [IsProper p]
    (hdim : topologicalKrullDim X ≤ 1)
    [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsTorsion X F)
    (q : ℕ) (hq : 2 < q) : Subsingleton (Sheaf.H.{e} F q) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : IsNoetherian X := ⟨⟩
  let : _root_.Finite (irreducibleComponents X) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  let Y := IrreducibleComponentCover.component X
  let c : (∐ Y) ⟶ X := IrreducibleComponentCover.map X
  let : IsFinite c := inferInstanceAs (IsFinite (IrreducibleComponentCover.map X))
  let : Surjective c := inferInstanceAs (Surjective (IrreducibleComponentCover.map X))
  let : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} (∐ Y)) := HasExt.standard _
  let : ∀ a, HasExt.{u + 2} (AbelianSheaf.{u, u + 1} (Y a)) :=
    fun a => HasExt.standard _
  let G := (inverseImage c).obj F
  let : ∀ a, Subsingleton (Sheaf.H.{u + 2} ((inverseImage (Sigma.ι Y a)).obj G) q) :=
    fun a => subsingleton_H_of_isTorsion_of_proper_integral_curve
      (IrreducibleComponentCover.inclusion X a ≫ p)
      ((IrreducibleComponentCover.component_topologicalKrullDim_le X a).trans hdim)
      ((inverseImage (Sigma.ι Y a)).obj G)
      ((hF.inverseImage c).inverseImage (Sigma.ι Y a)) q hq
  have hY : Subsingleton (Sheaf.H.{u + 2} G q) :=
    Finite.subsingleton_H_of_finite_components Y G q
  obtain ⟨Z, i, hi, hcomp, hdimZ⟩ :=
    IrreducibleComponentCover.exists_closedBoundary X 0 (by simpa using hdim)
  let : IsClosedImmersion i := hi
  let : IsIso (pullback.snd c (IrreducibleComponentCover.separatingOpen X).ι) :=
    IrreducibleComponentCover.pullback_map_isIso X
  exact subsingleton_H_of_finiteModification_dimensionZero p c
    (IrreducibleComponentCover.separatingOpen X).ι i hcomp (by simpa using hdimZ)
      F q (by omega) hY

/-- Proper schemes of dimension at most one over separably closed fields
have original torsion étale cohomological dimension at most two. No
reducedness, irreducibility, smoothness, perfection or invertibility
hypothesis is added, and the original coefficient has no uniform exponent. -/
theorem subsingleton_H_of_isTorsion_of_proper_curve
    {k : Type u} [Field k] [IsSepClosed k]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProper p]
    (hdim : topologicalKrullDim X ≤ 1)
    [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsTorsion X F)
    (q : ℕ) (hq : 2 < q) : Subsingleton (Sheaf.H.{e} F q) := by
  let : IsReduced X.nilradical.subscheme := by
    apply IdealSheafData.subscheme_reduced_of_radical
    rw [← IdealSheafData.vanishingIdeal_support, support_nilradical,
      IdealSheafData.vanishingIdeal_top]
  let : Surjective X.nilradical.subschemeι := by
    constructor
    apply Set.range_eq_univ.mp
    rw [IdealSheafData.range_subschemeι, support_nilradical]
    rfl
  let : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} X.nilradical.subscheme) :=
    HasExt.standard _
  have hred : Subsingleton
      (Sheaf.H.{u + 2} ((inverseImage X.nilradical.subschemeι).obj F) q) :=
    subsingleton_H_of_isTorsion_of_proper_reduced_curve
      (X.nilradical.subschemeι ≫ p)
      (X.nilradical.subschemeι.isClosedEmbedding.isInducing.topologicalKrullDim_le.trans hdim)
      ((inverseImage X.nilradical.subschemeι).obj F)
      (hF.inverseImage X.nilradical.subschemeι) q hq
  exact (subsingleton_H_iff_of_surjective_closedImmersion X.nilradical.subschemeι F q).mpr hred

end AlgebraicGeometry.Scheme.EtaleCohomology.Vanishing
