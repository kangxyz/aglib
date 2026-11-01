/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Vanishing.FiniteModificationTorsion
public import Aglib.AlgebraicGeometry.EtaleCohomology.Vanishing.ClosedImmersion
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.CoproductCohomology
public import Aglib.AlgebraicGeometry.Dimension.IntegralComponentCover

/-! # Reduction to integral components and a smaller closed boundary

The actual finite component cover is an isomorphism off its produced
lower-dimensional closed boundary. Original coproduct cohomology and the
literal torsion unit-cokernel sequence reduce vanishing to integral components
in the same degree and the boundary in the preceding degree. The native
nilradical closed immersion removes reducedness. The field is arbitrary and
the final Ext universe remains independent of the standard internal choices.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Vanishing

universe u e

attribute [local instance] hasSheafifyLarge HasExt.standard

variable {k : Type u} [Field k] (d n : ℕ)
  (hIntegral : ∀ (Y : Scheme.{u}) [IsIntegral Y] (pY : Y ⟶ Spec (.of k)) [IsProper pY],
    topologicalKrullDim Y ≤ (d + 1 : ℕ) →
      ∀ G : AbelianSheaf.{u, u + 1} Y, IsTorsion Y G →
        Subsingleton (Sheaf.H.{u + 2} G (n + 1)))
  (hBoundary : ∀ (Z : Scheme.{u}) (pZ : Z ⟶ Spec (.of k)) [IsProper pZ],
    topologicalKrullDim Z ≤ (d : ℕ) →
      ∀ G : AbelianSheaf.{u, u + 1} Z, IsTorsion Z G →
        Subsingleton (Sheaf.H.{u + 2} G n))

include hIntegral hBoundary

private theorem subsingleton_H_of_integral_boundary_reduced
    {X : Scheme.{u}} [IsReduced X] (p : X ⟶ Spec (.of k)) [IsProper p]
    (hdim : topologicalKrullDim X ≤ (d + 1 : ℕ))
    [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsTorsion X F) :
    Subsingleton (Sheaf.H.{e} F (n + 1)) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : IsNoetherian X := ⟨⟩
  let : _root_.Finite (irreducibleComponents X) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  let Y := IrreducibleComponentCover.component X
  let c : (∐ Y) ⟶ X := IrreducibleComponentCover.map X
  let : IsFinite c := inferInstanceAs (IsFinite (IrreducibleComponentCover.map X))
  let : Surjective c := inferInstanceAs (Surjective (IrreducibleComponentCover.map X))
  let G := (inverseImage c).obj F
  let : ∀ a, Subsingleton (Sheaf.H.{u + 2} ((inverseImage (Sigma.ι Y a)).obj G) (n + 1)) :=
    fun a => hIntegral (Y a) (IrreducibleComponentCover.inclusion X a ≫ p)
      ((IrreducibleComponentCover.component_topologicalKrullDim_le X a).trans hdim)
      ((inverseImage (Sigma.ι Y a)).obj G)
      ((hF.inverseImage c).inverseImage (Sigma.ι Y a))
  have hY : Subsingleton (Sheaf.H.{u + 2} G (n + 1)) :=
    Finite.subsingleton_H_of_finite_components Y G (n + 1)
  obtain ⟨Z, i, hi, hcomp, hdimZ⟩ :=
    IrreducibleComponentCover.exists_closedBoundary X d hdim
  let : IsClosedImmersion i := hi
  let : IsIso (pullback.snd c (IrreducibleComponentCover.separatingOpen X).ι) :=
    IrreducibleComponentCover.pullback_map_isIso X
  exact subsingleton_H_of_finiteModification_torsion c
    (IrreducibleComponentCover.separatingOpen X).ι i hcomp F hF n hY
      (hBoundary Z (i ≫ p) hdimZ)

/-- Same-degree vanishing on all integral proper components and preceding-degree
vanishing on all proper schemes of one smaller dimension imply vanishing for
an arbitrary proper scheme. The actual final coefficient is internally torsion;
no uniform annihilator, reducedness or algebraic-closure condition is imposed. -/
theorem subsingleton_H_of_integral_and_boundary
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProper p]
    (hdim : topologicalKrullDim X ≤ (d + 1 : ℕ))
    [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsTorsion X F) :
    Subsingleton (Sheaf.H.{e} F (n + 1)) := by
  let : IsReduced X.nilradical.subscheme := by
    apply IdealSheafData.subscheme_reduced_of_radical
    rw [← IdealSheafData.vanishingIdeal_support, support_nilradical,
      IdealSheafData.vanishingIdeal_top]
  let : Surjective X.nilradical.subschemeι := by
    constructor
    apply Set.range_eq_univ.mp
    rw [IdealSheafData.range_subschemeι, support_nilradical]
    rfl
  have hred : Subsingleton
      (Sheaf.H.{u + 2} ((inverseImage X.nilradical.subschemeι).obj F) (n + 1)) :=
    subsingleton_H_of_integral_boundary_reduced d n hIntegral hBoundary
      (X.nilradical.subschemeι ≫ p)
      (X.nilradical.subschemeι.isClosedEmbedding.isInducing.topologicalKrullDim_le.trans hdim)
      ((inverseImage X.nilradical.subschemeι).obj F)
      (hF.inverseImage X.nilradical.subschemeι)
  exact (subsingleton_H_iff_of_surjective_closedImmersion
    X.nilradical.subschemeι F (n + 1)).mpr hred

end AlgebraicGeometry.Scheme.EtaleCohomology.Vanishing
