/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Vanishing.ModificationBound
public import Aglib.AlgebraicGeometry.EtaleCohomology.Vanishing.ProperRelativeCurves
public import Aglib.AlgebraicGeometry.RationalMap.ProjectiveLineGeometricFibres

/-! # A finite cohomological dimension step through the actual rational graph

A proper integral scheme of dimension at most `d + 1` has an actual graph
modification over the projective line. The smaller-dimensional geometric
fibres bound its original higher direct images; the proved proper-curve
bound and the original Leray comparison bound its source cohomology.
The actual modification unit cone is supported on a produced boundary of
dimension at most `d`, and its upper amplitude is two. Original finite
Postnikov and triangle bounds give the step `N` to `N + 3`.

This is an auxiliary finite bound, not the sharp bound `2 * dim X`.
All fields in the smaller-dimensional hypothesis are algebraically closed,
and the final original Ext universe is arbitrary.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace
open DerivedCategory.Plus

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Vanishing

universe u e

attribute [local instance] hasSheafifyLarge HasExt.standard HasDerivedCategory.standard

/-- A common original torsion cohomology bound in dimension at most `d`
over all algebraically closed fields gives bound `N + 3` on integral proper
schemes of dimension at most `d + 1`. All geometric producers and the literal
original derived unit cone are constructed in the proof. -/
theorem subsingleton_H_of_isTorsion_of_proper_integral_dimension_step
    (d N : ℕ)
    (hsmall : ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (Z : Scheme.{u}) (pZ : Z ⟶ Spec (.of K)) [IsProper pZ],
      topologicalKrullDim Z ≤ (d : ℕ) →
        ∀ G : AbelianSheaf.{u, u + 1} Z, IsTorsion Z G →
          ∀ q : ℕ, N < q → Subsingleton (Sheaf.H.{u + 2} G q))
    {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} [IsIntegral X] (p : X ⟶ Spec (.of k)) [IsProper p]
    (hdim : topologicalKrullDim X ≤ (d + 1 : ℕ))
    [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsTorsion X F)
    (q : ℕ) (hq : N + 3 < q) : Subsingleton (Sheaf.H.{e} F q) := by
  by_cases hzero : topologicalKrullDim X ≤ 0
  · exact subsingleton_H_of_proper_dimension_le_zero p hzero F q (by omega)
  have hpos : 0 < topologicalKrullDim X := lt_of_not_ge hzero
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : IsNoetherian X := ⟨⟩
  let Xk : OverField.FScheme k := Over.mk p
  let : IsIntegral Xk.left := inferInstanceAs (IsIntegral X)
  let : IsNoetherian Xk.left := inferInstanceAs (IsNoetherian X)
  let : IsProper Xk.hom := inferInstanceAs (IsProper p)
  obtain ⟨Y, b, g, _, hb, _, hg, _, _, ⟨U, _, hUdense, hUiso⟩, _, hbfib, hgfib⟩ :=
    exists_proper_projectiveLine_graph_modification_with_geometricFiber_bounds
      Xk d hpos hdim
  let : IsProper b := hb
  let : IsProper g := hg
  let : IsIso (b ∣_ U) := hUiso
  let : IsDominant U.ι := Opens.isDominant_ι hUdense
  let G := (inverseImage b).obj F
  have hG : IsTorsion Y G := hF.inverseImage b
  have hRg (n : ℕ) (hn : N < n) : IsZero ((higherDirectImage g n).obj G) := by
    apply isZero_higherDirectImage_obj_of_geometricFiber_H_standard g G hG n
    intro K _ _ η
    exact hsmall K (pullback g η) (pullback.snd g η) (hgfib K η)
      ((inverseImage (pullback.fst g η)).obj G) (hG.inverseImage (pullback.fst g η)) n hn
  have hline : topologicalKrullDim (ProjectiveLine.projectiveP1 k) ≤ 1 := by
    apply le_of_eq
    have he := IsHomeomorph.topologicalKrullDim_eq _
      (ProjectiveLine.TwoChart.twoChartLineIsoProjectiveP1 k).hom.homeomorph.isHomeomorph
    exact he.symm.trans (OverField.Curve.Projectivity.twoChartLine_topologicalKrullDim k)
  have hY (r : ℕ) (hr : N + 2 < r) : Subsingleton (Sheaf.H.{u + 2} G r) := by
    apply subsingleton_H_of_leray_bounds g G N 2 hRg
      (fun n _ s hs => subsingleton_H_of_isTorsion_of_proper_curve
        (ProjectiveLine.structureMap k) hline ((higherDirectImage g n).obj G)
          (higherDirectImage_isTorsion g n G hG) s hs) r (by omega)
  obtain ⟨Z, i, hi, hcomp, hdimZ⟩ :=
    U.ι.exists_closedComplement_topologicalKrullDim_le d hdim
  let : IsClosedImmersion i := hi
  let : IsIso (pullback.snd b U.ι) := by
    rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict]
    infer_instance
  let : IsIso (pullback.fst U.ι b) := by
    rw [← pullbackSymmetry_hom_comp_snd]
    infer_instance
  have hRb (n : ℕ) (hn : 2 < n) : IsZero ((higherDirectImage b n).obj G) :=
    isZero_higherDirectImage_obj_of_geometricFibres_dimension_le_one b
      (fun K _ _ η => hbfib K η) G hG n hn
  let : Subsingleton (Sheaf.H.{u + 2} F q) :=
    subsingleton_H_of_modification_bounds b U.ι i hcomp F hF 2 (N + 2) N hRb hY
      (fun H hH r hr => hsmall k Z (i ≫ p) hdimZ H hH r hr) q (by omega) (by omega)
  let E : Sheaf.H.{e} F q ≃ Sheaf.H.{u + 2} F q := CategoryTheory.Abelian.Ext.chgUniv
  exact E.injective.subsingleton

end AlgebraicGeometry.Scheme.EtaleCohomology.Vanishing
