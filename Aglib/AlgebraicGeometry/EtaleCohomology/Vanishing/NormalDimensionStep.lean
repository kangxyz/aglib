/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Vanishing.ModificationBound
public import Aglib.AlgebraicGeometry.EtaleCohomology.Vanishing.ProperRelativeCurves
public import Aglib.AlgebraicGeometry.RationalMap.ProjectiveLineGeometricFibres

public import Aglib.AlgebraicGeometry.Morphisms.Proper.BirationalBoundary
public import Aglib.AlgebraicGeometry.FunctionField.Restriction

/-! # Normal dimension step with a codimension-two boundary

The actual projective-line graph and the original proper birational map give
an isomorphism open whose closed boundary has dimension two less than the
ambient normal scheme. Independent bounds in dimensions `d + 1` and `d`
therefore give bounds `N + 2` and `M + 3` on target cohomology. In particular,
the inductive inputs `2 * (d + 1)` and `2 * d` give the sharp bound
`2 * (d + 2)`. The graph, original unit, and original coefficient are retained.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace
open DerivedCategory.Plus

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Vanishing

universe u e

attribute [local instance] hasSheafifyLarge HasExt.standard HasDerivedCategory.standard

/-- Normal proper integral schemes admit the two-step boundary improvement.
The bounds in the two smaller dimensions and all coefficient conditions are
explicit; the codimension-two geometric boundary is produced, not assumed. -/
theorem subsingleton_H_of_isTorsion_of_proper_normal_dimension_step
    (d N M : ℕ)
    (hsmall : ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (Z : Scheme.{u}) (pZ : Z ⟶ Spec (.of K)) [IsProper pZ],
      topologicalKrullDim Z ≤ (d + 1 : ℕ) →
        ∀ G : AbelianSheaf.{u, u + 1} Z, IsTorsion Z G →
          ∀ q : ℕ, N < q → Subsingleton (Sheaf.H.{u + 2} G q))
    (hboundary : ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (Z : Scheme.{u}) (pZ : Z ⟶ Spec (.of K)) [IsProper pZ],
      topologicalKrullDim Z ≤ (d : ℕ) →
        ∀ G : AbelianSheaf.{u, u + 1} Z, IsTorsion Z G →
          ∀ q : ℕ, M < q → Subsingleton (Sheaf.H.{u + 2} G q))
    {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} [IsIntegral X] (p : X ⟶ Spec (.of k)) [IsProper p]
    (hX : NormalStalks X) (hdim : topologicalKrullDim X ≤ (d + 2 : ℕ))
    [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsTorsion X F)
    (q : ℕ) (hq : N + 2 < q) (hqboundary : M + 3 < q) : Subsingleton (Sheaf.H.{e} F q) := by
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
  obtain ⟨Y, b, g, hYi, hb, hbsurj, hg, _, _, ⟨U, hUne, hUdense, hUiso⟩, _, hbfib, hgfib⟩ :=
    exists_proper_projectiveLine_graph_modification_with_geometricFiber_bounds
      Xk (d + 1) hpos (by simpa only [Xk, Over.mk_left, Nat.add_assoc, Nat.reduceAdd] using hdim)
  let : IsProper b := hb
  let : IsProper g := hg
  let : IsIntegral Y := hYi
  let : Surjective b := hbsurj
  let : Nonempty U := hUne
  let : IsDominant b := inferInstance
  have hff := functionFieldMap_isIso_of_isIso_restrict b U hUiso
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
  obtain ⟨V, Z, i, hViso, hi, hcomp, hdimZ⟩ :=
    b.exists_closedBoundary_dimension_le_of_isProper_birational hff hX d hdim
  let : IsIso (b ∣_ V) := hViso
  let : IsClosedImmersion i := hi
  let : IsIso (pullback.snd b V.ι) := by
    rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict]
    infer_instance
  let : IsIso (pullback.fst V.ι b) := by
    rw [← pullbackSymmetry_hom_comp_snd]
    infer_instance
  have hRb (n : ℕ) (hn : 2 < n) : IsZero ((higherDirectImage b n).obj G) :=
    isZero_higherDirectImage_obj_of_geometricFibres_dimension_le_one b
      (fun K _ _ η => hbfib K η) G hG n hn
  let : Subsingleton (Sheaf.H.{u + 2} F q) :=
    subsingleton_H_of_modification_bounds b V.ι i hcomp F hF 2 (N + 2) M hRb hY
      (fun H hH r hr => hboundary k Z (i ≫ p) hdimZ H hH r hr) q (by omega) (by omega)
  let E : Sheaf.H.{e} F q ≃ Sheaf.H.{u + 2} F q := CategoryTheory.Abelian.Ext.chgUniv
  exact E.injective.subsingleton

end AlgebraicGeometry.Scheme.EtaleCohomology.Vanishing
