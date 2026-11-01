/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.RationalMap.ProjectiveLineModification
public import Aglib.AlgebraicGeometry.Dimension.ClosedPointFibre
public import Aglib.AlgebraicGeometry.Dimension.FieldExtension
public import Aglib.AlgebraicGeometry.Geometrically.Integral.FieldExtension
public import Aglib.AlgebraicGeometry.Limits.ImmersionBaseChange

/-! # Geometric fibre bounds for actual projective-line graph modifications

After any extension of an algebraically closed ground field, the integral
source remains integral and its dimension does not increase. A field-valued
point of the original projective line becomes a closed rational point of
the base-changed line. Surjectivity makes its actual fibre a proper closed
subscheme, so its dimension drops by one.

Together with the native schematic graph construction, this supplies both
geometric fibre bounds for a proper modification without normalization.
These are geometric inputs to a nonsharp auxiliary cohomological dimension
argument, not a claim of the sharp bound `2 * dim X`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

open OverField OverField.Curve.Projectivity ProjectiveLine.TwoChart

universe u

/-- A surjective map from an integral finite-type field scheme to the
projective line has all field-valued fibres of dimension at most `d` when
the source dimension is at most `d + 1`. The ground field is algebraically
closed, but the point's field need not be. -/
theorem Hom.topologicalKrullDim_projectiveLine_geometricFiber_le
    {k : Type u} [Field k] [IsAlgClosed k]
    {Y : Scheme.{u}} [IsIntegral Y]
    (g : Y ⟶ ProjectiveLine.projectiveP1 k) [Surjective g]
    [LocallyOfFiniteType (g ≫ ProjectiveLine.structureMap k)]
    (d : ℕ) (hdim : topologicalKrullDim Y ≤ (d + 1 : ℕ))
    (Ω : Type u) [Field Ω] (η : Spec (.of Ω) ⟶ ProjectiveLine.projectiveP1 k) :
    topologicalKrullDim (pullback (C := Scheme) g η) ≤ (d : ℕ) := by
  let p := ProjectiveLine.structureMap k
  let β := η ≫ p
  let G : Over.mk (g ≫ p) ⟶ Over.mk p := Over.homMk g rfl
  let gΩ : pullback (g ≫ p) β ⟶ pullback p β := ((Over.pullback β).map G).left
  let : Surjective gΩ := MorphismProperty.overPullbackMap (P := @Surjective)
    β G (by change Surjective g; infer_instance)
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (g ≫ p)
  obtain ⟨φ, hφ⟩ := Spec.map_surjective β
  let : IsIntegral (pullback (C := Scheme) (g ≫ p) β) := by
    rw [← hφ]
    let := φ.hom.toAlgebra
    exact Geometrically.isIntegral_fieldBaseChange k Ω (g ≫ p)
  let e : pullback p β ≅ ProjectiveLine.projectiveP1 Ω :=
    pullback.congrHom rfl hφ.symm ≪≫
      ((Over.forget _).mapIso
        (AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct.lineOverBaseChangeIso φ.hom)).symm
  have hline : topologicalKrullDim (pullback (C := Scheme) p β) = 1 := by
    calc
      _ = topologicalKrullDim (ProjectiveLine.projectiveP1 Ω) :=
        IsHomeomorph.topologicalKrullDim_eq _ e.hom.homeomorph.isHomeomorph
      _ = 1 :=
        (IsHomeomorph.topologicalKrullDim_eq _
          (twoChartLineIsoProjectiveP1 Ω).hom.homeomorph.isHomeomorph).symm.trans
            (twoChartLine_topologicalKrullDim Ω)
  let : Nontrivial (pullback (C := Scheme) p β) := by
    apply not_subsingleton_iff_nontrivial.mp
    intro h
    let := h
    have hzero := topologicalKrullDim_zero_of_discreteTopology (pullback (C := Scheme) p β)
    rw [hline] at hzero
    norm_num at hzero
  let ηΩ : Spec (.of Ω) ⟶ pullback p β := pullback.lift η (𝟙 _) (by simp [β])
  let : IsClosedImmersion ηΩ := isClosedImmersion_of_comp_eq_id (pullback.snd p β)
    ηΩ (by dsimp only [ηΩ]; exact pullback.lift_snd _ _ _)
  have Hbase : IsPullback (pullback.fst (g ≫ p) β) gΩ g (pullback.fst p β) :=
    isPullback_overPullbackMap β G
  have Horig : IsPullback (pullback.fst g η) (pullback.snd g η)
      g (ηΩ ≫ pullback.fst p β) := by
    simpa only [ηΩ, pullback.lift_fst] using IsPullback.of_hasPullback g η
  let eF := (Horig.of_right' Hbase).isoPullback
  calc
    topologicalKrullDim (pullback (C := Scheme) g η) =
        topologicalKrullDim (pullback (C := Scheme) gΩ ηΩ) :=
      IsHomeomorph.topologicalKrullDim_eq _ eF.hom.homeomorph.isHomeomorph
    _ ≤ (d : ℕ) := gΩ.topologicalKrullDim_closedPointFiber_le Ω ηΩ d
      (((g ≫ p).topologicalKrullDim_fieldBaseChange_le β).trans hdim)

/-- The actual integral projective-line graph modification has both required
geometric fibre bounds: at most one over its original source and at most
`d` over the line when the source dimension is at most `d + 1`. -/
theorem exists_proper_projectiveLine_graph_modification_with_geometricFiber_bounds
    {k : Type u} [Field k] [IsAlgClosed k] (X : FScheme k)
    [IsIntegral X.left] [IsNoetherian X.left] [IsProper X.hom]
    (d : ℕ) (hpos : 0 < topologicalKrullDim X.left)
    (hdim : topologicalKrullDim X.left ≤ (d + 1 : ℕ)) :
    ∃ (Y : Scheme.{u}) (b : Y ⟶ X.left) (g : Y ⟶ ProjectiveLine.projectiveP1 k),
      IsIntegral Y ∧ IsProper b ∧ Surjective b ∧ IsProper g ∧ IsDominant g ∧
      b ≫ X.hom = g ≫ ProjectiveLine.structureMap k ∧
      (∃ U : X.left.Opens, Nonempty U ∧ Dense (U : Set X.left) ∧ IsIso (b ∣_ U)) ∧
      topologicalKrullDim Y ≤ topologicalKrullDim X.left ∧
      (∀ (Ω : Type u) [Field Ω] (η : Spec (.of Ω) ⟶ X.left),
        topologicalKrullDim (pullback (C := Scheme) b η) ≤ 1) ∧
      ∀ (Ω : Type u) [Field Ω] (η : Spec (.of Ω) ⟶ ProjectiveLine.projectiveP1 k),
        topologicalKrullDim (pullback (C := Scheme) g η) ≤ (d : ℕ) := by
  obtain ⟨Y, b, g, hY, hb, hbs, hg, hgd, hbase, hU, hYdim, hbfib⟩ :=
    exists_proper_projectiveLine_graph_modification X hpos
  let := hY
  let := hg
  let := hgd
  let : Surjective g :=
    surjective_of_isDominant_of_isClosed_range g g.isClosedMap.isClosed_range
  refine ⟨Y, b, g, hY, hb, hbs, hg, hgd, hbase, hU, hYdim, hbfib, ?_⟩
  intro Ω _ η
  exact g.topologicalKrullDim_projectiveLine_geometricFiber_le d (hYdim.trans hdim) Ω η

end AlgebraicGeometry.Scheme
