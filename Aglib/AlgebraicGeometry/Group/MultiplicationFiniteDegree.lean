/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.MultiplicationDegree
public import Aglib.AlgebraicGeometry.FunctionField.StalkMap
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Finite flat multiplication at every positive level

The degree is the schematic rank of the original multiplication morphism.
Positive levels need not be units in the field. Inseparable multiplicities are
retained; no geometric point-count assertion is made at noninvertible levels.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve

/-- A dominant map of the actual smooth curves is flat: every target stalk is
a field or a DVR, and the actual stalk map is injective. -/
theorem dominant_flat {k : Type u} [Field k] {X Y : FScheme k}
    (hX : Properties X) (hY : Properties Y) (f : X ⟶ Y) [IsDominant f.left] :
    Flat f.left := by
  let : IsIntegral X.left := hX.isIntegral
  let : IsIntegral Y.left := hY.isIntegral
  have hdvr (y : Y.left) : IsDedekindDomain (Y.left.presheaf.stalk y) := by
    rcases DimensionOne.point_eq_generic_or_isClosed Y.left
        (curveProperties_dimension smoothFieldDimension hY).le y with rfl | hy
    · change IsDedekindDomain Y.left.functionField
      infer_instance
    · let : IsDiscreteValuationRing (Y.left.presheaf.stalk y) :=
        curveProperties_closedPoint_stalk_dvr smoothFieldNormality smoothFieldRegularity
          smoothClosedPointDimension hY y hy
      infer_instance
  apply Flat.of_stalkMap
  intro x
  let := (f.left.stalkMap x).hom.toAlgebra
  let : IsDedekindDomain (Y.left.presheaf.stalk (f.left x)) := hdvr (f.left x)
  have hinj : Function.Injective (f.left.stalkMap x).hom := by
    intro a b hab
    apply IsFractionRing.injective (Y.left.presheaf.stalk (f.left x)) Y.left.functionField
    apply Scheme.functionFieldMap_injective f.left
    rw [Scheme.functionFieldMap_stalk, Scheme.functionFieldMap_stalk, hab]
  let : Module.IsTorsionFree (Y.left.presheaf.stalk (f.left x))
      (X.left.presheaf.stalk x) := Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  exact inferInstanceAs (Module.Flat (Y.left.presheaf.stalk (f.left x))
    (X.left.presheaf.stalk x))

end AlgebraicGeometry.Scheme.OverField.Curve

namespace AlgebraicGeometry.Scheme.Group.Multiplication

attribute [local instance] Over.cartesianMonoidalCategory
variable {k : Type u} [Field k] (G : Grp (FScheme k))

local notation "curveDegree" => Curve.curveDegree smoothFieldNormality normalComponentsOpen
  smoothFieldRegularity smoothClosedPointDimension smoothFieldDimension
  Curve.Picard.Degree.properCurveProductFormula G.X

/-- The positive-level square formula rules out the constant origin map,
including levels divisible by the characteristic. -/
theorem multiplication_ne_one_of_pos_of_isAlgClosed [IsAlgClosed k]
    (hG : Curve.Properties G.X) (hg : Curve.coherentGenus k G.X = 1)
    (n : ℕ) (hn : 0 < n) : (𝟙 G.X) ^ n ≠ 1 := by
  let : SmoothOfRelativeDimension 1 G.X.hom := hG.smooth
  let : IsProper G.X.hom := hG.proper
  intro hconst
  have h := pullback_twice_identityIdealClass G hG hg n
  have hz : pullbackClass (1 : G.X ⟶ G.X).left (2 • identityIdealClass G) = 0 := by
    change pullbackHom moduleTensorPullback (1 : G.X ⟶ G.X).left
      (2 • identityIdealClass G) = 0
    rw [map_nsmul, pullbackHom_apply, pullback_identityIdealClass_one, nsmul_zero]
  rw [hconst, hz] at h
  have hdegree := congrArg (curveDegree hG) h
  rw [map_zero, map_nsmul, map_nsmul, identityIdealClass_curveDegree] at hdegree
  have hpos : (0 : ℤ) < (n * n : ℕ) := by exact_mod_cast Nat.mul_pos hn hn
  norm_num [nsmul_eq_mul] at hdegree
  omega

/-- Literal multiplication by every positive level is nonconstant over the
original arbitrary field. -/
theorem multiplication_ne_one_of_pos (hG : Curve.Properties G.X)
    (hg : Curve.coherentGenus k G.X = 1) (n : ℕ) (hn : 0 < n) :
    (𝟙 G.X) ^ n ≠ 1 := by
  let K := AlgebraicClosure k
  let s : Spec (.of K) ⟶ Base k := Spec.algebraMap k K
  let P := Over.pullback s
  let B := Scheme.Group.BaseChange.groupSchemeBaseChange s
  let G' := B.functor.obj G
  let : GrpObj (P.obj G.X) := Functor.grpObjObj
  have hG' : Curve.Properties G'.X :=
    { smooth := MorphismProperty.pullback_snd G.X.hom s hG.smooth
      proper := MorphismProperty.pullback_snd G.X.hom s hG.proper
      connected := MorphismProperty.pullback_snd G.X.hom s hG.connected }
  have hg' : Curve.coherentGenus K G'.X = 1 :=
    (Curve.coherentGenus_fieldBaseChange K Cohomology.properStructureCohomologyBaseChange
      G.X hG).trans hg
  have hpow : P.map ((𝟙 G.X) ^ n) = (𝟙 G'.X) ^ n := by
    change P.map ((𝟙 G.X) ^ n) = (𝟙 (P.obj G.X)) ^ n
    calc
      _ = (P.map (𝟙 G.X)) ^ n := (P.homMonoidHom (X := G.X) (M := G.X)).map_pow _ _
      _ = _ := by rw [CategoryTheory.Functor.map_id]
  intro hconst
  apply multiplication_ne_one_of_pos_of_isAlgClosed G' hG' hg' n hn
  rw [← hpow, hconst, Functor.map_one]

/-- Literal multiplication is finite, flat, and surjective for every positive
level in every characteristic. -/
theorem multiplication_finite_flat_surjective_of_pos (hG : Curve.Properties G.X)
    (hg : Curve.coherentGenus k G.X = 1) (n : ℕ) (hn : 0 < n) :
    IsFinite ((𝟙 G.X) ^ n).left ∧ Flat ((𝟙 G.X) ^ n).left ∧
      Surjective ((𝟙 G.X) ^ n).left := by
  have hne := multiplication_ne_one_of_pos G hG hg n hn
  obtain ⟨hf, hs⟩ := multiplication_finite_surjective_of_ne_one G hG n hne
  let : IsDominant ((𝟙 G.X) ^ n).left :=
    Curve.pointed_nonconstant_isDominant G G hG hG _ (multiplication_pointed G n) hne
  exact ⟨hf, Curve.dominant_flat hG hG _, hs⟩

/-- The actual direct-image structure sheaf has rank `n*n` over an
algebraically closed field, with no separability hypothesis. -/
theorem multiplication_hasLocallyFreeRank_of_pos_of_isAlgClosed [IsAlgClosed k]
    (hG : Curve.Properties G.X) (hg : Curve.coherentGenus k G.X = 1)
    (n : ℕ) (hn : 0 < n) : HasLocallyFreeRank ((𝟙 G.X) ^ n).left (n * n) := by
  let : SmoothOfRelativeDimension 1 G.X.hom := hG.smooth
  let : IsProper G.X.hom := hG.proper
  let : ConnectedSpace G.X.left := Curve.curveProperties_connectedSpace hG
  let : IsNoetherian G.X.left := Curve.curveProperties_isNoetherian hG
  obtain ⟨hf, hflat, hs⟩ := multiplication_finite_flat_surjective_of_pos G hG hg n hn
  let := hf
  let := hflat
  let := hs
  have hfree := finiteFlatPresentationLocallyFree _ _ ((𝟙 G.X) ^ n).left
    hf hflat inferInstance
  obtain ⟨d, hd⟩ := exists_hasLocallyFreeRank ((𝟙 G.X) ^ n).left hfree
  have hscale := Curve.curveDegree_pullback_of_hasLocallyFreeRank smoothFieldNormality
    normalComponentsOpen smoothFieldRegularity smoothClosedPointDimension smoothFieldDimension
    Curve.Picard.Degree.properCurveProductFormula Scheme.Modules.affineModuleBaseChange
    FiniteFlat.finiteDominantGenericFibre Curve.Picard.NormDegree.finiteMorphismNormOrder
    ((𝟙 G.X) ^ n) hG hG d hd (2 • identityIdealClass G)
  have hQ : curveDegree hG (2 • identityIdealClass G) = -2 := by
    rw [map_nsmul, identityIdealClass_curveDegree]
    norm_num
  rw [pullback_twice_identityIdealClass G hG hg n, map_nsmul, hQ] at hscale
  have hd' : d = n * n := by
    have heq : (d : ℤ) = (n * n : ℕ) := by
      simp only [nsmul_eq_mul] at hscale
      linarith
    exact_mod_cast heq
  exact hd' ▸ hd

/-- The native scheme-theoretic rank of positive-level multiplication is the
square of the level at every point of the original curve over any field. -/
theorem multiplication_nativeRank_of_pos (hG : Curve.Properties G.X)
    (hg : Curve.coherentGenus k G.X = 1) (n : ℕ) (hn : 0 < n) (y : G.X.left) :
    ((𝟙 G.X) ^ n).left.finrank y = n * n := by
  obtain ⟨hf, hflat, hs⟩ := multiplication_finite_flat_surjective_of_pos G hG hg n hn
  let := hf
  let := hflat
  let := hs
  let : IsMonHom ((𝟙 G.X) ^ n) :=
    Curve.pointedMorphism_of_curveProperties G G hG hG _ (multiplication_pointed G n)
  let f : G ⟶ G := Grp.ofHom ((𝟙 G.X) ^ n)
  let : IsFinite f.hom.hom.left := hf
  let : Flat f.hom.hom.left := hflat
  let K := AlgebraicClosure k
  let s : Spec (.of K) ⟶ Base k := Spec.algebraMap k K
  let P := Over.pullback s
  let B := Scheme.Group.BaseChange.groupSchemeBaseChange s
  let G' := B.functor.obj G
  let f' := B.functor.map f
  let : GrpObj (P.obj G.X) := Functor.grpObjObj
  have hSquare : IsPullback (pullback.fst G.X.hom s) f'.hom.hom.left
      f.hom.hom.left (pullback.fst G.X.hom s) := by
    apply IsPullback.flip
    apply IsPullback.of_right (h₁₂ := pullback.snd G.X.hom s)
      (h₂₂ := G.X.hom) (v₁₃ := s)
      _ (Scheme.Group.BaseChange.groupSchemeBaseChange_map_left_fst s f)
      (IsPullback.of_hasPullback G.X.hom s).flip
    simpa only [Scheme.Group.BaseChange.groupSchemeBaseChange_map_left_snd, Over.w] using
      (IsPullback.of_hasPullback G.X.hom s).flip
  have hG' : Curve.Properties G'.X :=
    { smooth := MorphismProperty.pullback_snd G.X.hom s hG.smooth
      proper := MorphismProperty.pullback_snd G.X.hom s hG.proper
      connected := MorphismProperty.pullback_snd G.X.hom s hG.connected }
  have hg' : Curve.coherentGenus K G'.X = 1 :=
    (Curve.coherentGenus_fieldBaseChange K Cohomology.properStructureCohomologyBaseChange
      G.X hG).trans hg
  have hpow : f'.hom.hom = (𝟙 G'.X) ^ n := by
    change P.map ((𝟙 G.X) ^ n) = (𝟙 (P.obj G.X)) ^ n
    calc
      _ = (P.map (𝟙 G.X)) ^ n := (P.homMonoidHom (X := G.X) (M := G.X)).map_pow _ _
      _ = _ := by rw [CategoryTheory.Functor.map_id]
  have hrank' : HasLocallyFreeRank f'.hom.hom.left (n * n) := by
    rw [hpow]
    exact multiplication_hasLocallyFreeRank_of_pos_of_isAlgClosed G' hG' hg' n hn
  let : IsFinite f'.hom.hom.left := MorphismProperty.of_isPullback hSquare hf
  let : Flat f'.hom.hom.left := MorphismProperty.of_isPullback hSquare hflat
  let : Surjective s := ⟨Function.surjective_to_subsingleton s⟩
  obtain ⟨y', hy'⟩ := (pullback.fst G.X.hom s).surjective y
  change f.hom.hom.left.finrank y = n * n
  rw [← hy']
  exact (Scheme.Hom.finrank_of_isPullback _ _ _ _ hSquare y').symm.trans
    ((FiniteFlat.nativeRank_eq_locallyFreeRank f'.hom.hom.left
      Scheme.Modules.affineModuleBaseChange y').trans
      ((hasLocallyFreeRank_iff_rank_eq _ hrank'.finiteLocallyFree _).mp hrank' y'))

/-- Positive-level multiplication has actual locally free rank `n*n` over any
field, including inseparable levels. -/
theorem multiplication_hasLocallyFreeRank_of_pos (hG : Curve.Properties G.X)
    (hg : Curve.coherentGenus k G.X = 1) (n : ℕ) (hn : 0 < n) :
    HasLocallyFreeRank ((𝟙 G.X) ^ n).left (n * n) := by
  obtain ⟨hf, hflat, _⟩ := multiplication_finite_flat_surjective_of_pos G hG hg n hn
  let := hf
  let := hflat
  let : IsNoetherian G.X.left := Curve.curveProperties_isNoetherian hG
  have hfree := finiteFlatPresentationLocallyFree _ _ ((𝟙 G.X) ^ n).left
    hf hflat inferInstance
  apply (hasLocallyFreeRank_iff_rank_eq _ hfree _).mpr
  intro y
  exact (FiniteFlat.nativeRank_eq_locallyFreeRank ((𝟙 G.X) ^ n).left
    Scheme.Modules.affineModuleBaseChange y).symm.trans
    (multiplication_nativeRank_of_pos G hG hg n hn y)

/-- The full finite-flat multiplication conclusion at an arbitrary positive
level. This rank includes the multiplicities of nonreduced fibres. -/
theorem multiplication_finite_flat_degree (hG : Curve.Properties G.X)
    (hg : Curve.coherentGenus k G.X = 1) (n : ℕ) (hn : 0 < n) :
    IsFinite ((𝟙 G.X) ^ n).left ∧ Flat ((𝟙 G.X) ^ n).left ∧
      Surjective ((𝟙 G.X) ^ n).left ∧
        HasLocallyFreeRank ((𝟙 G.X) ^ n).left (n * n) :=
  ⟨(multiplication_finite_flat_surjective_of_pos G hG hg n hn).1,
    (multiplication_finite_flat_surjective_of_pos G hG hg n hn).2.1,
    (multiplication_finite_flat_surjective_of_pos G hG hg n hn).2.2,
    multiplication_hasLocallyFreeRank_of_pos G hG hg n hn⟩

end AlgebraicGeometry.Scheme.Group.Multiplication
