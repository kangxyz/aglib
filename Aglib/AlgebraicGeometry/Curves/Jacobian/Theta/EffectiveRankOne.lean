/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.RankOne
public import Aglib.AlgebraicGeometry.Curves.Picard.BoundedParameters.Points

/-!
# A rank-one effective class in degree one below the genus

Represent the constructed nonspecial degree-g bundle by its actual
effective divisor. Remove one point from its ordered decomposition. The
remaining divisor has degree g-1, and its original H0 injects into the
one-dimensional H0 of the larger divisor. Its section one is nonzero, so
its section space also has dimension one. This includes g=1, where the
remaining divisor is the empty sum.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry
open Scheme Scheme.Cohomology Scheme.Modules.Invertible Scheme.RelativePicard
open Scheme.OverField.Curve.Divisors

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve

open Picard Picard.DivisorClass Picard.Degree

variable {k : Type u} [Field k] [IsAlgClosed k] {X : FScheme k} (hX : Properties X)
  (P : LocallyNoetherianOver (Spec (.of k)))
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf X.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  [LocallyOfFiniteType P.obj.hom] [IsSeparated P.obj.hom]

include P R

-- Preserve the actual divisor-sheaf and original structural-field cohomology maps.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- In positive genus there is an actual degree-(g-1) line bundle with h0=1,
obtained from an effective sub-divisor of the degree-g rank-one divisor. -/
theorem exists_lineBundle_degree_pred_genus_h0_one (hg : 0 < coherentGenus k X) :
    ∃ L : LineBundle X.left,
      curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
        smoothClosedPointDimension smoothFieldDimension properCurveProductFormula
        X hX (classOf X.left L) = ((coherentGenus k X - 1 : ℕ) : ℤ) ∧
      Module.finrank k (moduleCohomology k X L.val 0) = 1 := by
  let := hX.smooth
  let := hX.proper
  let := PointDivisor.isIntegral_of_properties X hX
  let := curveProperties_isNoetherian hX
  let (x : ClosedPoint X.left) : IsDiscreteValuationRing (X.left.presheaf.stalk x.val) :=
    PointDivisor.isDiscreteValuationRing_stalk X hX x
  let hd := hX.topologicalKrullDim_eq_one
  obtain ⟨L, hLdegree, hL0, -⟩ := exists_lineBundle_degree_genus_h0_one_h1_zero hX P R hg
  have : Nontrivial (moduleCohomology k X L.val 0) := Module.nontrivial_of_finrank_eq_succ hL0
  obtain ⟨s, hs⟩ := exists_ne (0 : moduleCohomology k X L.val 0)
  have hs' : moduleH0Equiv X L.val s ≠ 0 := fun hz =>
    hs ((moduleH0Equiv X L.val).injective (hz.trans (moduleH0Equiv X L.val).map_zero.symm))
  obtain ⟨D, hD, hDL⟩ := exists_effective_divisor_class_of_nonzero_section
    X.left hd.le L (moduleH0Equiv X L.val s) hs'
  obtain ⟨e⟩ := (class_eq_iff X.left (divisorLineBundle X.left hd.le D) L).mp hDL
  have hD0 : Module.finrank k (moduleCohomology k X (divisorSheaf X.left D) 0) = 1 :=
    (moduleCohomologyIso X e 0).finrank_eq.trans hL0
  have hDLdegree : picardDegree X.left X.hom hd.le
      (properCurveProductFormula k X.left X.hom hd) (classOf X.left L) =
        (coherentGenus k X : ℤ) := hLdegree
  have hDdegree : degDiv X.left X.hom D = (coherentGenus k X : ℤ) := by
    rw [← picardDegree_divisor X.left X.hom hd.le
      (properCurveProductFormula k X.left X.hom hd)]
    exact (congrArg (picardDegree X.left X.hom hd.le
      (properCurveProductFormula k X.left X.hom hd)) hDL).trans hDLdegree
  obtain ⟨t, ht⟩ := effective_divisor_eq_sum_points X.left X.hom
    (coherentGenus k X - 1 + 1) D hD (by simpa only [Nat.sub_add_cancel hg] using hDdegree)
  let E : Divisor X.left :=
    ∑ i : Fin (coherentGenus k X - 1), Finsupp.single (t i.succ) 1
  have hDsplit : D = Finsupp.single (t 0) 1 + E := by
    rw [ht, Fin.sum_univ_succ]
  have hE : ∀ x, 0 ≤ E x := by
    intro x
    dsimp only [E]
    rw [Finsupp.finsetSum_apply]
    apply Finset.sum_nonneg
    intro i _
    by_cases hx : x = t i.succ <;> simp [hx]
  have hED : E ≤ D := by
    intro x
    rw [hDsplit, Finsupp.add_apply]
    have hnonneg : 0 ≤ (Finsupp.single (t 0) (1 : ℤ)) x := by
      by_cases hx : x = t 0 <;> simp [hx]
    omega
  have hEdegree : degDiv X.left X.hom E = ((coherentGenus k X - 1 : ℕ) : ℤ) := by
    simp only [E, map_sum, degDiv_single, weight_eq_one, mul_one,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : Mono (divisorInclusion X.left hED) := divisorInclusion_mono X.left hED
  have hinj := moduleH0Map_injective X (divisorInclusion X.left hED)
  have : Module.Finite k (moduleCohomology k X (divisorSheaf X.left D) 0) :=
    Module.finite_of_finrank_eq_succ hD0
  have : Module.Finite k (moduleCohomology k X (divisorSheaf X.left E) 0) :=
    Module.Finite.of_injective (moduleCohomologyMap X (divisorInclusion X.left hED) 0) hinj
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rw [hD0] at hle
  obtain ⟨u, hu⟩ := divisorSheaf_exists_nonzero_section_of_effective X.left E hE
  let v := (moduleH0Equiv X (divisorSheaf X.left E)).symm u
  have hv : v ≠ 0 := by
    intro hv
    apply hu
    simpa only [v, LinearEquiv.apply_symm_apply, map_zero] using
      congrArg (moduleH0Equiv X (divisorSheaf X.left E)) hv
  have hne : Module.finrank k (moduleCohomology k X (divisorSheaf X.left E) 0) ≠ 0 := by
    intro hz
    have : Subsingleton (moduleCohomology k X (divisorSheaf X.left E) 0) :=
      Module.finrank_zero_iff.mp hz
    exact hv (Subsingleton.elim _ _)
  refine ⟨divisorLineBundle X.left hd.le E, ?_, ?_⟩
  · exact (lineBundleDegree_divisor X.left X.hom hd.le
      (properCurveProductFormula k X.left X.hom hd) E).trans hEdegree
  · change Module.finrank k (moduleCohomology k X (divisorSheaf X.left E) 0) = 1
    omega

end AlgebraicGeometry.Scheme.OverField.Curve
