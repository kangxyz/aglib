/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Eval.PairEvaluation
public import Aglib.AlgebraicGeometry.Surfaces.PowerNode.Comparison.StrictTransformRecognition

/-!
Native extraction from the R5 local-model source
`CyclicModelComparison.StrictExceptionalFibres`.
R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`8865ef70ebd310c8a08a5efa095532a1f49210882e4a4f8e784271cb14b81ab0`.
Actual scheme-theoretic strict/exceptional pullbacks and original critical-normalization node
  fibre. Original distinct roots, residue structural maps and both point projections remain fixed;
  support conclusions are proved from those maps, without endpoint records.
Conditional blowup families remain explicit inputs.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Polynomial
open scoped Polynomial
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.PowerNode WeierstrassCurve
open AlgebraicGeometry.Scheme.FunctionField AlgebraicGeometry.Scheme.FunctionField.GenericExtension
open AlgebraicGeometry.Scheme.Hom.Range AlgebraicGeometry.Scheme.Pullback.Fibre

/-!
# Original node fibres and strict/exceptional two-point support

This module preserves the conditional interfaces and source-coverage boundaries
recorded in the individual sections below.
-/

section StrictExceptionalOriginalFibre

/-! The strict P1 intersection with the entire actual exceptional scheme is
the actual original normalization's node fibre, by literal pullback pasting.
No reducedness of the exceptional scheme and no endpoint relabelling is used. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open WeierstrassCurve.CriticalNeighborhood WeierstrassCurve.Projective
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {W : WeierstrassCurve R} {x y : ResidueField R}
  (M : WeierstrassCurve.CriticalNeighborhood W x y) (π : R) (hπ : Irreducible π) (n : ℕ) (hn : 0 <
    n)
  (a : M.Carrierˣ) (ha : M.translated.a₆ = (a : M.Carrier) * algebraMap R M.Carrier (π ^ n))
  (he : (W.map (IsLocalRing.residue R)).toAffine.Equation x y)
  (ρ : ResidueField R) (hρ : WeierstrassCurve.CriticalNeighborhood.SplitTangent (W := W) (x := x)
    (y := y) ρ)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u})
  (hx : (W.map (IsLocalRing.residue R)).toAffine.polynomialX.evalEval x y = 0)
  (hy : (W.map (IsLocalRing.residue R)).toAffine.polynomialY.evalEval x y = 0)
  (H :
    AlgebraicGeometry.Scheme.FunctionField.GenericExtension.NormalProperCurveGenericExtension.{u})
local notation "f" => strictP1ToFinal M π hπ n hn a ha he ρ hρ hex hp hatlas hbc hx hy H
local notation "e" => originalExceptionalToSpecial M π hπ n hn a ha he ρ hρ hex hp hatlas hbc
local notation "E" => Resolution.resolve π hπ hex hp hatlas n
local notation "p" => NextCenter.origin π hπ n hn

lemma strictExceptionalOriginal_square :
    IsPullback (pullback.fst f e)
      (pullback.snd f e ≫ pullback.snd (E).map p)
      (originalSpecialNormalization he hx hy H) (originalSpecialNode he) := by
  have h := (IsPullback.of_hasPullback f e).paste_vert
    (originalExceptionalToSpecial_square M π hπ n hn a ha he ρ hρ hex hp hatlas hbc)
  simpa only [strictP1ToFinal_original] using h

/-- The actual maps to the original P1 and original residue point are retained. -/
def strictExceptionalOriginalIso : pullback f e ≅
    pullback (originalSpecialNormalization he hx hy H) (originalSpecialNode he) :=
  (strictExceptionalOriginal_square M π hπ n hn a ha he ρ hρ hex hp hatlas hbc hx hy H).isoPullback

@[reassoc] lemma strictExceptionalOriginalIso_hom_fst :
    (strictExceptionalOriginalIso M π hπ n hn a ha he ρ hρ hex hp hatlas hbc hx hy H).hom ≫
      pullback.fst (originalSpecialNormalization he hx hy H) (originalSpecialNode he) =
        pullback.fst f e :=
  (strictExceptionalOriginal_square M π hπ n hn a ha he ρ hρ hex hp hatlas hbc hx hy
    H).isoPullback_hom_fst

@[reassoc] lemma strictExceptionalOriginalIso_hom_snd :
    (strictExceptionalOriginalIso M π hπ n hn a ha he ρ hρ hex hp hatlas hbc hx hy H).hom ≫
      pullback.snd (originalSpecialNormalization he hx hy H) (originalSpecialNode he) =
        pullback.snd f e ≫ pullback.snd (E).map p :=
  (strictExceptionalOriginal_square M π hπ n hn a ha he ρ hρ hex hp hatlas hbc hx hy
    H).isoPullback_hom_snd

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale

end -- noncomputable section
end StrictExceptionalOriginalFibre


section WeierstrassCurve.CriticalCubic.OriginFibre

/-! The actual scheme-theoretic origin fibre of the literal critical-cubic
normalization is the reduced two-point scheme, over the original field. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry Polynomial
universe u
namespace WeierstrassCurve.CriticalCubic.OriginFibre
variable (k : Type u) [Field k] (A B ρ σ : k)


variable (hρ : ρ ^ 2 + A * ρ - B = 0)
  (hσ : σ ^ 2 + A * σ - B = 0) (hneq : ρ ≠ σ)
include hρ hσ hneq

lemma root_sum : ρ + σ = -A := by
  have hprod : (ρ - σ) * (ρ + σ + A) = 0 := by
    linear_combination hρ - hσ
  have h := (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hneq)
  linear_combination h

lemma root_product : ρ * σ = -B := by
  have hs := root_sum k A B ρ σ hρ hσ hneq
  linear_combination ρ * hs - hρ

lemma parameter_factorization :
    WeierstrassCurve.CriticalCubic.xPolynomial k A B = (X - C ρ) * (X - C σ) := by
  have hs := root_sum k A B ρ σ hρ hσ hneq
  have hp := root_product k A B ρ σ hρ hσ hneq
  calc
    WeierstrassCurve.CriticalCubic.xPolynomial k A B = X ^ 2 - C (ρ + σ) * X + C (ρ * σ) := by
      rw [hs, hp]
      simp only [WeierstrassCurve.CriticalCubic.xPolynomial, map_neg]
      ring
    _ = (X - C ρ) * (X - C σ) := by
      simp only [map_add, map_mul]
      ring

lemma pairedEvaluation_ker_parameter :
    RingHom.ker (pairedEvaluation k ρ σ) = Ideal.span {WeierstrassCurve.CriticalCubic.xPolynomial
      k A B} := by
  rw [pairedEvaluation_ker k ρ σ hneq, parameter_factorization k A B ρ σ hρ hσ hneq]

local notation "CubicRing" => WeierstrassCurve.Affine.CoordinateRing
  (WeierstrassCurve.toAffine (WeierstrassCurve.CriticalCubic.equation k A B))

omit hneq in
/-- The actual normalization/origin coordinate square commutes. -/
lemma coordinate_square :
    (pairedEvaluation k ρ σ).comp (WeierstrassCurve.CriticalCubic.coordinateMap k A B).toRingHom =
      (algebraMap k (k × k)).comp (WeierstrassCurve.CriticalCubic.originMap k A B).toRingHom := by
  apply RingHom.ext
  intro z
  apply Prod.ext
  · exact congrArg (fun f : CubicRing →ₐ[k] k => f z)
      ((WeierstrassCurve.CriticalCubic.eval_coordinateMap_eq_origin_iff k A B ρ).mpr hρ)
  · exact congrArg (fun f : CubicRing →ₐ[k] k => f z)
      ((WeierstrassCurve.CriticalCubic.eval_coordinateMap_eq_origin_iff k A B σ).mpr hσ)

/-- The full pushout universal property follows from the actual coordinate X,
whose normalization pullback is P and whose origin value is zero. -/
theorem origin_isPushout :
    IsPushout (CommRingCat.ofHom (WeierstrassCurve.CriticalCubic.coordinateMap k A B).toRingHom)
      (CommRingCat.ofHom (WeierstrassCurve.CriticalCubic.originMap k A B).toRingHom)
      (CommRingCat.ofHom (pairedEvaluation k ρ σ))
      (CommRingCat.ofHom (algebraMap k (k × k))) := by
  apply IsPushout.mk'
  · apply CommRingCat.hom_ext
    exact coordinate_square k A B ρ σ hρ hσ
  · intro T φ φ' h _
    ext z
    obtain ⟨p, rfl⟩ := pairedEvaluation_surjective k ρ σ hneq z
    exact congrArg (fun f : CommRingCat.of k[X] ⟶ T => f p) h
  · intro T a b h
    let q := pairedEvaluation k ρ σ
    have hp : a.hom (WeierstrassCurve.CriticalCubic.xPolynomial k A B) = 0 := by
      have hx := congrArg (fun f : CommRingCat.of CubicRing ⟶ T =>
        f (WeierstrassCurve.affineX (WeierstrassCurve.CriticalCubic.equation k A B))) h
      change a (WeierstrassCurve.CriticalCubic.coordinateMap k A B
        (WeierstrassCurve.affineX (WeierstrassCurve.CriticalCubic.equation k A B))) =
        b (WeierstrassCurve.CriticalCubic.originMap k A B
          (WeierstrassCurve.affineX (WeierstrassCurve.CriticalCubic.equation k A B))) at hx
      simpa only [WeierstrassCurve.CriticalCubic.coordinateMap_X,
        WeierstrassCurve.CriticalCubic.originMap_X, map_zero] using hx
    have hk : RingHom.ker q ≤ RingHom.ker a.hom := by
      rw [show q = pairedEvaluation k ρ σ from rfl,
        pairedEvaluation_ker_parameter k A B ρ σ hρ hσ hneq]
      apply Ideal.span_le.mpr
      intro p hmem
      rw [Set.mem_singleton_iff] at hmem
      subst p
      exact hp
    let d : k × k →+* T := q.liftOfSurjective (pairedEvaluation_surjective k ρ σ hneq) ⟨a.hom, hk⟩
    have hd (p : k[X]) : d (q p) = a p :=
      RingHom.liftOfSurjective_comp_apply q (pairedEvaluation_surjective k ρ σ hneq) ⟨a.hom, hk⟩ p
    refine ⟨CommRingCat.ofHom d, ?_, ?_⟩
    · apply CommRingCat.hom_ext
      exact RingHom.ext hd
    · apply CommRingCat.hom_ext
      apply RingHom.ext
      intro c
      have hc := congrArg (fun f : CommRingCat.of CubicRing ⟶ T =>
        f (algebraMap k CubicRing c)) h
      have hab : a (C c) = b c := by
        change a (WeierstrassCurve.CriticalCubic.coordinateMap k A B (algebraMap k CubicRing c)) =
          b (WeierstrassCurve.CriticalCubic.originMap k A B (algebraMap k CubicRing c)) at hc
        simpa only [AlgHom.commutes, Polynomial.algebraMap_eq, Algebra.algebraMap_self_apply]
          using hc
      change d (c, c) = b c
      rw [← pairedEvaluation_C k ρ σ c]
      exact (hd (C c)).trans hab

/-- The actual affine normalization's origin fibre, scheme-theoretically. -/
theorem originFibre_isPullback :
    IsPullback (Spec.map (CommRingCat.ofHom (pairedEvaluation k ρ σ)))
      (Spec.map (CommRingCat.ofHom (algebraMap k (k × k))))
      (WeierstrassCurve.CriticalCubic.affineNormalization k A B)
        (WeierstrassCurve.CriticalCubic.originSection k A B) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (origin_isPushout k A B ρ σ hρ hσ hneq)

/-- An actual fibre isomorphism, carrying its original residue-field structure. -/
def originFibreIso :
    pullback (WeierstrassCurve.CriticalCubic.affineNormalization k A B)
      (WeierstrassCurve.CriticalCubic.originSection k A B) ≅
      Spec (.of (k × k)) :=
  (originFibre_isPullback k A B ρ σ hρ hσ hneq).isoPullback.symm

lemma originFibreIso_structure :
    (originFibreIso k A B ρ σ hρ hσ hneq).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (k × k))) = pullback.snd _ _ := by
  simp [originFibreIso]

lemma originFibreIso_toLine :
    (originFibreIso k A B ρ σ hρ hσ hneq).hom ≫
      Spec.map (CommRingCat.ofHom (pairedEvaluation k ρ σ)) = pullback.fst _ _ := by
  simp [originFibreIso]

/-- The same fibre isomorphism in the category over the original field. -/
def originFibreOverIso :
    Over.mk (pullback.snd (WeierstrassCurve.CriticalCubic.affineNormalization k A B)
      (WeierstrassCurve.CriticalCubic.originSection k A B)) ≅
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (k × k)))) :=
  Over.isoMk (originFibreIso k A B ρ σ hρ hσ hneq)
    (originFibreIso_structure k A B ρ σ hρ hσ hneq)

end WeierstrassCurve.CriticalCubic.OriginFibre

end -- noncomputable section
end WeierstrassCurve.CriticalCubic.OriginFibre


section OriginalNormalizationNodeFibre

/-! Transport the actual two-root affine normalization fibre through the proved
normalization chart and original coefficient isomorphism. The original node,
P1 source, field structure and both evaluation coordinates are unchanged. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open AlgebraicGeometry.Scheme.FunctionField.GenericExtension
open WeierstrassCurve.Projective
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale
attribute [local instance] specialFibre_isIntegral
  WeierstrassCurve.Projective.scheme_isIntegral_of_isDomain
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {W : WeierstrassCurve R} {x y : ResidueField R}
  (he : (W.map (IsLocalRing.residue R)).toAffine.Equation x y)
local notation "k" => ResidueField R

@[reassoc] lemma affineNode_coefficient :
    (affinePointOver (W.map (IsLocalRing.residue R)) x y he).left ≫
      affineChart (W.map (IsLocalRing.residue R)) ≫
      (specialCoefficientIso W).hom = originalSpecialNode he := by
  apply pullback.hom_ext
  · simp only [Category.assoc, specialCoefficientIso_hom_fst, originalSpecialNode_fst]
    change Spec.map (CommRingCat.ofHom (affinePointEval (W.map (IsLocalRing.residue R)) x y he)) ≫
      affineChart (W.map (IsLocalRing.residue R)) ≫
        coefficientSchemeMap W (IsLocalRing.residue R) = _
    rw [affineChart_coefficient, ← Category.assoc, ← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom
      ((affinePointEval (W.map (IsLocalRing.residue R)) x y he).comp
        (affineCoefficientMap W (IsLocalRing.residue R)))) ≫ affineChart W = residueNodeMap W x y he
    rw [affinePointEval_comp_residueCoefficient]
    rfl
  · simp only [Category.assoc, specialCoefficientIso_hom_snd, originalSpecialNode_snd]
    change (affinePointOver (W.map (IsLocalRing.residue R)) x y he).left ≫
      affineChart (W.map (IsLocalRing.residue R)) ≫
        structureMap (W.map (IsLocalRing.residue R)) = 𝟙 _
    rw [affineChart_structure]
    exact (affinePointOver (W.map (IsLocalRing.residue R)) x y he).w

variable (hx : (W.map (IsLocalRing.residue R)).toAffine.polynomialX.evalEval x y = 0)
  (hy : (W.map (IsLocalRing.residue R)).toAffine.polynomialY.evalEval x y = 0)
  (H : NormalProperCurveGenericExtension.{u})
  (ρ σ : ResidueField R)
  (hρ : ρ ^ 2 + (W.map (IsLocalRing.residue R)).a₁ * ρ -
    ((W.map (IsLocalRing.residue R)).a₂ + 3 * x) = 0)
  (hσ : σ ^ 2 + (W.map (IsLocalRing.residue R)).a₁ * σ -
    ((W.map (IsLocalRing.residue R)).a₂ + 3 * x) = 0)
  (hne : ρ ≠ σ)

include hρ hσ hne

/-- The entire scheme-theoretic node fibre of the original normalization. -/
lemma originalNormalizationNode_isPullback :
    IsPullback
      (Spec.map (CommRingCat.ofHom (Polynomial.pairedEvaluation k ρ σ)) ≫
        ProjectiveLine.chart k 0)
      (Spec.map (CommRingCat.ofHom (algebraMap k (k × k))))
      (originalSpecialNormalization he hx hy H) (originalSpecialNode he) := by
  have h := (WeierstrassCurve.CriticalCubic.OriginFibre.originFibre_isPullback k
    (W.map (IsLocalRing.residue R)).a₁ ((W.map (IsLocalRing.residue R)).a₂ + 3 * x)
      ρ σ hρ hσ hne).paste_horiz
      (WeierstrassCurve.CriticalCubic.TargetNormalization.normalization_affine_isPullback k
        (W.map (IsLocalRing.residue R)).a₁ ((W.map (IsLocalRing.residue R)).a₂ + 3 * x)
        (structureMap (W.map (IsLocalRing.residue R)))
        (WeierstrassCurve.CriticalCubic.SingularNormalization.criticalChart
          (W.map (IsLocalRing.residue R)) x y he hx hy)
        (WeierstrassCurve.CriticalCubic.SingularNormalization.criticalChart_structure (W.map
          (IsLocalRing.residue R)) x y he hx hy) H)
  apply h.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (specialCoefficientIso W)
  · simp
  · simp
  · rfl
  · simpa only [Iso.refl_hom, Category.id_comp, Category.assoc,
      WeierstrassCurve.CriticalCubic.SingularNormalization.criticalChart_origin] using
        affineNode_coefficient he

/-- The isomorphism preserves the actual original residue projection. -/
def originalNormalizationNodeIso :
    pullback (originalSpecialNormalization he hx hy H) (originalSpecialNode he) ≅ Spec (.of (k ×
      k)) :=
  (originalNormalizationNode_isPullback he hx hy H ρ σ hρ hσ hne).isoPullback.symm

@[reassoc] lemma originalNormalizationNodeIso_structure :
    (originalNormalizationNodeIso he hx hy H ρ σ hρ hσ hne).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (k × k))) =
        pullback.snd (originalSpecialNormalization he hx hy H) (originalSpecialNode he) := by
  simp [originalNormalizationNodeIso]

@[reassoc] lemma originalNormalizationNodeIso_toP1 :
    (originalNormalizationNodeIso he hx hy H ρ σ hρ hσ hne).hom ≫
      Spec.map (CommRingCat.ofHom (Polynomial.pairedEvaluation k ρ σ)) ≫
        ProjectiveLine.chart k 0 =
      pullback.fst (originalSpecialNormalization he hx hy H) (originalSpecialNode he) := by
  simpa only [originalNormalizationNodeIso, Iso.symm_hom, Category.assoc] using
    (originalNormalizationNode_isPullback he hx hy H ρ σ hρ hσ hne).isoPullback_inv_fst

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale

end -- noncomputable section
end OriginalNormalizationNodeFibre


section StrictExceptionalTwoPoint

/-! The actual strict-P1/whole-exceptional intersection is exactly the original
split two-root scheme over the original residue field. This computation does
not assume or require the whole exceptional fibre to be reduced. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open WeierstrassCurve.CriticalNeighborhood WeierstrassCurve.Projective
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {W : WeierstrassCurve R} {x y : ResidueField R}
  (M : WeierstrassCurve.CriticalNeighborhood W x y) (π : R) (hπ : Irreducible π) (n : ℕ) (hn : 0 <
    n)
  (a : M.Carrierˣ) (ha : M.translated.a₆ = (a : M.Carrier) * algebraMap R M.Carrier (π ^ n))
  (he : (W.map (IsLocalRing.residue R)).toAffine.Equation x y)
  (ρ : ResidueField R) (hρ : WeierstrassCurve.CriticalNeighborhood.SplitTangent (W := W) (x := x)
    (y := y) ρ)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u})
  (hx : (W.map (IsLocalRing.residue R)).toAffine.polynomialX.evalEval x y = 0)
  (hy : (W.map (IsLocalRing.residue R)).toAffine.polynomialY.evalEval x y = 0)
  (H :
    AlgebraicGeometry.Scheme.FunctionField.GenericExtension.NormalProperCurveGenericExtension.{u})
  (σ : ResidueField R) (hσ : WeierstrassCurve.CriticalNeighborhood.SplitTangent (W := W) (x := x)
    (y := y) σ)
  (hne : ρ ≠ σ)
local notation "k" => ResidueField R
local notation "f" => strictP1ToFinal M π hπ n hn a ha he ρ hρ hex hp hatlas hbc hx hy H
local notation "e" => originalExceptionalToSpecial M π hπ n hn a ha he ρ hρ hex hp hatlas hbc
local notation "E" => Resolution.resolve π hπ hex hp hatlas n
local notation "p" => NextCenter.origin π hπ n hn

lemma splitTangent_parameter_root {c : ResidueField R}
    (hc : WeierstrassCurve.CriticalNeighborhood.SplitTangent (W := W) (x := x) (y := y) c) :
    c ^ 2 + (W.map (IsLocalRing.residue R)).a₁ * c -
      ((W.map (IsLocalRing.residue R)).a₂ + 3 * x) = 0 := by
  simpa only [WeierstrassCurve.CriticalNeighborhood.SplitTangent,
    WeierstrassCurve.translate_a1, WeierstrassCurve.translate_a2] using hc

/-- Under the supplied distinct split-tangent roots, identifies the strict
projective-line/exceptional-fibre intersection with the split two-point scheme. -/
def strictExceptionalTwoPointIso : pullback f e ≅ Spec (.of (k × k)) :=
  strictExceptionalOriginalIso M π hπ n hn a ha he ρ hρ hex hp hatlas hbc hx hy H ≪≫
    originalNormalizationNodeIso he hx hy H ρ σ (splitTangent_parameter_root hρ)
      (splitTangent_parameter_root hσ) hne

@[reassoc] lemma strictExceptionalTwoPointIso_residue :
    (strictExceptionalTwoPointIso M π hπ n hn a ha he ρ hρ hex hp hatlas hbc hx hy H σ hσ hne).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (k × k))) =
        pullback.snd f e ≫ pullback.snd (E).map p := by
  simp only [strictExceptionalTwoPointIso, Iso.trans_hom, Category.assoc,
    originalNormalizationNodeIso_structure, strictExceptionalOriginalIso_hom_snd]

/-- Both native choices of the intersection's k-structure agree literally. -/
lemma strictExceptional_structure_eq :
    pullback.fst f e ≫ AlgebraicGeometry.Scheme.ProjectiveLine.structureMap k =
      pullback.snd f e ≫ pullback.snd (E).map p := by
  rw [← strictP1ToFinal_over M π hπ n hn a ha he ρ hρ hex hp hatlas hbc hx hy H,
    ← Category.assoc, pullback.condition, Category.assoc, originalExceptionalToSpecial_snd]

@[reassoc] lemma strictExceptionalTwoPointIso_structure :
    (strictExceptionalTwoPointIso M π hπ n hn a ha he ρ hρ hex hp hatlas hbc hx hy H σ hσ hne).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (k × k))) =
        pullback.fst f e ≫ AlgebraicGeometry.Scheme.ProjectiveLine.structureMap k := by
  rw [strictExceptionalTwoPointIso_residue, strictExceptional_structure_eq]

/-- The genuine two-point isomorphism is over the original residue field. -/
def strictExceptionalTwoPointOverIso :
    Over.mk (pullback.fst f e ≫ AlgebraicGeometry.Scheme.ProjectiveLine.structureMap k) ≅
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (k × k)))) :=
  Over.isoMk (strictExceptionalTwoPointIso M π hπ n hn a ha he ρ hρ hex hp hatlas hbc hx hy H σ hσ
    hne)
    (strictExceptionalTwoPointIso_structure M π hπ n hn a ha he ρ hρ hex hp hatlas hbc hx hy H σ
      hσ hne)

@[reassoc] lemma strictExceptionalTwoPointIso_toP1 :
    (strictExceptionalTwoPointIso M π hπ n hn a ha he ρ hρ hex hp hatlas hbc hx hy H σ hσ hne).hom ≫
      Spec.map (CommRingCat.ofHom (Polynomial.pairedEvaluation k ρ σ)) ≫
        AlgebraicGeometry.Scheme.ProjectiveLine.chart k 0 = pullback.fst f e := by
  simp only [strictExceptionalTwoPointIso, Iso.trans_hom, Category.assoc,
    originalNormalizationNodeIso_toP1, strictExceptionalOriginalIso_hom_fst]

include hσ hne in
/-- Reducedness is transported from the computed two-point target. -/
lemma strictExceptional_isReduced : IsReduced (pullback f e) := by
  exact isReduced_of_isOpenImmersion
    (strictExceptionalTwoPointIso M π hπ n hn a ha he ρ hρ hex hp hatlas hbc hx hy H σ hσ hne).hom

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale

end -- noncomputable section
end StrictExceptionalTwoPoint


section WeierstrassExceptionalComplementSupport

/-! The native union of all components other than the actual strict component
has exactly the full original exceptional support. This is derived from the
proved actual component equivalence and actual exceptional P1 coverage. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open WeierstrassCurve.CriticalNeighborhood WeierstrassCurve.Projective
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {W : WeierstrassCurve R} {x y : ResidueField R}
variable (M : WeierstrassCurve.CriticalNeighborhood W x y) (π : R) (hπ : Irreducible π) (q : ℕ)
  (a : M.Carrierˣ)
  (ha : M.translated.a₆ = (a : M.Carrier) * algebraMap R M.Carrier (π ^ (q + 1)))
  (he : (W.map (IsLocalRing.residue R)).toAffine.Equation x y)
  (ρ : ResidueField R) (hρ : WeierstrassCurve.CriticalNeighborhood.SplitTangent (W := W) (x := x)
    (y := y) ρ)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u}) (hq : 0 < q)
local notation "F" => finalSpecialFibre M π hπ (q + 1) (Nat.succ_pos q) a ha he ρ hρ hex hp hatlas
  hbc
local notation "J" => originalExceptionalToSpecial M π hπ (q + 1) (Nat.succ_pos q) a ha he ρ hρ
  hex hp hatlas hbc
local notation "P" => originalExceptionalP1 M π hπ q a ha he ρ hρ hex hp hatlas hbc
local notation "e" => resolvedComponentEquiv M π hπ q a ha he ρ hρ hex hp hatlas hbc hq

include hq in
lemma originalExceptionalToSpecial_range_eq_iUnion :
    Set.range J = ⋃ j : Fin q, Set.range (P j) := by
  ext z
  constructor
  · rintro ⟨x,rfl⟩
    obtain ⟨j,p,hpoint⟩ := Resolution.exceptionalP1_cover π hπ hex hp hatlas q hq x
    refine Set.mem_iUnion.mpr ⟨j,p,?_⟩
    change (Resolution.exceptionalP1 π hπ hex hp hatlas q j ≫ J) p = J x
    exact congrArg J hpoint
  · intro hz
    obtain ⟨j,p,hpoint⟩ := Set.mem_iUnion.mp hz
    exact ⟨Resolution.exceptionalP1 π hπ hex hp hatlas q j p,hpoint⟩

/-- Exactly the support used by the native `otherScheme` at the strict index.
The equality does not presume that the exceptional pullback scheme is reduced. -/
lemma resolved_non_strict_components_support :
    (⋃ v : {v : irreducibleComponents F // v ≠ (e) none}, v.val.val) = Set.range J := by
  rw [originalExceptionalToSpecial_range_eq_iUnion M π hπ q a ha he ρ hρ hex hp hatlas hbc hq]
  ext z
  constructor
  · intro hz
    obtain ⟨v,hv⟩ := Set.mem_iUnion.mp hz
    obtain ⟨j,hj⟩ := (e).surjective v.val
    cases j with
    | none => exact False.elim (v.property hj.symm)
    | some j =>
      refine Set.mem_iUnion.mpr ⟨j,?_⟩
      have hr : ((e) (some j)).val = Set.range (P j) :=
        resolvedComponentEquiv_range M π hπ q a ha he ρ hρ hex hp hatlas hbc hq (some j)
      rw [← hr,hj]
      exact hv
  · intro hz
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hz
    have hne : (e) (some j) ≠ (e) none := by
      intro h
      cases (e).injective h
    refine Set.mem_iUnion.mpr ⟨⟨(e) (some j),hne⟩,?_⟩
    change z ∈ ((e) (some j)).val
    rw [resolvedComponentEquiv_range]
    exact hj

/-- At an exceptional index, the native complementary support is exactly the
strict component together with all the other actual exceptional P1 images. -/
lemma resolved_except_exceptional_components_support (i : Fin q) :
    (⋃ v : {v : irreducibleComponents F // v ≠ (e) (some i)}, v.val.val) =
      Set.range (strictTransformInclusion M π hπ (q + 1) (Nat.succ_pos q)
        a ha he ρ hρ hex hp hatlas hbc) ∪
        ⋃ j : {j : Fin q // j ≠ i}, Set.range (P j.val) := by
  ext z
  constructor
  · intro hz
    obtain ⟨v,hv⟩ := Set.mem_iUnion.mp hz
    obtain ⟨j,hj⟩ := (e).surjective v.val
    cases j with
    | none =>
      left
      have hr := resolvedComponentEquiv_range M π hπ q a ha he ρ hρ hex hp hatlas hbc hq none
      rw [← hj,hr] at hv
      exact hv
    | some j =>
      right
      have hne : j ≠ i := by
        intro h
        subst j
        exact v.property hj.symm
      refine Set.mem_iUnion.mpr ⟨⟨j,hne⟩,?_⟩
      have hr := resolvedComponentEquiv_range M π hπ q a ha he ρ hρ hex hp hatlas hbc hq (some j)
      rw [← hj,hr] at hv
      exact hv
  · intro hz
    rcases hz with hz | hz
    · have hne : (e) none ≠ (e) (some i) := by
        intro h
        cases (e).injective h
      refine Set.mem_iUnion.mpr ⟨⟨(e) none,hne⟩,?_⟩
      change z ∈ ((e) none).val
      rw [resolvedComponentEquiv_range]
      exact hz
    · obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hz
      have hne : (e) (some j.val) ≠ (e) (some i) := by
        intro h
        exact j.property (Option.some.inj ((e).injective h))
      refine Set.mem_iUnion.mpr ⟨⟨(e) (some j.val),hne⟩,?_⟩
      change z ∈ ((e) (some j.val)).val
      rw [resolvedComponentEquiv_range]
      exact hj

include hq in
/-- The thickness-two exceptional P1 covers the entire literal exceptional
support. This uses the proved actual inventory, not a new count premise. -/
lemma originalExceptionalP1_single_range (hq1 : q = 1) (i : Fin q) :
    Set.range (P i) = Set.range J := by
  rw [originalExceptionalToSpecial_range_eq_iUnion M π hπ q a ha he ρ hρ hex hp hatlas hbc hq]
  apply Set.Subset.antisymm
  · exact Set.subset_iUnion (fun j : Fin q => Set.range (P j)) i
  · intro z hz
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hz
    have hji : j = i := Fin.ext (by omega)
    simpa only [hji] using hj

/-- For thickness two, the native complement of the sole exceptional P1 has
exactly the actual strict support. Intersection scheme geometry is separate. -/
lemma resolved_except_single_exceptional_support (hq1 : q = 1) (i : Fin q) :
    (⋃ v : {v : irreducibleComponents F // v ≠ (e) (some i)}, v.val.val) =
      Set.range (strictTransformInclusion M π hπ (q + 1) (Nat.succ_pos q)
        a ha he ρ hρ hex hp hatlas hbc) := by
  rw [resolved_except_exceptional_components_support M π hπ q a ha he ρ hρ hex hp hatlas hbc hq i]
  have hnil : (⋃ j : {j : Fin q // j ≠ i}, Set.range (P j.val)) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hz
    exact j.property (Fin.ext (by omega))
  rw [hnil,Set.union_empty]

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale

end -- noncomputable section
end WeierstrassExceptionalComplementSupport
