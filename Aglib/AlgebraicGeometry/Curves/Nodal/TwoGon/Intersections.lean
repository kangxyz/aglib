/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Galois.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Tactic.LinearCombination
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.Topology.Sober
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.RingTheory.TensorProduct.Pi
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.Etale.Pi
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.RingTheory.Localization.Pi
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
public import Mathlib.RingTheory.Adjoin.Tower
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.RingTheory.Polynomial.Ideal
public import Mathlib.RingTheory.Polynomial.IsIntegral
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.Topology.DenseEmbedding
public import Aglib.AlgebraicGeometry.Curves.Nodal.TwoGon.Components
public import Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.AffineDegree

/-!
# The literal two-component pinched curve: Intersections

Source: frozen R5 `Curves/Cyclic/TwoGon/Intersections.lean`, revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`.
The actual ring maps, gluing arrows and component indices are retained.
This leaf does not construct a marked model or assume a model-existence theorem.
-/

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Polynomial
open scoped Polynomial
universe u

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Polynomial
open scoped Polynomial
namespace AlgebraicGeometry.Scheme.TwoGon.Affine

variable (k : Type u) [Field k]

/-- Actual scheme-theoretic affine intersection ideal of the two components. -/
def componentIntersectionIdeal : Ideal (nodeRing k) :=
  RingHom.ker (Scheme.TwoGon.leftProjection k) ⊔ RingHom.ker (Scheme.TwoGon.rightProjection k)

/-- Simultaneous evaluation at the two actual gluing points. -/
def endpointEvaluation : nodeRing k →ₐ[k] k × k :=
  ((leftEvaluation k 0).comp (nodeRing k).val).prod
    ((leftEvaluation k 1).comp (nodeRing k).val)

@[simp] theorem endpointEvaluation_apply (p : nodeRing k) :
    endpointEvaluation k p = ((p : NormalizationRing k).1.eval 0,
      (p : NormalizationRing k).1.eval 1) := rfl

theorem endpointEvaluation_surjective : Function.Surjective (endpointEvaluation k) := by
  rintro ⟨a, b⟩
  refine ⟨diagonal k (C a + C (b - a) * X), ?_⟩
  ext <;> simp [endpointEvaluation_apply, diagonal]

theorem componentIntersectionIdeal_eq_ker : componentIntersectionIdeal k =
    RingHom.ker (endpointEvaluation k).toRingHom := by
  apply le_antisymm
  · apply sup_le
    · intro p hp
      change (p : NormalizationRing k).1 = 0 at hp
      change endpointEvaluation k p = 0
      simp [endpointEvaluation_apply, hp]
    · intro p hp
      change (p : NormalizationRing k).2 = 0 at hp
      have h := (mem_nodeRing k p).mp p.property
      change endpointEvaluation k p = 0
      ext <;> simp only [endpointEvaluation_apply, Prod.fst_zero, Prod.snd_zero]
      · rw [h.1, hp]; simp
      · rw [h.2, hp]; simp
  · intro p hp
    change endpointEvaluation k p = 0 at hp
    have h0 : (p : NormalizationRing k).1.eval 0 = 0 := congrArg Prod.fst hp
    have h1 : (p : NormalizationRing k).1.eval 1 = 0 := congrArg Prod.snd hp
    have hp0 := (mem_nodeRing k p).mp p.property
    let l : nodeRing k := ⟨((p : NormalizationRing k).1, 0), by
      simp only [mem_nodeRing, eval_zero, h0, h1, and_self]⟩
    let r : nodeRing k := ⟨(0, (p : NormalizationRing k).2), by
      simp only [mem_nodeRing, eval_zero, ← hp0.1, ← hp0.2, h0, h1, and_self]⟩
    have hl : l ∈ RingHom.ker (Scheme.TwoGon.rightProjection k) := by rfl
    have hr : r ∈ RingHom.ker (Scheme.TwoGon.leftProjection k) := by rfl
    have he : r + l = p := by
      apply Subtype.ext
      ext <;> simp [l, r]
    rw [← he]
    exact Ideal.add_mem _ (Ideal.mem_sup_left hr) (Ideal.mem_sup_right hl)

/-- The intersection is a disjoint pair of reduced rational points as a ring,
not merely a set of two topological points. -/
def componentIntersectionEquiv :
    (nodeRing k ⧸ componentIntersectionIdeal k) ≃ₐ[k] (k × k) := by
  rw [componentIntersectionIdeal_eq_ker]
  exact Ideal.quotientKerAlgEquivOfSurjective (endpointEvaluation_surjective k)

theorem componentIntersection_finrank :
    Module.finrank k (nodeRing k ⧸ componentIntersectionIdeal k) = 2 := by
  rw [(componentIntersectionEquiv k).toLinearEquiv.finrank_eq]
  simp

/-- The quotient by the sum of the two component ideals is reduced. -/
instance componentIntersection_reduced : _root_.IsReduced (nodeRing k ⧸
  componentIntersectionIdeal k) :=
  isReduced_of_injective (componentIntersectionEquiv k) (componentIntersectionEquiv k).injective

/-- The spectrum of the component-intersection quotient identified with two rational points. -/
def componentIntersectionSchemeIso :
    Spec (.of (nodeRing k ⧸ componentIntersectionIdeal k)) ≅ Spec (.of (k × k)) :=
  Scheme.Spec.mapIso (componentIntersectionEquiv k).toRingEquiv.toCommRingCatIso.symm.op

/-- The same endpoint map on each of the two polynomial components. -/
def lineEndpoints : k[X] →+* k × k := (evalRingHom 0).prod (evalRingHom 1)

theorem lineEndpoints_surjective : Function.Surjective (lineEndpoints k) := by
  rintro ⟨a, b⟩
  refine ⟨C a + C (b-a) * X, ?_⟩
  ext <;> simp [lineEndpoints]

theorem lineEndpoints_left (p : nodeRing k) :
    lineEndpoints k (Scheme.TwoGon.leftProjection k p) = endpointEvaluation k p := rfl

theorem lineEndpoints_right (p : nodeRing k) :
    lineEndpoints k (Scheme.TwoGon.rightProjection k p) = endpointEvaluation k p := by
  have h := (mem_nodeRing k p).mp p.property
  exact Prod.ext h.1.symm h.2.symm

/-- The endpoint algebra satisfies the full pushout universal property for
these actual component projections. -/
theorem componentIntersection_isPushout :
    IsPushout (CommRingCat.ofHom (Scheme.TwoGon.leftProjection k))
      (CommRingCat.ofHom (Scheme.TwoGon.rightProjection k))
      (CommRingCat.ofHom (lineEndpoints k)) (CommRingCat.ofHom (lineEndpoints k)) := by
  apply IsPushout.mk'
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro p
    exact (lineEndpoints_left k p).trans (lineEndpoints_right k p).symm
  · intro T φ φ' h _
    ext x
    obtain ⟨p, rfl⟩ := lineEndpoints_surjective k x
    exact congrArg (fun f : CommRingCat.of k[X] ⟶ T => f p) h
  · intro T a b h
    let q := (endpointEvaluation k).toRingHom
    let f := a.hom.comp (Scheme.TwoGon.leftProjection k)
    have hk : RingHom.ker q ≤ RingHom.ker f := by
      rw [← componentIntersectionIdeal_eq_ker]
      apply sup_le
      · intro p hp
        change Scheme.TwoGon.leftProjection k p = 0 at hp
        change a (Scheme.TwoGon.leftProjection k p) = 0
        rw [hp, map_zero]
      · intro p hp
        change Scheme.TwoGon.rightProjection k p = 0 at hp
        change a (Scheme.TwoGon.leftProjection k p) = 0
        have he := congrArg (fun f : CommRingCat.of (nodeRing k) ⟶ T => f p) h
        change a (Scheme.TwoGon.leftProjection k p) = b (Scheme.TwoGon.rightProjection k p) at he
        rw [he, hp, map_zero]
    let d : k × k →+* T := q.liftOfSurjective (endpointEvaluation_surjective k) ⟨f, hk⟩
    have hd (p : nodeRing k) : d (q p) = a (Scheme.TwoGon.leftProjection k p) :=
      RingHom.liftOfSurjective_comp_apply q (endpointEvaluation_surjective k) ⟨f, hk⟩ p
    refine ⟨CommRingCat.ofHom d, ?_, ?_⟩
    · apply CommRingCat.hom_ext
      apply RingHom.ext
      intro p
      exact hd (diagonal k p)
    · apply CommRingCat.hom_ext
      apply RingHom.ext
      intro p
      have he := congrArg (fun f : CommRingCat.of (nodeRing k) ⟶ T => f (diagonal k p)) h
      change a p = b p at he
      change d (lineEndpoints k p) = b p
      rw [← he]
      exact hd (diagonal k p)

/-- Hence the actual affine component intersection is the spectrum of k×k,
with its genuine categorical pullback square. -/
theorem componentIntersection_isPullback :
    IsPullback (Spec.map (CommRingCat.ofHom (lineEndpoints k)))
      (Spec.map (CommRingCat.ofHom (lineEndpoints k)))
      (Scheme.TwoGon.leftAffine k) (Scheme.TwoGon.rightAffine k) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (componentIntersection_isPushout k)

/-- The affine component pullback identified with the spectrum of `k × k`. -/
def componentIntersectionPullbackIso :
    pullback (Scheme.TwoGon.leftAffine k) (Scheme.TwoGon.rightAffine k) ≅ Spec (.of (k × k)) :=
  (componentIntersection_isPullback k).isoPullback.symm

end AlgebraicGeometry.Scheme.TwoGon.Affine
end -- noncomputable section
end
section
noncomputable section
open CategoryTheory AlgebraicGeometry

end -- noncomputable section
end
section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.TwoGon
open Affine

variable (k : Type u) [Field k]

/-- The polynomial affine chart inclusion of a component projective line. -/
abbrev lineAffineChart : Spec (.of (Polynomial k)) ⟶ Scheme.PinchedLine.lineGluing k :=
  pushout.inl (Scheme.PinchedLine.normalizationOverlapInclusion k)
    (Scheme.PinchedLine.gluingToInfinity k)

/-- The pinched affine chart inclusion of the two-gon. -/
abbrev targetAffineChart : nodeScheme k ⟶ twoGon k :=
  pushout.inl (gluingToNode k) (gluingToInfinity k)

/-- The actual global intersection of the two closed projective-line immersions. -/
abbrev globalIntersection : Scheme.{u} := pullback (leftTargetMap k) (rightTargetMap k)

/-- The projection of the global component intersection to the left projective line. -/
abbrev globalIntersectionFirst : globalIntersection k ⟶ Scheme.PinchedLine.lineGluing k :=
  pullback.fst (leftTargetMap k) (rightTargetMap k)

/-- The projection of the global component intersection to the right projective line. -/
abbrev globalIntersectionSecond : globalIntersection k ⟶ Scheme.PinchedLine.lineGluing k :=
  pullback.snd (leftTargetMap k) (rightTargetMap k)

theorem globalIntersection_point_eq (z : globalIntersection k) :
    normalization k (leftComponent k (globalIntersectionFirst k z)) =
      normalization k (rightComponent k (globalIntersectionSecond k z)) :=
  congrArg (fun f : globalIntersection k ⟶ twoGon k => f z)
    (pullback.condition (f := leftTargetMap k) (g := rightTargetMap k))

/-- There is no intersection point on the infinity chart. This statement is
about the actual global fibre product, without a point-count hypothesis. -/
theorem globalIntersection_not_infinity (z : globalIntersection k) (v : infinityScheme k) :
    (globalIntersectionFirst k ≫ leftTargetMap k) z ≠
      pushout.inr (gluingToNode k) (gluingToInfinity k) v :=
  commonImage_not_infinity k _ _ (globalIntersection_point_eq k z) v

/-- The actual restriction of the intersection to the infinity chart is empty. -/
instance globalIntersection_infinity_empty :
    IsEmpty (pullback (globalIntersectionFirst k ≫ leftTargetMap k)
      (pushout.inr (gluingToNode k) (gluingToInfinity k)) : Scheme.{u}) := by
  apply Scheme.isEmpty_pullback
  rw [Set.disjoint_left]
  rintro z ⟨x, rfl⟩ ⟨v, hv⟩
  exact globalIntersection_not_infinity k x v hv.symm

theorem globalIntersectionFirst_range :
    Set.range (globalIntersectionFirst k) ⊆ Set.range (lineAffineChart k) := by
  rintro _ ⟨z, rfl⟩
  exact (commonImage_affine k _ _ (globalIntersection_point_eq k z)).1

theorem globalIntersectionSecond_range :
    Set.range (globalIntersectionSecond k) ⊆ Set.range (lineAffineChart k) := by
  rintro _ ⟨z, rfl⟩
  exact (commonImage_affine k _ _ (globalIntersection_point_eq k z)).2

/-- The universal open-immersion property factors the two global projections
through the actual polynomial charts as scheme morphisms. -/
def intersectionAffineFirst : globalIntersection k ⟶ Spec (.of (Polynomial k)) :=
  IsOpenImmersion.lift (lineAffineChart k) (globalIntersectionFirst k)
    (globalIntersectionFirst_range k)

/-- The right projection of the global intersection lifted to the polynomial affine chart. -/
def intersectionAffineSecond : globalIntersection k ⟶ Spec (.of (Polynomial k)) :=
  IsOpenImmersion.lift (lineAffineChart k) (globalIntersectionSecond k)
    (globalIntersectionSecond_range k)

@[reassoc (attr := simp)] theorem intersectionAffineFirst_chart :
    intersectionAffineFirst k ≫ lineAffineChart k = globalIntersectionFirst k :=
  IsOpenImmersion.lift_fac _ _ _

@[reassoc (attr := simp)] theorem intersectionAffineSecond_chart :
    intersectionAffineSecond k ≫ lineAffineChart k = globalIntersectionSecond k :=
  IsOpenImmersion.lift_fac _ _ _

theorem intersectionAffine_condition :
    intersectionAffineFirst k ≫ leftAffine k = intersectionAffineSecond k ≫ rightAffine k := by
  apply (cancel_mono (targetAffineChart k)).mp
  calc
    (intersectionAffineFirst k ≫ leftAffine k) ≫ targetAffineChart k =
        globalIntersectionFirst k ≫ leftTargetMap k := by
      rw [Category.assoc, ← leftTargetMap_affine, ← Category.assoc, intersectionAffineFirst_chart]
    _ = globalIntersectionSecond k ≫ rightTargetMap k := pullback.condition
    _ = (intersectionAffineSecond k ≫ rightAffine k) ≫ targetAffineChart k := by
      rw [Category.assoc, ← rightTargetMap_affine, ← Category.assoc, intersectionAffineSecond_chart]

/-- The global component intersection mapped to the pullback of the affine component maps. -/
def globalIntersectionToAffine : globalIntersection k ⟶ pullback (leftAffine k) (rightAffine k) :=
  pullback.lift (intersectionAffineFirst k) (intersectionAffineSecond k)
    (intersectionAffine_condition k)

/-- The affine component pullback mapped to the global component intersection. -/
def affineIntersectionToGlobal : pullback (leftAffine k) (rightAffine k) ⟶ globalIntersection k :=
  pullback.lift (pullback.fst _ _ ≫ lineAffineChart k)
    (pullback.snd _ _ ≫ lineAffineChart k) (by
      rw [Category.assoc, leftTargetMap_affine, Category.assoc, rightTargetMap_affine,
        ← Category.assoc, ← Category.assoc, pullback.condition])

/-- The affine comparison is an actual isomorphism; nilpotents and local-ring
structure are retained, rather than inferred from a topological bijection. -/
def globalIntersectionAffineIso :
    globalIntersection k ≅ pullback (leftAffine k) (rightAffine k) where
  hom := globalIntersectionToAffine k
  inv := affineIntersectionToGlobal k
  hom_inv_id := by
    apply pullback.hom_ext
    · simp [globalIntersectionToAffine, affineIntersectionToGlobal, Category.assoc]
    · simp [globalIntersectionToAffine, affineIntersectionToGlobal, Category.assoc]
  inv_hom_id := by
    apply pullback.hom_ext
    · apply (cancel_mono (lineAffineChart k)).mp
      simp [globalIntersectionToAffine, affineIntersectionToGlobal, Category.assoc]
    · apply (cancel_mono (lineAffineChart k)).mp
      simp [globalIntersectionToAffine, affineIntersectionToGlobal, Category.assoc]

/-- The global closed-component intersection is the actual two-point scheme. -/
def globalIntersectionIsoTwoPoints : globalIntersection k ≅ Spec (.of (k × k)) :=
  globalIntersectionAffineIso k ≪≫ componentIntersectionPullbackIso k

@[reassoc] theorem globalIntersectionAffineIso_hom_fst :
    (globalIntersectionAffineIso k).hom ≫ pullback.fst _ _ = intersectionAffineFirst k :=
  pullback.lift_fst _ _ _

@[reassoc] theorem globalIntersectionIsoTwoPoints_endpoints :
    (globalIntersectionIsoTwoPoints k).hom ≫ Spec.map (CommRingCat.ofHom (lineEndpoints k)) =
      intersectionAffineFirst k := by
  rw [globalIntersectionIsoTwoPoints, Iso.trans_hom, Category.assoc,
    componentIntersectionPullbackIso, Iso.symm_hom, IsPullback.isoPullback_inv_fst,
    globalIntersectionAffineIso_hom_fst]

/-- Compatibility with the structural field map is proved, so the intersection
identification is genuinely over k. -/
theorem globalIntersectionIsoTwoPoints_over :
    (globalIntersectionIsoTwoPoints k).hom ≫ AlgebraicGeometry.Spec.algebraMap k (k × k) =
      globalIntersectionFirst k ≫ Scheme.PinchedLine.lineStructure k := by
  have he : Spec.map (CommRingCat.ofHom (lineEndpoints k)) ≫
      AlgebraicGeometry.Spec.algebraMap k (Polynomial k) = AlgebraicGeometry.Spec.algebraMap k
        (k × k) := by
    unfold AlgebraicGeometry.Spec.algebraMap
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact Prod.ext (by simp [lineEndpoints]) (by simp [lineEndpoints])
  rw [← he, ← Category.assoc, globalIntersectionIsoTwoPoints_endpoints]
  have hl : lineAffineChart k ≫ Scheme.PinchedLine.lineStructure k =
      AlgebraicGeometry.Spec.algebraMap k (Polynomial k) := by
    exact pushout.inl_desc _ _ _
  rw [← hl, ← Category.assoc, intersectionAffineFirst_chart]

/-- The global component intersection identified with two rational points over `k`. -/
def globalIntersectionOverIsoTwoPoints :
    Over.mk (globalIntersectionFirst k ≫ Scheme.PinchedLine.lineStructure k) ≅
      Over.mk (AlgebraicGeometry.Spec.algebraMap k (k × k)) :=
  Over.isoMk (globalIntersectionIsoTwoPoints k) (globalIntersectionIsoTwoPoints_over k)

/-- The fibre product of the canonical reduced closed component image schemes. -/
abbrev closedComponentIntersection : Scheme.{u} :=
  pullback (leftTargetMap k).imageι (rightTargetMap k).imageι

/-- Transporting each closed immersion through its actual image factorization
induces an isomorphism of the two global component fibre products. -/
def globalToClosedComponentIntersection : globalIntersection k ⟶ closedComponentIntersection k :=
  pullback.map (leftTargetMap k) (rightTargetMap k)
    (leftTargetMap k).imageι (rightTargetMap k).imageι
    (leftTargetMap k).toImage (rightTargetMap k).toImage (𝟙 _) (by simp) (by simp)

/-- Replacing the parametrized components by their closed images preserves their intersection. -/
instance globalToClosedComponentIntersection_isIso : IsIso (globalToClosedComponentIntersection
  k) := by
  unfold globalToClosedComponentIntersection
  infer_instance

/-- The intersection of the closed component images identified with the spectrum of `k × k`. -/
def closedComponentIntersectionIsoTwoPoints :
    closedComponentIntersection k ≅ Spec (.of (k × k)) :=
  (asIso (globalToClosedComponentIntersection k)).symm ≪≫ globalIntersectionIsoTwoPoints k

/-- The field structure map of the intersection of the closed component images. -/
abbrev closedComponentIntersectionStructure : closedComponentIntersection k ⟶ Spec (.of k) :=
  pullback.fst _ _ ≫ (leftTargetMap k).imageι ≫ structureMap k

@[reassoc] theorem globalToClosedComponentIntersection_over :
    globalToClosedComponentIntersection k ≫ closedComponentIntersectionStructure k =
      globalIntersectionFirst k ≫ Scheme.PinchedLine.lineStructure k := by
  simp only [globalToClosedComponentIntersection, closedComponentIntersectionStructure,
    pullback.map, Category.assoc, pullback.lift_fst_assoc, Scheme.Hom.toImage_imageι_assoc,
    leftTargetMap_over]

theorem closedComponentIntersectionIsoTwoPoints_over :
    (closedComponentIntersectionIsoTwoPoints k).hom ≫ AlgebraicGeometry.Spec.algebraMap k (k × k) =
      closedComponentIntersectionStructure k := by
  rw [closedComponentIntersectionIsoTwoPoints, Iso.trans_hom, Category.assoc,
    globalIntersectionIsoTwoPoints_over, ← globalToClosedComponentIntersection_over]
  simp

/-- The closed-component intersection identified with two rational points over `k`. -/
def closedComponentIntersectionOverIsoTwoPoints :
    Over.mk (closedComponentIntersectionStructure k) ≅
      Over.mk (AlgebraicGeometry.Spec.algebraMap k (k × k)) :=
  Over.isoMk (closedComponentIntersectionIsoTwoPoints k)
    (closedComponentIntersectionIsoTwoPoints_over k)

/-- The scheme-theoretic intersection of the closed component images is reduced. -/
instance closedComponentIntersection_reduced : IsReduced (closedComponentIntersection k) :=
  isReduced_of_isOpenImmersion (closedComponentIntersectionIsoTwoPoints k).hom

/-- The scheme-theoretic intersection of the closed component images is finite over `k`. -/
instance closedComponentIntersection_finite : IsFinite (closedComponentIntersectionStructure k)
  := by
  rw [← closedComponentIntersectionIsoTwoPoints_over]
  have : IsFinite (AlgebraicGeometry.Spec.algebraMap k (k × k)) := by
    unfold AlgebraicGeometry.Spec.algebraMap
    apply (IsFinite.SpecMap_iff _).mpr
    exact RingHom.finite_algebraMap.mpr inferInstance
  infer_instance

end AlgebraicGeometry.Scheme.TwoGon
end -- noncomputable section
end
