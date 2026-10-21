/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Nodal.Polygon.EtaleProjection

/-!
# Field-valued points of the actual polygon projection

Source: frozen R5 `Curves/Cyclic/Covers/FiniteCover.lean`, lines 488–590,
revision `f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`b96dbafa96b00d65651d1f9b2e777bc889c72e9e02c218b154c2a17813a33f37`.
The private node-evaluation argument is from `DoubleCoverPoints.lean`, lines
38–66, SHA-256 `400f6ec15d26fd74b56c2c4b5fd52bc0b523a9095d2a27867d5f1c02bda18487`.
The lifts are morphisms from the original field, through the same projection.
No algebraic closure, finite field extension or invertibility of the level is used.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits AlgebraicGeometry Polynomial
open scoped Polynomial

universe u v

namespace Polynomial.PinchedPair

variable (k : Type u) [Field k] (K : Type v) [Field K] [Algebra k K]

private def fieldNodeEvaluation : nodeRing k →ₐ[k] K :=
  (aeval (0 : K)).comp (nodeRing k).val

@[simp] private theorem fieldNodeEvaluation_conductor :
    fieldNodeEvaluation k K (conductor k) = 0 := by
  simp [fieldNodeEvaluation, conductor]

@[simp] private theorem fieldNodeEvaluation_second :
    fieldNodeEvaluation k K (secondCoordinate k) = 0 := by
  simp [fieldNodeEvaluation, secondCoordinate, conductorMul]

private theorem fieldEval_second_eq_zero (f : nodeRing k →ₐ[k] K)
    (h : f (conductor k) = 0) : f (secondCoordinate k) = 0 := by
  have hc := congrArg f (coordinate_relation k)
  simp only [map_sub, map_pow, map_mul, map_zero, h, zero_mul, sub_zero,
    zero_pow (by decide : 3 ≠ 0)] at hc
  exact (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp hc

private theorem fieldEval_eq_nodeEvaluation (f : nodeRing k →ₐ[k] K)
    (h : f (conductor k) = 0) : f = fieldNodeEvaluation k K := by
  have hv := fieldEval_second_eq_zero k K f h
  have heq : f.comp (coordinateHom k) = (fieldNodeEvaluation k K).comp (coordinateHom k) := by
    ext
    · simp [coordinateHom, h]
    · simp [coordinateHom, hv]
  ext p
  obtain ⟨a, rfl⟩ := coordinateHom_surjective k p
  exact DFunLike.congr_fun heq a

end Polynomial.PinchedPair

namespace AlgebraicGeometry.Scheme.Polygon

variable (k : Type u) [Field k] (n : ℕ) [NeZero n]

/-- Every field-valued pinched node map lifts to the actual polynomial normalization. -/
theorem polynomialRingMap_lift (K : Type u) [Field K]
    (f : Polynomial.PinchedPair.nodeRing k →+* K) :
    ∃ g : k[X] →+* K, g.comp (Polynomial.PinchedPair.nodeRing k).val.toRingHom = f := by
  by_cases h : f (Polynomial.PinchedPair.conductor k) = 0
  · let : Algebra k K := (f.comp (algebraMap k (Polynomial.PinchedPair.nodeRing k))).toAlgebra
    let f' : Polynomial.PinchedPair.nodeRing k →ₐ[k] K := { f with commutes' := fun _ => rfl }
    have he := Polynomial.PinchedPair.fieldEval_eq_nodeEvaluation k K f' h
    refine ⟨(aeval (0 : K)).toRingHom, ?_⟩
    exact congrArg AlgHom.toRingHom he.symm
  · let f' : Polynomial.PinchedPair.nodeOverlapRing k →+* K :=
      IsLocalization.Away.lift (Polynomial.PinchedPair.conductor k) (isUnit_iff_ne_zero.mpr h)
    let g : k[X] →+* K :=
      (f'.comp (Polynomial.PinchedPair.conductorLocalizationEquiv k).symm.toRingHom).comp
        (algebraMap k[X] (Polynomial.PinchedPair.normalizationOverlapRing k))
    refine ⟨g, ?_⟩
    apply RingHom.ext
    intro a
    change f' ((Polynomial.PinchedPair.conductorLocalizationEquiv k).symm
      (algebraMap k[X] (Polynomial.PinchedPair.normalizationOverlapRing k) (a : k[X]))) = f a
    have he : (Polynomial.PinchedPair.conductorLocalizationEquiv k).symm
        (algebraMap k[X] (Polynomial.PinchedPair.normalizationOverlapRing k) (a : k[X])) =
        algebraMap (Polynomial.PinchedPair.nodeRing k)
          (Polynomial.PinchedPair.nodeOverlapRing k) a := by
      apply (Polynomial.PinchedPair.conductorLocalizationEquiv k).injective
      rw [RingEquiv.apply_symm_apply]
      exact (Polynomial.PinchedPair.localizationComparison_algebraMap k a).symm
    rw [he]
    exact IsLocalization.Away.lift_eq _ _ a

/-- The first actual normalized component supplies a lift to the n-cycle. -/
theorem affineRingMap_lift (K : Type u) [Field K]
    (f : Polynomial.PinchedPair.nodeRing k →+* K) :
    ∃ g : nodeRing k n →+* K, g.comp (baseMap k n).toRingHom = f := by
  obtain ⟨g, hg⟩ := polynomialRingMap_lift k K f
  refine ⟨(g.comp (Pi.evalRingHom _ (0 : Fin n))).comp (nodeRing k n).val.toRingHom, ?_⟩
  exact hg

/-- Literal lifting of scheme morphisms from every field, not just points. -/
theorem affineMap_fieldPoint_lift (K : Type u) [Field K]
    (p : Spec (.of K) ⟶ Scheme.PinchedLine.nodeScheme k) :
    ∃ s : Spec (.of K) ⟶ nodeScheme k n, s ≫ affineMap k n = p := by
  obtain ⟨f, rfl⟩ := Spec.map_surjective p
  obtain ⟨g, hg⟩ := affineRingMap_lift k n K f.hom
  refine ⟨Spec.map (CommRingCat.ofHom g), ?_⟩
  rw [affineMap, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext hg

/-- The first-sheet section of the actual infinity projection. -/
def infinitySection : Spec (.of (V k)) ⟶ infinityScheme k n :=
  Spec.map (CommRingCat.ofHom (Pi.evalRingHom _ (0 : Fin n)))

@[simp] theorem infinitySection_map : infinitySection k n ≫ infinityMap k n = 𝟙 _ := by
  rw [infinitySection, infinityMap, ← Spec.map_comp, ← Spec.map_id]
  rfl

/-- The two exhaustive opens give actual lifts over arbitrary fields. -/
theorem cycleMap_fieldPoint_lift (K : Type u) [Field K]
    (p : Spec (.of K) ⟶ Scheme.PinchedLine.pinchedGluing k) :
    ∃ s : Spec (.of K) ⟶ cycleScheme k n, s ≫ cycleMap k n = p := by
  rcases Scheme.PinchedLine.pinchedGluing_covered k (p (IsLocalRing.closedPoint K)) with
    ⟨a, ha⟩ | ⟨a, ha⟩
  · have hr : Set.range p ⊆
        Set.range (pushout.inl (Scheme.PinchedLine.gluingToNode k)
          (Scheme.PinchedLine.gluingToInfinity k)) := by
      rintro _ ⟨x, rfl⟩
      have hx : x = IsLocalRing.closedPoint K := Subsingleton.elim _ _
      exact ⟨a, by rwa [hx]⟩
    let q := IsOpenImmersion.lift
      (pushout.inl (Scheme.PinchedLine.gluingToNode k) (Scheme.PinchedLine.gluingToInfinity k)) p hr
    obtain ⟨s, hs⟩ := affineMap_fieldPoint_lift k n K q
    refine ⟨s ≫ pushout.inl (gluingToNode k n)
      (gluingToInfinity k n), ?_⟩
    rw [Category.assoc, cycleMap_affine, ← Category.assoc, hs]
    exact IsOpenImmersion.lift_fac _ _ hr
  · have hr : Set.range p ⊆
        Set.range (pushout.inr (Scheme.PinchedLine.gluingToNode k)
          (Scheme.PinchedLine.gluingToInfinity k)) := by
      rintro _ ⟨x, rfl⟩
      have hx : x = IsLocalRing.closedPoint K := Subsingleton.elim _ _
      exact ⟨a, by rwa [hx]⟩
    let q := IsOpenImmersion.lift
      (pushout.inr (Scheme.PinchedLine.gluingToNode k) (Scheme.PinchedLine.gluingToInfinity k)) p hr
    refine ⟨q ≫ infinitySection k n ≫ pushout.inr (gluingToNode k n)
      (gluingToInfinity k n), ?_⟩
    rw [Category.assoc, Category.assoc, cycleMap_infinity,
      ← Category.assoc (infinitySection k n), infinitySection_map, Category.id_comp]
    exact IsOpenImmersion.lift_fac _ _ hr

/-- An actual lift, chosen from the proved field-point lifting theorem. -/
def fieldPointLift (K : Type u) [Field K]
    (p : Spec (.of K) ⟶ Scheme.PinchedLine.pinchedGluing k) :
    Spec (.of K) ⟶ cycleScheme k n :=
  (cycleMap_fieldPoint_lift k n K p).choose

@[reassoc] theorem fieldPointLift_map (K : Type u) [Field K]
    (p : Spec (.of K) ⟶ Scheme.PinchedLine.pinchedGluing k) :
    fieldPointLift k n K p ≫ cycleMap k n = p :=
  (cycleMap_fieldPoint_lift k n K p).choose_spec

@[reassoc] theorem fieldPointLift_over (K : Type u) [Field K]
    (p : Spec (.of K) ⟶ Scheme.PinchedLine.pinchedGluing k) :
    fieldPointLift k n K p ≫ structureMap k n =
      p ≫ Scheme.PinchedLine.pinchedStructure k := by
  rw [structureMap, ← Category.assoc, fieldPointLift_map]



end AlgebraicGeometry.Scheme.Polygon
