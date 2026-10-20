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
public import Aglib.AlgebraicGeometry.Curves.Nodal.Polygon.Normalization
public import Aglib.AlgebraicGeometry.Curves.Nodal.Polygon.Projection
public import Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.DegreeIso
public import Aglib.AlgebraicGeometry.Curves.Nodal.TwoGon.Intersections
public import Aglib.Data.Fin.Rotate
public import Aglib.AlgebraicGeometry.IdealSheaf.Closed.SpecKernel
public import Aglib.AlgebraicGeometry.IdealSheaf.Closed.RadicalSubscheme
public import Aglib.AlgebraicGeometry.IdealSheaf.Closed.OpenRestriction
public import Aglib.AlgebraicGeometry.IdealSheaf.Closed.ReducedClosedUnion
public import Aglib.AlgebraicGeometry.Properties.IrreducibleComponents.Transport

/-!
# The unmarked polygon curve: ComponentGeometry

Source: frozen R5 `Curves/Cyclic/ComponentGeometry.lean`, revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`.
The actual ring maps, gluing arrows and component indices are retained.
This leaf does not construct a marked model or assume a model-existence theorem.
-/

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Polynomial
open Scheme.Hom Scheme.IdealSheafData
open scoped Polynomial
universe u

section
noncomputable section
open Polynomial
namespace AlgebraicGeometry.Scheme.Polygon
variable (k : Type u) [Field k] (n : ℕ)

/-- The actual projection of the cyclic pinching algebra onto a normalization component. -/
def componentProjection (i : Fin n) : nodeRing k n →ₐ[k] k[X] :=
  (Pi.evalAlgHom k (fun _ : Fin n => k[X]) i).comp (nodeRing k n).val

/-- A component with distinct preceding and following nodes has its entire polynomial
coordinate ring as a quotient of the actual cyclic pinching algebra. -/
theorem componentProjection_surjective (i : Fin n) (hi : finRotate n i ≠ i) :
    Function.Surjective (componentProjection k n i) := by
  intro p
  let r := finRotate n
  let a : Fin n → k := fun j => if j = i then p.eval 1 else
    if r j = i then p.eval 0 else 0
  have hprev : r.symm i ≠ i := by
    intro h
    apply hi
    exact (congrArg r h.symm).trans (r.apply_symm_apply i)
  have ha0 : a (r.symm i) = p.eval 0 := by simp [a, hprev]
  have ha1 : a i = p.eval 1 := by simp [a]
  let q : NormalizationRing k n := fun j => if j = i then p else
    Polynomial.linearInterpolate k (a (r.symm j)) (a j)
  have hq0 (j : Fin n) : (q j).eval 0 = a (r.symm j) := by
    by_cases hj : j = i
    · subst j; simp [q, ha0]
    · simp [q, hj]
  have hq1 (j : Fin n) : (q j).eval 1 = a j := by
    by_cases hj : j = i
    · subst j; simp [q, ha1]
    · simp [q, hj]
  have hq : q ∈ nodeRing k n := by
    rw [mem_nodeRing]
    intro j
    rw [hq1, hq0]
    exact congrArg a (r.symm_apply_apply j).symm
  refine ⟨⟨q,hq⟩, ?_⟩
  change q i = p
  simp [q]

end AlgebraicGeometry.Scheme.Polygon
end -- noncomputable section
end
section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits AlgebraicGeometry Polynomial
namespace AlgebraicGeometry.Scheme.Polygon
variable (k : Type u) [Field k] (n : ℕ)

/-- Each projective-line component is closed in the normalization gluing. -/
instance componentLine_closedImmersion (i : Fin n) : IsClosedImmersion (componentLine k n i) where
  toSurjectiveOnStalks := inferInstance
  isClosedEmbedding := ⟨(componentLine k n i).isOpenEmbedding.isEmbedding,
    componentLine_range_closed k n i⟩

/-- The normalization component with label `i` mapped to the polygon curve. -/
def componentTarget (i : Fin n) : Scheme.PinchedLine.lineGluing k ⟶ cycleScheme k n :=
  componentLine k n i ≫ gluedPolynomialCover k n

/-- The affine component map induced by projection of the pinching algebra onto coordinate `i`. -/
def componentTargetAffine (i : Fin n) : Spec (.of k[X]) ⟶ nodeScheme k n :=
  Spec.map (CommRingCat.ofHom (componentProjection k n i).toRingHom)

theorem componentTargetAffine_closed (i : Fin n) (hi : finRotate n i ≠ i) :
    IsClosedImmersion (componentTargetAffine k n i) :=
  IsClosedImmersion.spec_of_surjective _ (componentProjection_surjective k n i hi)

/-- The component inclusion on the product infinity chart is a closed immersion. -/
instance componentInfinity_closed (i : Fin n) : IsClosedImmersion (componentInfinity k n i) :=
  IsClosedImmersion.spec_of_surjective _ (fun p => ⟨fun _ => p, rfl⟩)

@[reassoc] theorem componentTarget_affine (i : Fin n) :
    pushout.inl (Scheme.PinchedLine.normalizationOverlapInclusion k)
      (Scheme.PinchedLine.gluingToInfinity k) ≫
      componentTarget k n i = componentTargetAffine k n i ≫
        pushout.inl (gluingToNode k n) (gluingToInfinity k n) := by
  rw [componentTarget, ← Category.assoc, componentLine_affine, Category.assoc]
  rw [show pushout.inl (normalizationOverlapInclusion k n) (gluingToInfinity k n) ≫
      gluedPolynomialCover k n = polynomialCover k n ≫
        pushout.inl (gluingToNode k n) (gluingToInfinity k n) from
    Scheme.OpenNormalizationGluing.affine_chart _ _ _ _ _]
  rw [← Category.assoc]
  congr 1
  unfold polynomialCover componentTargetAffine componentProjection componentAffine
  rw [← Spec.map_comp]
  rfl

@[reassoc] theorem componentTarget_infinity (i : Fin n) :
    pushout.inr (Scheme.PinchedLine.normalizationOverlapInclusion k)
      (Scheme.PinchedLine.gluingToInfinity k) ≫
      componentTarget k n i = componentInfinity k n i ≫
        pushout.inr (gluingToNode k n) (gluingToInfinity k n) := by
  rw [componentTarget, ← Category.assoc, componentLine_infinity, Category.assoc]
  exact congrArg (componentInfinity k n i ≫ ·)
    (Scheme.OpenNormalizationGluing.infinity_chart _ _ _ _ _)

/-- Each parametrized projective-line component maps finitely to the polygon curve. -/
instance componentTarget_finite (i : Fin n) : IsFinite (componentTarget k n i) := by
  unfold componentTarget
  infer_instance

theorem componentTarget_surjectiveOnStalks (i : Fin n) (hi : finRotate n i ≠ i) :
    SurjectiveOnStalks (componentTarget k n i) := by
  let := componentTargetAffine_closed k n i hi
  apply IsZariskiLocalAtSource.of_openCover (P := @SurjectiveOnStalks)
    (Scheme.OpenNormalizationGluing.twoChartCover
      (Scheme.PinchedLine.normalizationOverlapInclusion k) (Scheme.PinchedLine.gluingToInfinity k))
  intro b
  cases b
  · change SurjectiveOnStalks
      (pushout.inl (Scheme.PinchedLine.normalizationOverlapInclusion k)
        (Scheme.PinchedLine.gluingToInfinity k) ≫ componentTarget k n i)
    rw [componentTarget_affine]
    infer_instance
  · change SurjectiveOnStalks
      (pushout.inr (Scheme.PinchedLine.normalizationOverlapInclusion k)
        (Scheme.PinchedLine.gluingToInfinity k) ≫ componentTarget k n i)
    rw [componentTarget_infinity]
    infer_instance

theorem componentTarget_injective
    (c : Scheme.PinchedLine.lineGluing k ⟶ normalizedScheme k n) [IsOpenImmersion c]
    (a : Spec (.of k[X]) ⟶ nodeScheme k n) [IsClosedImmersion a]
    (v : Spec (.of (V k)) ⟶ infinityScheme k n)
    (ha : pushout.inl (Scheme.PinchedLine.normalizationOverlapInclusion k)
      (Scheme.PinchedLine.gluingToInfinity k) ≫
      (c ≫ gluedPolynomialCover k n) = a ≫ pushout.inl (gluingToNode k n) (gluingToInfinity k n))
    (hv : pushout.inr (Scheme.PinchedLine.normalizationOverlapInclusion k)
      (Scheme.PinchedLine.gluingToInfinity k) ≫ c =
      v ≫ pushout.inr (normalizationOverlapInclusion k n) (gluingToInfinity k n)) :
    Function.Injective (c ≫ gluedPolynomialCover k n) := by
  have infinity_case (x : Scheme.PinchedLine.lineGluing k) (y : Spec (.of (V k)))
      (h : gluedPolynomialCover k n (c x) = gluedPolynomialCover k n (c
        (pushout.inr (Scheme.PinchedLine.normalizationOverlapInclusion k)
          (Scheme.PinchedLine.gluingToInfinity k) y))) :
      x = pushout.inr (Scheme.PinchedLine.normalizationOverlapInclusion k)
        (Scheme.PinchedLine.gluingToInfinity k) y := by
    have hy := congrArg (fun f : Spec (.of (V k)) ⟶ normalizedScheme k n => f y) hv
    simp only [Scheme.Hom.comp_apply] at hy
    apply c.isOpenEmbedding.injective
    rw [hy]
    apply (gluedPolynomialCover_infinity_fibre k n _ _).mp
    exact h.trans ((gluedPolynomialCover_infinity_fibre k n _ _).mpr hy)
  intro x y h
  change gluedPolynomialCover k n (c x) = gluedPolynomialCover k n (c y) at h
  rcases Scheme.PinchedLine.lineGluing_covered k x with ⟨p, rfl⟩ | ⟨p, rfl⟩
  · rcases Scheme.PinchedLine.lineGluing_covered k y with ⟨q, rfl⟩ | ⟨q, rfl⟩
    · have hp := congrArg (fun f : Spec (.of k[X]) ⟶ cycleScheme k n => f p) ha
      have hq := congrArg (fun f : Spec (.of k[X]) ⟶ cycleScheme k n => f q) ha
      simp only [Scheme.Hom.comp_apply] at hp hq
      have h' := (pushout.inl (gluingToNode k n) (gluingToInfinity k n)).isOpenEmbedding.injective
        (hp.symm.trans (h.trans hq))
      have hpq := a.isClosedEmbedding.injective h'
      exact congrArg _ hpq
    · exact infinity_case _ _ h
  · exact (infinity_case _ _ h.symm).symm

theorem componentTarget_closedImmersion (i : Fin n) (hi : finRotate n i ≠ i) :
    IsClosedImmersion (componentTarget k n i) := by
  let := componentTargetAffine_closed k n i hi
  exact { toSurjectiveOnStalks := componentTarget_surjectiveOnStalks k n i hi
          isClosedEmbedding := Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
            (componentTarget k n i).continuous
            (componentTarget_injective k n (componentLine k n i) (componentTargetAffine k n i)
              (componentInfinity k n i) (componentTarget_affine k n i) (componentLine_infinity
                k n i))
            (componentTarget k n i).isClosedMap }

/-- Actual projective component embedding; the nodal one-gon is correctly excluded. -/
theorem componentTarget_closedImmersion_of_one_lt (hn : 1 < n) (i : Fin n) :
    IsClosedImmersion (componentTarget k n i) :=
  componentTarget_closedImmersion k n i (Fin.finRotate_ne_self_of_one_lt n hn i)

theorem componentTarget_range (i : Fin n) :
    Set.range (componentTarget k n i) = targetComponent k n i := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨componentLine k n i x, ⟨x, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩

/-- The actual scheme-theoretic component image. -/
abbrev componentImage (i : Fin n) : Scheme.{u} := (componentTarget k n i).image

/-- Each component image for n>1 is the literal Proj projective line. -/
def componentImageIsoP1 (hn : 1 < n) (i : Fin n) :
    componentImage k n i ≅ Scheme.ProjectiveLine.projectiveP1 k := by
  let := componentTarget_closedImmersion_of_one_lt k n hn i
  exact (asIso (componentTarget k n i).toImage).symm ≪≫
    Scheme.PinchedLine.ProjectiveComparison.lineIsoP1 k

/-- Retain the actual base-field structural triangle in the component P1 identification. -/
def componentImageOverIsoP1 (hn : 1 < n) (i : Fin n)
    (s : cycleScheme k n ⟶ Spec (.of k))
    (hs : componentTarget k n i ≫ s = Scheme.PinchedLine.lineStructure k) :
    Over.mk ((componentTarget k n i).imageι ≫ s) ≅
      Over.mk (Scheme.ProjectiveLine.structureMap k) := by
  let := componentTarget_closedImmersion_of_one_lt k n hn i
  refine Over.isoMk (componentImageIsoP1 k n hn i) ?_
  apply (cancel_epi (componentTarget k n i).toImage).mp
  simp only [Over.mk_hom, componentImageIsoP1, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Scheme.PinchedLine.ProjectiveComparison.lineIsoP1_over]
  have he : (componentTarget k n i).toImage ≫
      (asIso (componentTarget k n i).toImage).inv = 𝟙 _ :=
    (asIso (componentTarget k n i).toImage).hom_inv_id
  rw [← Category.assoc, he, Category.id_comp, ← Category.assoc,
    Scheme.Hom.toImage_imageι, hs]

end AlgebraicGeometry.Scheme.Polygon
end -- noncomputable section
end
section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits AlgebraicGeometry Polynomial
namespace AlgebraicGeometry.Scheme.Polygon
variable (k : Type u) [Field k] (n : ℕ)

/-- Kernel defining the scheme-theoretic union of every affine component other than i. -/
def otherComponentsIdeal (i : Fin n) : Ideal (nodeRing k n) :=
  ⨅ (j : {j : Fin n // j ≠ i}), RingHom.ker (componentProjection k n j.val).toRingHom

@[simp] theorem mem_otherComponentsIdeal (i : Fin n) (p : nodeRing k n) :
    p ∈ otherComponentsIdeal k n i ↔ ∀ j, j ≠ i → p.val j = 0 := by
  simp only [otherComponentsIdeal, Ideal.mem_iInf, RingHom.mem_ker, Subtype.forall]
  rfl

/-- Simultaneous evaluation at the two actual endpoints of component i. -/
def componentEndpoints (i : Fin n) : nodeRing k n →ₐ[k] k × k :=
  ((aeval (0 : k)).prod (aeval (1 : k))).comp (componentProjection k n i)

@[simp] theorem componentEndpoints_apply (i : Fin n) (p : nodeRing k n) :
    componentEndpoints k n i p = ((p.val i).eval 0, (p.val i).eval 1) := rfl

/-- Actual reduced complement ring on the original node affine chart. -/
abbrev otherComponentsRing (i : Fin n) := nodeRing k n ⧸ otherComponentsIdeal k n i

theorem otherComponentsIdeal_le_endpointKernel (hn : 1 < n) (i : Fin n) :
    otherComponentsIdeal k n i ≤ RingHom.ker (componentEndpoints k n i).toRingHom := by
  intro p hp
  rw [mem_otherComponentsIdeal] at hp
  have h := (mem_nodeRing k n p.val).mp p.property
  have h0 := h ((finRotate n).symm i)
  have h1 := h i
  rw [(finRotate n).apply_symm_apply, hp _ (Fin.finRotate_symm_ne_self_of_one_lt n hn i),
    eval_zero] at h0
  rw [hp _ (Fin.finRotate_ne_self_of_one_lt n hn i), eval_zero] at h1
  change componentEndpoints k n i p = 0
  exact Prod.ext h0.symm h1

/-- Scheme-theoretic intersection with the reduced complement. -/
def componentComplementIntersectionIdeal (i : Fin n) : Ideal (nodeRing k n) :=
  RingHom.ker (componentProjection k n i).toRingHom ⊔ otherComponentsIdeal k n i

/-- The genuine intersection ideal is exactly the two endpoint equations. -/
theorem componentComplementIntersectionIdeal_eq_kernel (hn : 1 < n) (i : Fin n) :
    componentComplementIntersectionIdeal k n i =
      RingHom.ker (componentEndpoints k n i).toRingHom := by
  classical
  apply le_antisymm
  · apply sup_le
    · intro p hp
      change p.val i = 0 at hp
      change componentEndpoints k n i p = 0
      simp [componentEndpoints_apply, hp]
    · exact otherComponentsIdeal_le_endpointKernel k n hn i
  · intro p hp
    change componentEndpoints k n i p = 0 at hp
    have h0 : (p.val i).eval 0 = 0 := congrArg Prod.fst hp
    have h1 : (p.val i).eval 1 = 0 := congrArg Prod.snd hp
    let l : nodeRing k n := ⟨Pi.single i (p.val i), by
      rw [mem_nodeRing]
      intro j
      by_cases hj : j = i
      · subst j
        rw [Pi.single_eq_same, Pi.single_eq_of_ne (Fin.finRotate_ne_self_of_one_lt n hn i),
          eval_zero, h1]
      · by_cases hr : finRotate n j = i
        · rw [Pi.single_eq_of_ne hj, hr, Pi.single_eq_same, eval_zero, h0]
        · rw [Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hr, eval_zero, eval_zero]⟩
    have hl : l ∈ otherComponentsIdeal k n i := by
      rw [mem_otherComponentsIdeal]
      intro j hj
      simp [l, Pi.single_eq_of_ne hj]
    have hr : p - l ∈ RingHom.ker (componentProjection k n i).toRingHom := by
      change p.val i - l.val i = 0
      simp [l]
    have he : p - l + l = p := sub_add_cancel p l
    rw [← he]
    exact Ideal.add_mem _ (Ideal.mem_sup_left hr) (Ideal.mem_sup_right hl)

theorem componentEndpoints_surjective (hn : 1 < n) (i : Fin n) :
    Function.Surjective (componentEndpoints k n i) := by
  rintro ⟨a,b⟩
  obtain ⟨p,hp⟩ := componentProjection_surjective k n i
    (Fin.finRotate_ne_self_of_one_lt n hn i) (Polynomial.linearInterpolate k a b)
  refine ⟨p, ?_⟩
  change ((componentProjection k n i p).eval 0, (componentProjection k n i p).eval 1) = (a,b)
  rw [hp, Polynomial.linearInterpolate_zero, Polynomial.linearInterpolate_one]

/-- A ring isomorphism, not merely a pair of topological intersection points. -/
def componentComplementIntersectionEquiv (hn : 1 < n) (i : Fin n) :
    (nodeRing k n ⧸ componentComplementIntersectionIdeal k n i) ≃ₐ[k] (k × k) := by
  rw [componentComplementIntersectionIdeal_eq_kernel k n hn i]
  exact Ideal.quotientKerAlgEquivOfSurjective (componentEndpoints_surjective k n hn i)

theorem componentComplementIntersection_finrank (hn : 1 < n) (i : Fin n) :
    Module.finrank k (nodeRing k n ⧸ componentComplementIntersectionIdeal k n i) = 2 := by
  rw [(componentComplementIntersectionEquiv k n hn i).toLinearEquiv.finrank_eq]
  simp

theorem componentComplementIntersection_reduced (hn : 1 < n) (i : Fin n) :
    _root_.IsReduced (nodeRing k n ⧸ componentComplementIntersectionIdeal k n i) :=
  isReduced_of_injective (componentComplementIntersectionEquiv k n hn i)
    (componentComplementIntersectionEquiv k n hn i).injective

end AlgebraicGeometry.Scheme.Polygon
end -- noncomputable section
end
section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits AlgebraicGeometry Polynomial
namespace AlgebraicGeometry.Scheme.Polygon
variable (k : Type u) [Field k] (n : ℕ)

/-- This ideal really is radical: it cuts out the reduced union of all
normalization components other than the selected component. -/
theorem otherComponentsIdeal_radical (i : Fin n) :
    (otherComponentsIdeal k n i).IsRadical := by
  apply Ideal.isRadical_iInf
  intro j
  rw [RingHom.ker_eq_comap_bot]
  exact Ideal.isRadical_bot.comap _

/-- The quotient defining the union of the other affine components is reduced. -/
instance otherComponentsRing_reduced (i : Fin n) :
    _root_.IsReduced (otherComponentsRing k n i) :=
  (Ideal.isRadical_iff_quotient_reduced _).mp (otherComponentsIdeal_radical k n i)

/-- The actual quotient morphism defining the reduced affine complement. -/
def otherComponentsQuotient (i : Fin n) : nodeRing k n →ₐ[k] otherComponentsRing k n i :=
  Ideal.Quotient.mkₐ k (otherComponentsIdeal k n i)

/-- The reduced affine scheme formed by the components other than `i`. -/
abbrev otherComponentsScheme (i : Fin n) : Scheme.{u} :=
  Spec (.of (otherComponentsRing k n i))

/-- The closed inclusion of the other affine components into the polygon node scheme. -/
def otherComponentsInclusion (i : Fin n) : otherComponentsScheme k n i ⟶ nodeScheme k n :=
  Spec.map (CommRingCat.ofHom (otherComponentsQuotient k n i).toRingHom)

/-- The quotient map defines a closed immersion of the other affine components. -/
instance otherComponentsInclusion_closed (i : Fin n) :
    IsClosedImmersion (otherComponentsInclusion k n i) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- The two actual endpoint evaluations factor through the reduced complement. -/
def otherComponentsEndpoints (hn : 1 < n) (i : Fin n) :
    otherComponentsRing k n i →ₐ[k] k × k :=
  Ideal.Quotient.liftₐ (otherComponentsIdeal k n i) (componentEndpoints k n i)
    (fun _ hp => otherComponentsIdeal_le_endpointKernel k n hn i hp)

@[simp] theorem otherComponentsEndpoints_quotient (hn : 1 < n) (i : Fin n)
    (p : nodeRing k n) :
    otherComponentsEndpoints k n hn i (otherComponentsQuotient k n i p) =
      componentEndpoints k n i p := rfl

/-- The affine intersection is proved by the complete ring pushout property.
Both endpoint points are retained even when n=2 and their neighbouring
component labels coincide. -/
theorem componentComplement_isPushout (hn : 1 < n) (i : Fin n) :
    IsPushout (CommRingCat.ofHom (componentProjection k n i).toRingHom)
      (CommRingCat.ofHom (otherComponentsQuotient k n i).toRingHom)
      (CommRingCat.ofHom (baseBoundary k).toRingHom)
      (CommRingCat.ofHom (otherComponentsEndpoints k n hn i).toRingHom :
        CommRingCat.of (otherComponentsRing k n i) ⟶ CommRingCat.of (k × k)) := by
  apply IsPushout.mk'
  · rfl
  · intro T φ φ' h _
    ext x
    obtain ⟨p, rfl⟩ := baseBoundary_surjective k x
    exact congrArg (fun f : CommRingCat.of k[X] ⟶ T => f p) h
  · intro T a b h
    let q := (componentEndpoints k n i).toRingHom
    let f := a.hom.comp (componentProjection k n i).toRingHom
    have hk : RingHom.ker q ≤ RingHom.ker f := by
      rw [← componentComplementIntersectionIdeal_eq_kernel k n hn i]
      apply sup_le
      · intro p hp
        change componentProjection k n i p = 0 at hp
        change a (componentProjection k n i p) = 0
        rw [hp, map_zero]
      · intro p hp
        have he := congrArg (fun f : CommRingCat.of (nodeRing k n) ⟶ T => f p) h
        change a (componentProjection k n i p) = b (otherComponentsQuotient k n i p) at he
        change a (componentProjection k n i p) = 0
        rw [he]
        have hz : otherComponentsQuotient k n i p = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hp
        rw [hz, map_zero]
    let d : k × k →+* T := q.liftOfSurjective (componentEndpoints_surjective k n hn i) ⟨f,hk⟩
    have hd (p : nodeRing k n) : d (q p) = a (componentProjection k n i p) :=
      RingHom.liftOfSurjective_comp_apply q (componentEndpoints_surjective k n hn i) ⟨f,hk⟩ p
    refine ⟨CommRingCat.ofHom d, ?_, ?_⟩
    · apply CommRingCat.hom_ext
      apply RingHom.ext
      intro p
      obtain ⟨p, rfl⟩ := componentProjection_surjective k n i
        (Fin.finRotate_ne_self_of_one_lt n hn i) p
      exact hd p
    · apply CommRingCat.hom_ext
      apply RingHom.ext
      intro p
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mkₐ_surjective k (otherComponentsIdeal k n i) p
      have he := congrArg (fun f : CommRingCat.of (nodeRing k n) ⟶ T => f p) h
      exact (hd p).trans he

/-- The actual scheme-theoretic intersection is the reduced two-point scheme. -/
theorem componentComplement_isPullback (hn : 1 < n) (i : Fin n) :
    IsPullback (Spec.map (CommRingCat.ofHom (baseBoundary k).toRingHom))
      (Spec.map (CommRingCat.ofHom (otherComponentsEndpoints k n hn i).toRingHom :
        CommRingCat.of (otherComponentsRing k n i) ⟶ CommRingCat.of (k × k)))
      (componentTargetAffine k n i) (otherComponentsInclusion k n i) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (componentComplement_isPushout k n hn i)

/-- For `1 < n`, the affine component-complement intersection identified with two rational
points. -/
def affineComponentComplementIsoTwoPoints (hn : 1 < n) (i : Fin n) :
    pullback (componentTargetAffine k n i) (otherComponentsInclusion k n i) ≅
      Spec (.of (k × k)) :=
  (componentComplement_isPullback k n hn i).isoPullback.symm

@[reassoc] theorem affineComponentComplementIsoTwoPoints_endpoints (hn : 1 < n) (i : Fin n) :
    (affineComponentComplementIsoTwoPoints k n hn i).hom ≫
      Spec.map (CommRingCat.ofHom (baseBoundary k).toRingHom) =
      pullback.fst (componentTargetAffine k n i) (otherComponentsInclusion k n i) :=
  (componentComplement_isPullback k n hn i).isoPullback_inv_fst

/-- Scalar compatibility is retained, so degree is the actual degree over k. -/
@[reassoc] theorem affineComponentComplementIsoTwoPoints_over (hn : 1 < n) (i : Fin n) :
    (affineComponentComplementIsoTwoPoints k n hn i).hom ≫
      AlgebraicGeometry.Spec.algebraMap k (k × k) =
      pullback.fst (componentTargetAffine k n i) (otherComponentsInclusion k n i) ≫
        AlgebraicGeometry.Spec.algebraMap k k[X] := by
  have he : Spec.map (CommRingCat.ofHom (baseBoundary k).toRingHom) ≫
      AlgebraicGeometry.Spec.algebraMap k k[X] = AlgebraicGeometry.Spec.algebraMap k (k × k) := by
    unfold AlgebraicGeometry.Spec.algebraMap
    rw [← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (baseBoundary k).comp_algebraMap
  rw [← he, ← Category.assoc, affineComponentComplementIsoTwoPoints_endpoints]

/-- For `1 < n`, the affine component-complement intersection identified with two points over
`k`. -/
def affineComponentComplementOverIsoTwoPoints (hn : 1 < n) (i : Fin n) :
    Over.mk (pullback.fst (componentTargetAffine k n i) (otherComponentsInclusion k n i) ≫
      AlgebraicGeometry.Spec.algebraMap k k[X]) ≅
      Over.mk (AlgebraicGeometry.Spec.algebraMap k (k × k)) :=
  Over.isoMk (affineComponentComplementIsoTwoPoints k n hn i)
    (affineComponentComplementIsoTwoPoints_over k n hn i)

theorem affineComponentComplement_degree (hn : 1 < n) (i : Fin n) :
    Scheme.Hom.finiteSchemeDegree k
      (pullback.fst (componentTargetAffine k n i) (otherComponentsInclusion k n i) ≫
        AlgebraicGeometry.Spec.algebraMap k k[X]) = 2 := by
  rw [Scheme.Hom.finiteSchemeDegree_iso _ _
    (affineComponentComplementIsoTwoPoints k n hn i)
    (affineComponentComplementIsoTwoPoints_over k n hn i)]
  exact Scheme.Hom.twoPointSchemeDegree k

end AlgebraicGeometry.Scheme.Polygon
end -- noncomputable section
end
section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits AlgebraicGeometry Polynomial Opposite
namespace AlgebraicGeometry.Scheme.Polygon
open Scheme.IdealSheafData
variable (k : Type u) [Field k] (n : ℕ)

/-- The affine polynomial chart inclusion of the selected projective-line parametrization. -/
abbrev selectedLineAffine : Spec (.of k[X]) ⟶ Scheme.PinchedLine.lineGluing k :=
  pushout.inl (Scheme.PinchedLine.normalizationOverlapInclusion k)
    (Scheme.PinchedLine.gluingToInfinity k)

/-- The node-scheme chart inclusion of the polygon curve. -/
abbrev cycleAffineChart : nodeScheme k n ⟶ cycleScheme k n :=
  pushout.inl (gluingToNode k n) (gluingToInfinity k n)

/-- The product polynomial chart inclusion of the normalization gluing. -/
abbrev normalizedAffineChart : Spec (.of (NormalizationRing k n)) ⟶ normalizedScheme k n :=
  pushout.inl (normalizationOverlapInclusion k n) (gluingToInfinity k n)

/-- The polynomial chart of each literal normalization component is exactly
its inverse image of the polynomial chart of the whole normalization. -/
theorem componentLine_preimage_affine (i : Fin n) :
    componentLine k n i ⁻¹ᵁ (normalizedAffineChart k n).opensRange =
      (selectedLineAffine k).opensRange := by
  ext x
  constructor
  · rintro ⟨q,hq⟩
    obtain ⟨⟨j,p⟩,rfl⟩ := (PrimeSpectrum.sigmaToPi_bijective
      (fun _ : Fin n => k[X])).surjective q
    have he : componentLine k n j (selectedLineAffine k p) = componentLine k n i x := by
      change (selectedLineAffine k ≫ componentLine k n j) p = _
      rw [componentLine_affine]
      exact hq
    have hji := componentLine_index_eq k n j i _ _ he
    subst j
    exact ⟨p,(componentLine k n i).isOpenEmbedding.injective he⟩
  · rintro ⟨p,rfl⟩
    refine ⟨componentAffine k n i p, ?_⟩
    exact congrArg (fun f : Spec (.of k[X]) ⟶ normalizedScheme k n => f p)
      (componentLine_affine k n i).symm

/-- Thus the selected global component has precisely its polynomial chart
over the node chart of the global cyclic curve. -/
theorem componentTarget_preimage_affine (i : Fin n) :
    componentTarget k n i ⁻¹ᵁ (cycleAffineChart k n).opensRange =
      (selectedLineAffine k).opensRange := by
  change componentLine k n i ⁻¹ᵁ
    (gluedPolynomialCover k n ⁻¹ᵁ (cycleAffineChart k n).opensRange) = _
  have h := Scheme.OpenNormalizationGluing.preimage_affine (gluingToNode k n)
    (gluingToInfinity k n) (normalizationOverlapInclusion k n) (polynomialCover k n)
    (conductorOpenIso_over k n).symm
  change gluedPolynomialCover k n ⁻¹ᵁ (cycleAffineChart k n).opensRange =
    (normalizedAffineChart k n).opensRange at h
  rw [h]
  exact componentLine_preimage_affine k n i

theorem componentTarget_affine_isPullback (i : Fin n) :
    IsPullback (componentTargetAffine k n i) (selectedLineAffine k)
      (cycleAffineChart k n) (componentTarget k n i) :=
  IsOpenImmersion.isPullback _ _ _ _ (componentTarget_affine k n i)
    (componentTarget_preimage_affine k n i)

theorem componentTarget_kernel_affine (i : Fin n) :
    (componentTarget k n i).ker.comap (cycleAffineChart k n) =
      (componentTargetAffine k n i).ker :=
  kernel_comap_open_pullback _ _ _ _ (componentTarget_affine_isPullback k n i)

/-- The actual closed subset formed by every other component, with its native
reduced induced scheme structure. -/
def otherGlobalSupport (i : Fin n) : TopologicalSpace.Closeds (cycleScheme k n) :=
  ⟨⋃ j : {j : Fin n // j ≠ i}, targetComponent k n j.val,
    isClosed_iUnion_of_finite (fun j => targetComponent_closed k n j.val)⟩

/-- The vanishing ideal sheaf of the union of the other global component images. -/
def otherGlobalIdeal (i : Fin n) : (cycleScheme k n).IdealSheafData :=
  vanishingIdeal (otherGlobalSupport k n i)

/-- The reduced closed subscheme supported on the union of the other global component images. -/
abbrev otherGlobalScheme (i : Fin n) : Scheme.{u} := (otherGlobalIdeal k n i).subscheme
/-- The inclusion of the reduced union of the other global components into the polygon curve. -/
abbrev otherGlobalInclusion (i : Fin n) : otherGlobalScheme k n i ⟶ cycleScheme k n :=
  (otherGlobalIdeal k n i).subschemeι

theorem otherGlobalInclusion_range (i : Fin n) :
    Set.range (otherGlobalInclusion k n i) =
      ⋃ j : {j : Fin n // j ≠ i}, targetComponent k n j.val := by
  rw [range_subschemeι]
  exact coe_support_vanishingIdeal _

/-- The reduced union is the intersection of the genuine component ideals. -/
theorem otherGlobalIdeal_eq_iInf (i : Fin n) :
    otherGlobalIdeal k n i =
      ⨅ j : {j : Fin n // j ≠ i}, (componentTarget k n j.val).ker := by
  have hs : otherGlobalSupport k n i =
      ⨆ j : {j : Fin n // j ≠ i},
        (⟨targetComponent k n j.val, targetComponent_closed k n j.val⟩ :
          TopologicalSpace.Closeds (cycleScheme k n)) := by
    apply le_antisymm
    · rintro x hx
      rcases Set.mem_iUnion.mp hx with ⟨j,hj⟩
      exact le_iSup (fun j : {j : Fin n // j ≠ i} =>
        (⟨targetComponent k n j.val, targetComponent_closed k n j.val⟩ :
          TopologicalSpace.Closeds (cycleScheme k n))) j hj
    · apply iSup_le
      intro j x hx
      exact Set.mem_iUnion.mpr ⟨j,hx⟩
  unfold otherGlobalIdeal
  rw [hs, vanishingIdeal_iSup]
  congr 1
  funext j
  rw [Scheme.IdealSheafData.kernel_eq_vanishingIdeal]
  congr 1
  ext x
  rw [Scheme.Hom.support_ker, componentTarget_range,
    (targetComponent_closed k n j.val).closure_eq]
  rfl

/-- The global union of the other component images has its reduced scheme structure. -/
instance otherGlobalScheme_reduced (i : Fin n) : IsReduced (otherGlobalScheme k n i) := by
  apply subscheme_reduced_of_radical
  ext U : 2
  apply Ideal.radical_eq_iff.mpr
  exact PrimeSpectrum.isRadical_vanishingIdeal _

/-- The global reduced complement restricts to the constructed quotient
by the intersection of the other coordinate kernels, scheme-theoretically. -/
theorem otherGlobalIdeal_affine (i : Fin n) :
    (otherGlobalIdeal k n i).comap (cycleAffineChart k n) =
      (otherComponentsInclusion k n i).ker := by
  rw [otherGlobalIdeal_eq_iInf, comap_finite_iInf]
  simp only [componentTarget_kernel_affine]
  apply Scheme.IdealSheafData.ext_of_isAffine
  simp only [ideal_iInf, iInf_apply]
  simp only [componentTargetAffine, otherComponentsInclusion, specMap_kernel_top,
    ← Ideal.comap_iInf]
  congr 1
  exact (Ideal.mk_ker (I := otherComponentsIdeal k n i)).symm

/-- The actual affine complementary union maps into the actual global one. -/
def otherAffineToGlobal (i : Fin n) : otherComponentsScheme k n i ⟶ otherGlobalScheme k n i :=
  IsClosedImmersion.lift (otherGlobalInclusion k n i)
    (otherComponentsInclusion k n i ≫ cycleAffineChart k n) (by
      rw [ker_subschemeι, Scheme.Hom.ker_comp]
      apply le_map_iff_comap_le.mpr
      rw [otherGlobalIdeal_affine])

@[reassoc (attr := simp)] theorem otherAffineToGlobal_inclusion (i : Fin n) :
    otherAffineToGlobal k n i ≫ otherGlobalInclusion k n i =
      otherComponentsInclusion k n i ≫ cycleAffineChart k n :=
  IsClosedImmersion.lift_fac _ _ _

theorem otherGlobal_affine_isPullback (i : Fin n) :
    IsPullback (otherComponentsInclusion k n i) (otherAffineToGlobal k n i)
      (cycleAffineChart k n) (otherGlobalInclusion k n i) := by
  apply isPullback_of_isClosedImmersion
  · exact (otherAffineToGlobal_inclusion k n i).symm
  · rw [ker_subschemeι, otherGlobalIdeal_affine]

/-- The affine complement scheme is an open chart of the global complement scheme. -/
instance otherAffineToGlobal_open (i : Fin n) : IsOpenImmersion (otherAffineToGlobal k n i) :=
  MorphismProperty.of_isPullback (otherGlobal_affine_isPullback k n i) inferInstance

end AlgebraicGeometry.Scheme.Polygon
end -- noncomputable section
end
section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits AlgebraicGeometry Polynomial
namespace AlgebraicGeometry.Scheme.Polygon
variable (k : Type u) [Field k] (n : ℕ)

/-- The global scheme-theoretic intersection with the reduced union of all
other components, not a count or a chosen endpoint scheme. -/
abbrev globalComponentComplement (i : Fin n) : Scheme.{u} :=
  pullback (componentTarget k n i) (otherGlobalInclusion k n i)
/-- The projection of the global component-complement intersection to the selected line. -/
abbrev globalComplementFirst (i : Fin n) : globalComponentComplement k n i ⟶
  Scheme.PinchedLine.lineGluing k :=
  pullback.fst _ _
/-- The projection of the global component-complement intersection to the complement scheme. -/
abbrev globalComplementSecond (i : Fin n) : globalComponentComplement k n i ⟶ otherGlobalScheme
  k n i :=
  pullback.snd _ _
/-- The inclusion map from the global component-complement intersection to the polygon curve. -/
abbrev globalComplementMap (i : Fin n) : globalComponentComplement k n i ⟶ cycleScheme k n :=
  globalComplementFirst k n i ≫ componentTarget k n i

/-- Distinct normalization components cannot meet above the infinity chart,
where the actual normalization map is an isomorphism. -/
theorem globalComponentComplement_not_infinity (i : Fin n)
    (z : globalComponentComplement k n i) (v : infinityScheme k n) :
    globalComplementMap k n i z ≠
      pushout.inr (gluingToNode k n) (gluingToInfinity k n) v := by
  intro hv
  have hz : globalComplementMap k n i z ∈
      Set.range (otherGlobalInclusion k n i) := by
    refine ⟨globalComplementSecond k n i z, ?_⟩
    exact congrArg (fun f : globalComponentComplement k n i ⟶ cycleScheme k n => f z)
      (pullback.condition (f := componentTarget k n i) (g := otherGlobalInclusion k n i)).symm
  rw [otherGlobalInclusion_range] at hz
  rcases Set.mem_iUnion.mp hz with ⟨j,hj⟩
  rw [← componentTarget_range] at hj
  rcases hj with ⟨y,hy⟩
  have hi : componentLine k n i (globalComplementFirst k n i z) =
      pushout.inr (normalizationOverlapInclusion k n) (gluingToInfinity k n) v :=
    (gluedPolynomialCover_infinity_fibre k n v _).mp hv
  have hj' : componentLine k n j.val y =
      pushout.inr (normalizationOverlapInclusion k n) (gluingToInfinity k n) v :=
    (gluedPolynomialCover_infinity_fibre k n v _).mp (hy.trans hv)
  exact j.property (componentLine_index_eq k n j.val i _ _ (hj'.trans hi.symm))

/-- The global component-complement intersection has empty inverse image in the infinity chart. -/
instance globalComponentComplement_infinity_empty (i : Fin n) :
    IsEmpty (pullback (globalComplementMap k n i)
      (pushout.inr (gluingToNode k n) (gluingToInfinity k n)) : Scheme.{u}) := by
  apply Scheme.isEmpty_pullback
  rw [Set.disjoint_left]
  rintro _ ⟨z,rfl⟩ ⟨v,hv⟩
  exact globalComponentComplement_not_infinity k n i z v hv.symm

theorem globalComplementMap_range_affine (i : Fin n) :
    Set.range (globalComplementMap k n i) ⊆ Set.range (cycleAffineChart k n) := by
  rintro _ ⟨z,rfl⟩
  rcases Scheme.openPushout_covered (gluingToNode k n) (gluingToInfinity k n)
    (globalComplementMap k n i z) with ⟨p,hp⟩ | ⟨v,hv⟩
  · exact ⟨p,hp⟩
  · exact (globalComponentComplement_not_infinity k n i z v hv.symm).elim

/-- Universal open factorization of the entire global intersection into the
node chart, justified by the proved empty infinity intersection. -/
def globalComplementToNode (i : Fin n) : globalComponentComplement k n i ⟶ nodeScheme k n :=
  IsOpenImmersion.lift (cycleAffineChart k n) (globalComplementMap k n i)
    (globalComplementMap_range_affine k n i)

@[reassoc (attr := simp)] theorem globalComplementToNode_chart (i : Fin n) :
    globalComplementToNode k n i ≫ cycleAffineChart k n = globalComplementMap k n i :=
  IsOpenImmersion.lift_fac _ _ _

/-- The projection of the global intersection lifted to the polynomial chart of the selected
line. -/
def globalComplementAffineFirst (i : Fin n) : globalComponentComplement k n i ⟶ Spec (.of k[X]) :=
  pullback.lift (globalComplementToNode k n i) (globalComplementFirst k n i)
    (globalComplementToNode_chart k n i) ≫
      (componentTarget_affine_isPullback k n i).isoPullback.inv

/-- The projection of the global intersection lifted to the affine complement scheme. -/
def globalComplementAffineSecond (i : Fin n) :
    globalComponentComplement k n i ⟶ otherComponentsScheme k n i :=
  pullback.lift (globalComplementToNode k n i) (globalComplementSecond k n i)
    ((globalComplementToNode_chart k n i).trans pullback.condition) ≫
      (otherGlobal_affine_isPullback k n i).isoPullback.inv

@[reassoc (attr := simp)] theorem globalComplementAffineFirst_chart (i : Fin n) :
    globalComplementAffineFirst k n i ≫ selectedLineAffine k = globalComplementFirst k n i := by
  simp [globalComplementAffineFirst]

@[reassoc (attr := simp)] theorem globalComplementAffineSecond_chart (i : Fin n) :
    globalComplementAffineSecond k n i ≫ otherAffineToGlobal k n i = globalComplementSecond k n
      i := by
  simp [globalComplementAffineSecond]

@[reassoc (attr := simp)] theorem globalComplementAffineFirst_target (i : Fin n) :
    globalComplementAffineFirst k n i ≫ componentTargetAffine k n i = globalComplementToNode k
      n i := by
  simp [globalComplementAffineFirst]

@[reassoc (attr := simp)] theorem globalComplementAffineSecond_target (i : Fin n) :
    globalComplementAffineSecond k n i ≫ otherComponentsInclusion k n i =
      globalComplementToNode k n i := by
  simp [globalComplementAffineSecond]

/-- The global component-complement intersection mapped to its affine pullback presentation. -/
def globalComplementToAffine (i : Fin n) : globalComponentComplement k n i ⟶
    pullback (componentTargetAffine k n i) (otherComponentsInclusion k n i) :=
  pullback.lift (globalComplementAffineFirst k n i) (globalComplementAffineSecond k n i) (by simp)

/-- The affine component-complement pullback mapped to the global intersection. -/
def affineComplementToGlobal (i : Fin n) :
    pullback (componentTargetAffine k n i) (otherComponentsInclusion k n i) ⟶
      globalComponentComplement k n i :=
  pullback.lift (pullback.fst _ _ ≫ selectedLineAffine k)
    (pullback.snd _ _ ≫ otherAffineToGlobal k n i) (by
      rw [Category.assoc, componentTarget_affine, Category.assoc, otherAffineToGlobal_inclusion,
        ← Category.assoc, ← Category.assoc, pullback.condition])

/-- The global scheme intersection is isomorphic to its computed affine one;
this retains its whole local-ring structure. -/
def globalComplementAffineIso (i : Fin n) : globalComponentComplement k n i ≅
    pullback (componentTargetAffine k n i) (otherComponentsInclusion k n i) where
  hom := globalComplementToAffine k n i
  inv := affineComplementToGlobal k n i
  hom_inv_id := by
    apply pullback.hom_ext <;>
      simp [globalComplementToAffine, affineComplementToGlobal, Category.assoc]
  inv_hom_id := by
    apply pullback.hom_ext
    · apply (cancel_mono (selectedLineAffine k)).mp
      simp [globalComplementToAffine, affineComplementToGlobal, Category.assoc]
    · apply (cancel_mono (otherAffineToGlobal k n i)).mp
      simp [globalComplementToAffine, affineComplementToGlobal, Category.assoc]

/-- The actual selected component meets its actual reduced complement in two
reduced rational points, including the two distinct intersections for n=2. -/
def globalComponentComplementIsoTwoPoints (hn : 1 < n) (i : Fin n) :
    globalComponentComplement k n i ≅ Spec (.of (k × k)) :=
  globalComplementAffineIso k n i ≪≫ affineComponentComplementIsoTwoPoints k n hn i

@[reassoc] theorem globalComponentComplementIsoTwoPoints_over (hn : 1 < n) (i : Fin n) :
    (globalComponentComplementIsoTwoPoints k n hn i).hom ≫
      AlgebraicGeometry.Spec.algebraMap k (k × k) =
      globalComplementFirst k n i ≫ Scheme.PinchedLine.lineStructure k := by
  rw [globalComponentComplementIsoTwoPoints, Iso.trans_hom, Category.assoc,
    affineComponentComplementIsoTwoPoints_over]
  change globalComplementToAffine k n i ≫ pullback.fst _ _ ≫
    AlgebraicGeometry.Spec.algebraMap k k[X] = _
  rw [← Category.assoc, show globalComplementToAffine k n i ≫ pullback.fst _ _ =
    globalComplementAffineFirst k n i from pullback.lift_fst _ _ _]
  have hl : selectedLineAffine k ≫ Scheme.PinchedLine.lineStructure k =
      AlgebraicGeometry.Spec.algebraMap k k[X] := pushout.inl_desc _ _ _
  rw [← hl, ← Category.assoc, globalComplementAffineFirst_chart]

theorem globalComponentComplement_degree (hn : 1 < n) (i : Fin n) :
    Scheme.Hom.finiteSchemeDegree k
      (globalComplementFirst k n i ≫ Scheme.PinchedLine.lineStructure k) = 2 := by
  rw [Scheme.Hom.finiteSchemeDegree_iso _ _ (globalComponentComplementIsoTwoPoints k n hn i)
    (globalComponentComplementIsoTwoPoints_over k n hn i)]
  exact Scheme.Hom.twoPointSchemeDegree k

theorem globalComponentComplement_reduced (hn : 1 < n) (i : Fin n) :
    IsReduced (globalComponentComplement k n i) :=
  isReduced_of_isOpenImmersion (globalComponentComplementIsoTwoPoints k n hn i).hom

theorem globalComponentComplement_finite (hn : 1 < n) (i : Fin n) :
    IsFinite (globalComplementFirst k n i ≫ Scheme.PinchedLine.lineStructure k) := by
  rw [← globalComponentComplementIsoTwoPoints_over k n hn i]
  have : IsFinite (AlgebraicGeometry.Spec.algebraMap k (k × k)) := by
    unfold AlgebraicGeometry.Spec.algebraMap
    apply (IsFinite.SpecMap_iff _).mpr
    exact RingHom.finite_algebraMap.mpr inferInstance
  infer_instance

end AlgebraicGeometry.Scheme.Polygon
end -- noncomputable section
end
section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits AlgebraicGeometry Polynomial
namespace AlgebraicGeometry.Scheme.Polygon
variable (k : Type u) [Field k] (n : ℕ)

/-- These are the two canonical rational sections of the computed intersection. -/
def endpointZeroSection : Spec (.of k) ⟶ Spec (.of (k × k)) :=
  Spec.map (CommRingCat.ofHom (RingHom.fst k k))
/-- The section selecting the second factor of `Spec (k × k)`, corresponding to endpoint one. -/
def endpointOneSection : Spec (.of k) ⟶ Spec (.of (k × k)) :=
  Spec.map (CommRingCat.ofHom (RingHom.snd k k))

theorem endpointZero_to_node (i : Fin n) :
    endpointZeroSection k ≫ Spec.map (CommRingCat.ofHom (baseBoundary k).toRingHom) ≫
      componentTargetAffine k n i =
      Spec.map (CommRingCat.ofHom (nodeValue k n ((finRotate n).symm i))) := by
  unfold endpointZeroSection componentTargetAffine
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro p
  change (p.val i).eval 0 = (p.val ((finRotate n).symm i)).eval 1
  simpa only [Equiv.apply_symm_apply] using ((mem_nodeRing k n p.val).mp p.property
    ((finRotate n).symm i)).symm

theorem endpointOne_to_node (i : Fin n) :
    endpointOneSection k ≫ Spec.map (CommRingCat.ofHom (baseBoundary k).toRingHom) ≫
      componentTargetAffine k n i =
      Spec.map (CommRingCat.ofHom (nodeValue k n i)) := by
  unfold endpointOneSection componentTargetAffine
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

@[reassoc] theorem globalComponentComplementIsoTwoPoints_endpoints (hn : 1 < n) (i : Fin n) :
    (globalComponentComplementIsoTwoPoints k n hn i).hom ≫
      Spec.map (CommRingCat.ofHom (baseBoundary k).toRingHom) ≫ selectedLineAffine k =
      globalComplementFirst k n i := by
  rw [globalComponentComplementIsoTwoPoints, Iso.trans_hom, ← Category.assoc,
    Category.assoc (globalComplementAffineIso k n i).hom,
    affineComponentComplementIsoTwoPoints_endpoints]
  change globalComplementToAffine k n i ≫ pullback.fst _ _ ≫ selectedLineAffine k = _
  simp [globalComplementToAffine]

/-- The first true endpoint is exactly the preceding existing node section. -/
theorem globalComplement_zero_endpoint (hn : 1 < n) (i : Fin n) :
    endpointZeroSection k ≫ (globalComponentComplementIsoTwoPoints k n hn i).inv ≫
      globalComplementMap k n i =
      Spec.map (CommRingCat.ofHom (nodeValue k n ((finRotate n).symm i))) ≫
        cycleAffineChart k n := by
  have he : (globalComponentComplementIsoTwoPoints k n hn i).inv ≫
      globalComplementMap k n i =
      Spec.map (CommRingCat.ofHom (baseBoundary k).toRingHom) ≫
        componentTargetAffine k n i ≫ cycleAffineChart k n := by
    apply (cancel_epi (globalComponentComplementIsoTwoPoints k n hn i).hom).mp
    simp only [Iso.hom_inv_id_assoc, globalComplementMap]
    rw [← componentTarget_affine]
    simpa only [Category.assoc] using
      (globalComponentComplementIsoTwoPoints_endpoints_assoc k n hn i (componentTarget k n i)).symm
  rw [he]
  simpa only [Category.assoc] using congrArg (· ≫ cycleAffineChart k n) (endpointZero_to_node k n i)

/-- The second true endpoint is exactly the following existing node section. -/
theorem globalComplement_one_endpoint (hn : 1 < n) (i : Fin n) :
    endpointOneSection k ≫ (globalComponentComplementIsoTwoPoints k n hn i).inv ≫
      globalComplementMap k n i =
      Spec.map (CommRingCat.ofHom (nodeValue k n i)) ≫ cycleAffineChart k n := by
  have he : (globalComponentComplementIsoTwoPoints k n hn i).inv ≫
      globalComplementMap k n i =
      Spec.map (CommRingCat.ofHom (baseBoundary k).toRingHom) ≫
        componentTargetAffine k n i ≫ cycleAffineChart k n := by
    apply (cancel_epi (globalComponentComplementIsoTwoPoints k n hn i).hom).mp
    simp only [Iso.hom_inv_id_assoc, globalComplementMap]
    rw [← componentTarget_affine]
    simpa only [Category.assoc] using
      (globalComponentComplementIsoTwoPoints_endpoints_assoc k n hn i (componentTarget k n i)).symm
  rw [he]
  simpa only [Category.assoc] using congrArg (· ≫ cycleAffineChart k n) (endpointOne_to_node k n i)

theorem component_endpoint_nodes_distinct (hn : 1 < n) (i : Fin n) :
    gluedNodePoint k n ((finRotate n).symm i) ≠ gluedNodePoint k n i :=
  fun h => Fin.finRotate_symm_ne_self_of_one_lt n hn i (gluedNodePoint_injective k n h)

/-- A selected component is genuinely not contained in the union of the
others: its infinity point is missed by every other normalization component. -/
theorem componentTarget_not_subset_other (i : Fin n) :
    ¬ Set.range (componentTarget k n i) ⊆ Set.range (otherGlobalInclusion k n i) := by
  intro h
  obtain ⟨v⟩ := (inferInstance : Nonempty (Spec (.of (V k))))
  let x := pushout.inr (Scheme.PinchedLine.normalizationOverlapInclusion k)
    (Scheme.PinchedLine.gluingToInfinity k) v
  have hx : componentTarget k n i x =
      pushout.inr (gluingToNode k n) (gluingToInfinity k n) (componentInfinity k n i v) :=
    congrArg (fun f : Spec (.of (V k)) ⟶ cycleScheme k n => f v)
      (componentTarget_infinity k n i)
  have hh := h ⟨x,rfl⟩
  rw [otherGlobalInclusion_range] at hh
  rcases Set.mem_iUnion.mp hh with ⟨j,hj⟩
  rw [← componentTarget_range] at hj
  rcases hj with ⟨y,hy⟩
  have hi := (gluedPolynomialCover_infinity_fibre k n _ _).mp hx
  have hj' := (gluedPolynomialCover_infinity_fibre k n _ _).mp (hy.trans hx)
  exact j.property (componentLine_index_eq k n j.val i _ _ (hj'.trans hi.symm))

theorem component_and_others_cover (i : Fin n) :
    Set.range (componentTarget k n i) ∪ Set.range (otherGlobalInclusion k n i) = Set.univ := by
  rw [componentTarget_range, otherGlobalInclusion_range]
  apply Set.eq_univ_of_forall
  intro z
  obtain ⟨j,hj⟩ := targetComponents_cover k n z
  by_cases h : j = i
  · exact Or.inl (h ▸ hj)
  · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨j,h⟩,hj⟩)

/-- The global curve is reduced by its two actual reduced affine charts. -/
theorem cycleScheme_reduced_from_charts : IsReduced (cycleScheme k n) := by
  let C := Scheme.OpenNormalizationGluing.twoChartCover (gluingToNode k n) (gluingToInfinity k n)
  let : ∀ b, IsReduced (C.X b) := fun b => by
    cases b
    · exact inferInstanceAs (IsReduced (nodeScheme k n))
    · exact inferInstanceAs (IsReduced (infinityScheme k n))
  exact IsReduced.of_openCover _ C

/-- The one-gon has no other component. Its complement ideal is the unit ideal;
no smooth-component or two-endpoint claim is made for that nodal component. -/
theorem otherGlobalIdeal_one_eq_top (i : Fin 1) : otherGlobalIdeal k 1 i = ⊤ := by
  rw [otherGlobalIdeal_eq_iInf]
  let : IsEmpty {j : Fin 1 // j ≠ i} := ⟨fun j => j.property (Subsingleton.elim _ _)⟩
  simp

end AlgebraicGeometry.Scheme.Polygon
end -- noncomputable section
end
section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits AlgebraicGeometry Polynomial

namespace AlgebraicGeometry.Scheme.Polygon
variable (k : Type u) [Field k] (n : ℕ)

/-- The closed component parameter retains the original residue-field structure. -/
@[reassoc] theorem componentTarget_over (i : Fin n) :
    componentTarget k n i ≫ structureMap k n = Scheme.PinchedLine.lineStructure k := by
  apply pushout.hom_ext
  · simp only [componentTarget, componentLine, gluedPolynomialCover,
      Scheme.OpenNormalizationGluing.normalizationMap, structureMap, cycleMap,
      Scheme.PinchedLine.pinchedStructure, Scheme.PinchedLine.lineStructure, Category.assoc,
      pushout.inl_desc_assoc, pushout.inl_desc]
    change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = Spec.map _
    simp only [← Spec.map_comp]
    rfl
  · simp only [componentTarget, componentLine, gluedPolynomialCover,
      Scheme.OpenNormalizationGluing.normalizationMap, structureMap, cycleMap,
      Scheme.PinchedLine.pinchedStructure, Scheme.PinchedLine.lineStructure, Category.assoc,
      pushout.inr_desc_assoc, pushout.inr_desc]
    change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = Spec.map _
    simp only [← Spec.map_comp]
    rfl
end AlgebraicGeometry.Scheme.Polygon
end
end
