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
public import Aglib.AlgebraicGeometry.Curves.Nodal.TwoGon.Gluing
public import Aglib.AlgebraicGeometry.Curves.Nodal.Projective
public import Aglib.Topology.Irreducible.ClosedCover

/-!
# The literal two-component pinched curve: Components

Source: frozen R5 `Curves/Cyclic/TwoGon/Components.lean`, revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`.
The actual ring maps, gluing arrows and component indices are retained.
This leaf does not construct a marked model or assume a model-existence theorem.
-/

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Polynomial
open scoped Polynomial
universe u

namespace AlgebraicGeometry.Scheme.TwoGon

private theorem normalityOfOpen {U X : Scheme.{u}} (f : U ⟶ X)
    [IsOpenImmersion f] (x : U)
    (h : IsDomain (U.presheaf.stalk x) ∧ IsIntegrallyClosed (U.presheaf.stalk x)) :
    IsDomain (X.presheaf.stalk (f x)) ∧ IsIntegrallyClosed (X.presheaf.stalk (f x)) := by
  let := h.1
  let := h.2
  let e := (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv
  exact ⟨e.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e.symm⟩

private theorem normalityOfIso {X Y : Scheme.{u}} (e : X ≅ Y) (h : NormalStalks Y) :
    NormalStalks X := by
  intro x
  have hx := h (e.hom x)
  let := hx.1
  let := hx.2
  let r := (asIso (e.hom.stalkMap x)).commRingCatIsoToRingEquiv
  exact ⟨r.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv r⟩

end AlgebraicGeometry.Scheme.TwoGon

section
open Set

end
section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits AlgebraicGeometry Polynomial
open scoped Polynomial TensorProduct
namespace AlgebraicGeometry.Scheme.TwoGon
open Affine
open Scheme.OpenPushout Scheme.Pullback.SpecProducts Localization.Away
variable (k : Type u) [Field k]

/-- The left projective-line component included in the normalization gluing. -/
def leftComponent : Scheme.PinchedLine.lineGluing k ⟶ normalized k :=
  coprod.inl ≫ (normalizationLinesIso k).inv

/-- The right projective-line component included in the normalization gluing. -/
def rightComponent : Scheme.PinchedLine.lineGluing k ⟶ normalized k :=
  coprod.inr ≫ (normalizationLinesIso k).inv

/-- The left projective-line component is open in the normalization gluing. -/
instance leftComponent_open : IsOpenImmersion (leftComponent k) := by
  unfold leftComponent
  infer_instance
/-- The right projective-line component is open in the normalization gluing. -/
instance rightComponent_open : IsOpenImmersion (rightComponent k) := by
  unfold rightComponent
  infer_instance

@[simp] theorem leftComponent_toLines (x : Scheme.PinchedLine.lineGluing k) :
    (normalizationLinesIso k).hom (leftComponent k x) = (coprod.inl :
      Scheme.PinchedLine.lineGluing k ⟶ Scheme.PinchedLine.lineGluing k ⨿
      Scheme.PinchedLine.lineGluing k) x := by
  simp only [leftComponent, ← Scheme.Hom.comp_apply, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
@[simp] theorem rightComponent_toLines (x : Scheme.PinchedLine.lineGluing k) :
    (normalizationLinesIso k).hom (rightComponent k x) = (coprod.inr :
      Scheme.PinchedLine.lineGluing k ⟶ Scheme.PinchedLine.lineGluing k ⨿
      Scheme.PinchedLine.lineGluing k) x := by
  simp only [rightComponent, ← Scheme.Hom.comp_apply, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

theorem leftComponent_ne_right (x y : Scheme.PinchedLine.lineGluing k) :
    leftComponent k x ≠ rightComponent k y := by
  intro h
  have h' := congrArg (normalizationLinesIso k).hom h
  simp only [leftComponent_toLines, rightComponent_toLines] at h'
  exact inl_ne_inr _ _ x y h'

theorem source_components_cover (z : normalized k) :
    (∃ x, leftComponent k x = z) ∨ ∃ y, rightComponent k y = z := by
  obtain ⟨x | x, hx⟩ := (coprodMk (Scheme.PinchedLine.lineGluing k)
    (Scheme.PinchedLine.lineGluing k)).surjective
    ((normalizationLinesIso k).hom z)
  · left
    refine ⟨x, (normalizationLinesIso k).hom.isOpenEmbedding.injective ?_⟩
    simpa only [coprodMk_inl, leftComponent_toLines] using hx
  · right
    refine ⟨x, (normalizationLinesIso k).hom.isOpenEmbedding.injective ?_⟩
    simpa only [coprodMk_inr, rightComponent_toLines] using hx

theorem source_left_compl : (Set.range (leftComponent k))ᶜ = Set.range (rightComponent k) := by
  ext z
  constructor
  · intro hz
    rcases source_components_cover k z with h | h
    · exact (hz h).elim
    · exact h
  · rintro ⟨y, rfl⟩ ⟨x, h⟩
    exact leftComponent_ne_right k x y h

theorem source_right_compl : (Set.range (rightComponent k))ᶜ = Set.range (leftComponent k) := by
  rw [← source_left_compl, compl_compl]

theorem leftComponent_isClosed : IsClosed (Set.range (leftComponent k)) := by
  rw [← isOpen_compl_iff, source_left_compl]
  exact (rightComponent k).isOpenEmbedding.isOpen_range

theorem rightComponent_isClosed : IsClosed (Set.range (rightComponent k)) := by
  rw [← isOpen_compl_iff, source_right_compl]
  exact (leftComponent k).isOpenEmbedding.isOpen_range

theorem leftComponent_irreducible : IsIrreducible (Set.range (leftComponent k)) := by
  simpa only [Set.image_univ] using
    (IrreducibleSpace.isIrreducible_univ (Scheme.PinchedLine.lineGluing k)).image _
      (leftComponent k).continuous.continuousOn

theorem rightComponent_irreducible : IsIrreducible (Set.range (rightComponent k)) := by
  simpa only [Set.image_univ] using
    (IrreducibleSpace.isIrreducible_univ (Scheme.PinchedLine.lineGluing k)).image _
      (rightComponent k).continuous.continuousOn

theorem source_components_eq : irreducibleComponents (normalized k) =
    {Set.range (leftComponent k), Set.range (rightComponent k)} := by
  apply irreducibleComponents_eq_pair (leftComponent_isClosed k) (rightComponent_isClosed k)
    (leftComponent_irreducible k) (rightComponent_irreducible k)
  · ext z
    exact ⟨fun _ => trivial, fun _ => source_components_cover k z⟩
  · intro h
    obtain ⟨x⟩ := (inferInstance : Nonempty (Scheme.PinchedLine.lineGluing k))
    obtain ⟨y, hy⟩ := h ⟨x, rfl⟩
    exact leftComponent_ne_right k x y hy.symm
  · intro h
    obtain ⟨x⟩ := (inferInstance : Nonempty (Scheme.PinchedLine.lineGluing k))
    obtain ⟨y, hy⟩ := h ⟨x, rfl⟩
    exact leftComponent_ne_right k y x hy

theorem source_components_card : Nat.card (irreducibleComponents (normalized k)) = 2 := by
  change (irreducibleComponents (normalized k)).ncard = 2
  rw [source_components_eq]
  apply Set.ncard_pair
  intro h
  obtain ⟨x⟩ := (inferInstance : Nonempty (Scheme.PinchedLine.lineGluing k))
  have hx : leftComponent k x ∈ Set.range (rightComponent k) := h ▸ ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := hx
  exact leftComponent_ne_right k x y hy.symm

/-- Every stalk of the actual normalized source is normal, transferred along
the two actual open component embeddings. -/
theorem normalized_normal : NormalStalks (normalized k) := by
  intro z
  rcases source_components_cover k z with ⟨x, rfl⟩ | ⟨x, rfl⟩
  · exact normalityOfOpen (leftComponent k) x
      (Scheme.PinchedLine.lineGluing_normal k x)
  · exact normalityOfOpen (rightComponent k) x
      (Scheme.PinchedLine.lineGluing_normal k x)

end AlgebraicGeometry.Scheme.TwoGon
end
section
open CategoryTheory Limits AlgebraicGeometry Polynomial
open scoped Polynomial
namespace AlgebraicGeometry.Scheme.TwoGon.Affine
variable (k : Type u) [Field k]

/-- A polynomial prime viewed on the left affine normalization component. -/
def leftComponentPrime (p : PrimeSpectrum k[X]) : normalizationScheme k :=
  PrimeSpectrum.comap (RingHom.fst k[X] k[X]) p

/-- A polynomial prime viewed on the right affine normalization component. -/
def rightComponentPrime (p : PrimeSpectrum k[X]) : normalizationScheme k :=
  PrimeSpectrum.comap (RingHom.snd k[X] k[X]) p

/-- The two affine component images meet only at 0 and 1. -/
theorem affine_cross_image (p q : PrimeSpectrum k[X]) :
    normalizationMap k (leftComponentPrime k p) = normalizationMap k (rightComponentPrime k q) ↔
      (p = linePoint k 0 ∧ q = linePoint k 0) ∨
      (p = linePoint k 1 ∧ q = linePoint k 1) := by
  constructor
  · intro h
    have hz : conductorMul k (1, 0) ∈
        (normalizationMap k (rightComponentPrime k q)).asIdeal := by
      change (X * (X - 1) : k[X]) * 0 ∈ q.asIdeal
      simp
    rw [← h] at hz
    change (X * (X - 1) : k[X]) * 1 ∈ p.asIdeal at hz
    rw [mul_one] at hz
    have hp : p = linePoint k 0 ∨ p = linePoint k 1 := by
      rcases p.isPrime.mem_or_mem hz with hp | hp
      · exact Or.inl (linePoint_eq_of_mem k p 0 (by simpa using hp))
      · exact Or.inr (linePoint_eq_of_mem k p 1 (by simpa using hp))
    rcases hp with rfl | rfl
    · left
      refine ⟨rfl, ?_⟩
      have hx : diagonal k X ∈
          (normalizationMap k (rightComponentPrime k q)).asIdeal := by
        rw [← h]
        change eval 0 (X : k[X]) = 0
        simp
      change X ∈ q.asIdeal at hx
      exact linePoint_eq_of_mem k q 0 (by simpa using hx)
    · right
      refine ⟨rfl, ?_⟩
      have hx : diagonal k (X - 1) ∈
          (normalizationMap k (rightComponentPrime k q)).asIdeal := by
        rw [← h]
        change eval 1 (X - 1 : k[X]) = 0
        simp
      change X - 1 ∈ q.asIdeal at hx
      exact linePoint_eq_of_mem k q 1 (by simpa using hx)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact branches_same_image k 0 (Or.inl rfl)
    · exact branches_same_image k 1 (Or.inr rfl)

end AlgebraicGeometry.Scheme.TwoGon.Affine
end
section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits AlgebraicGeometry Polynomial
open scoped Polynomial TensorProduct
namespace AlgebraicGeometry.Scheme.TwoGon
open Affine
open Scheme.OpenPushout Scheme.Pullback.SpecProducts Localization.Away
variable (k : Type u) [Field k]

theorem leftComponent_affine :
    pushout.inl (Scheme.PinchedLine.normalizationOverlapInclusion k)
      (Scheme.PinchedLine.gluingToInfinity k) ≫
      leftComponent k = Spec.map (CommRingCat.ofHom (RingHom.fst k[X] k[X])) ≫
        pushout.inl (normalizationOverlapInclusion k) (gluingToInfinity k) := by
  apply (cancel_mono (normalizationLinesIso k).hom).mp
  simp only [Category.assoc]
  rw [normalizationLinesIso_affine]
  rw [← specProductIso_inl]
  simp only [leftComponent, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    coprod.inl_map, Category.comp_id]

theorem rightComponent_affine :
    pushout.inl (Scheme.PinchedLine.normalizationOverlapInclusion k)
      (Scheme.PinchedLine.gluingToInfinity k) ≫
      rightComponent k = Spec.map (CommRingCat.ofHom (RingHom.snd k[X] k[X])) ≫
        pushout.inl (normalizationOverlapInclusion k) (gluingToInfinity k) := by
  apply (cancel_mono (normalizationLinesIso k).hom).mp
  simp only [Category.assoc]
  rw [normalizationLinesIso_affine]
  rw [← specProductIso_inr]
  simp only [rightComponent, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    coprod.inr_map, Category.comp_id]

theorem leftComponent_infinity :
    pushout.inr (Scheme.PinchedLine.normalizationOverlapInclusion k)
      (Scheme.PinchedLine.gluingToInfinity k) ≫
      leftComponent k = Spec.map (CommRingCat.ofHom (RingHom.fst (V k) (V k))) ≫
        pushout.inr (normalizationOverlapInclusion k) (gluingToInfinity k) := by
  apply (cancel_mono (normalizationLinesIso k).hom).mp
  simp only [Category.assoc]
  rw [normalizationLinesIso_infinity]
  rw [← specProductIso_inl]
  simp only [leftComponent, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    coprod.inl_map, Category.comp_id]

theorem rightComponent_infinity :
    pushout.inr (Scheme.PinchedLine.normalizationOverlapInclusion k)
      (Scheme.PinchedLine.gluingToInfinity k) ≫
      rightComponent k = Spec.map (CommRingCat.ofHom (RingHom.snd (V k) (V k))) ≫
        pushout.inr (normalizationOverlapInclusion k) (gluingToInfinity k) := by
  apply (cancel_mono (normalizationLinesIso k).hom).mp
  simp only [Category.assoc]
  rw [normalizationLinesIso_infinity]
  rw [← specProductIso_inr]
  simp only [rightComponent, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    coprod.inr_map, Category.comp_id]

theorem leftPoint_on_leftComponent (a : k) :
    leftPoint k a ∈ Set.range (leftComponent k) := by
  refine ⟨Scheme.PinchedLine.gluedBranchPoint k a, ?_⟩
  exact congrArg (fun f : Spec (.of k[X]) ⟶ normalized k => f (Scheme.PinchedLine.branchPoint k a))
    (leftComponent_affine k)

theorem rightPoint_on_rightComponent (a : k) :
    rightPoint k a ∈ Set.range (rightComponent k) := by
  refine ⟨Scheme.PinchedLine.gluedBranchPoint k a, ?_⟩
  exact congrArg (fun f : Spec (.of k[X]) ⟶ normalized k => f (Scheme.PinchedLine.branchPoint k a))
    (rightComponent_affine k)

/-- Above the infinity open the global normalization has singleton fibres. -/
theorem normalization_infinity_fibre (y : infinityScheme k) (z : normalized k) :
    normalization k z = pushout.inr (gluingToNode k) (gluingToInfinity k) y ↔
      z = pushout.inr (normalizationOverlapInclusion k) (gluingToInfinity k) y := by
  constructor
  · intro h
    have hz : z ∈ (pushout.inr (normalizationOverlapInclusion k) (gluingToInfinity
      k)).opensRange := by
      rw [← Scheme.OpenNormalizationGluing.preimage_infinity (gluingToNode k)
        (gluingToInfinity k) (normalizationOverlapInclusion k) (normalizationMap k)
        (conductorOpenIso_over k).symm (conductor_preimage k)]
      exact ⟨y, h.symm⟩
    obtain ⟨y', rfl⟩ := hz
    apply congrArg (pushout.inr (normalizationOverlapInclusion k) (gluingToInfinity k))
    apply (pushout.inr (gluingToNode k) (gluingToInfinity k)).isOpenEmbedding.injective
    simpa only [← Scheme.Hom.comp_apply, normalization,
      Scheme.OpenNormalizationGluing.infinity_chart] using h
  · rintro rfl
    simp only [← Scheme.Hom.comp_apply, normalization,
      Scheme.OpenNormalizationGluing.infinity_chart]

/-- The image of the left normalization component in the two-gon. -/
def targetLeftComponent : Set (twoGon k) := normalization k '' Set.range (leftComponent k)
/-- The image of the right normalization component in the two-gon. -/
def targetRightComponent : Set (twoGon k) := normalization k '' Set.range (rightComponent k)

theorem targetLeft_isClosed : IsClosed (targetLeftComponent k) :=
  (normalization k).isClosedMap _ (leftComponent_isClosed k)
theorem targetRight_isClosed : IsClosed (targetRightComponent k) :=
  (normalization k).isClosedMap _ (rightComponent_isClosed k)

theorem targetLeft_irreducible : IsIrreducible (targetLeftComponent k) :=
  (leftComponent_irreducible k).image _ (normalization k).continuous.continuousOn
theorem targetRight_irreducible : IsIrreducible (targetRightComponent k) :=
  (rightComponent_irreducible k).image _ (normalization k).continuous.continuousOn

theorem target_components_cover : targetLeftComponent k ∪ targetRightComponent k = Set.univ := by
  ext z
  constructor
  · intro _; trivial
  · intro _
    obtain ⟨x, rfl⟩ := normalization_surjective k z
    rcases source_components_cover k x with hx | hx
    · exact Or.inl ⟨x, hx, rfl⟩
    · exact Or.inr ⟨x, hx, rfl⟩

theorem target_left_not_subset_right : ¬ targetLeftComponent k ⊆ targetRightComponent k := by
  intro h
  obtain ⟨y⟩ := (inferInstance : Nonempty (Spec (.of (V k))))
  let x := pushout.inr (Scheme.PinchedLine.normalizationOverlapInclusion k)
    (Scheme.PinchedLine.gluingToInfinity k) y
  have hx : leftComponent k x =
      pushout.inr (normalizationOverlapInclusion k) (gluingToInfinity k)
        (Spec.map (CommRingCat.ofHom (RingHom.fst (V k) (V k))) y) :=
    congrArg (fun f : Spec (.of (V k)) ⟶ normalized k => f y) (leftComponent_infinity k)
  obtain ⟨z, ⟨w, rfl⟩, hz⟩ := h ⟨leftComponent k x, ⟨x, rfl⟩, rfl⟩
  have he : rightComponent k w = leftComponent k x := by
    rw [hx]
    apply (normalization_infinity_fibre k _ _).mp
    rw [hz, hx]
    exact (normalization_infinity_fibre k _ _).mpr rfl
  exact leftComponent_ne_right k x w he.symm

theorem target_right_not_subset_left : ¬ targetRightComponent k ⊆ targetLeftComponent k := by
  intro h
  obtain ⟨y⟩ := (inferInstance : Nonempty (Spec (.of (V k))))
  let x := pushout.inr (Scheme.PinchedLine.normalizationOverlapInclusion k)
    (Scheme.PinchedLine.gluingToInfinity k) y
  have hx : rightComponent k x =
      pushout.inr (normalizationOverlapInclusion k) (gluingToInfinity k)
        (Spec.map (CommRingCat.ofHom (RingHom.snd (V k) (V k))) y) :=
    congrArg (fun f : Spec (.of (V k)) ⟶ normalized k => f y) (rightComponent_infinity k)
  obtain ⟨z, ⟨w, rfl⟩, hz⟩ := h ⟨rightComponent k x, ⟨x, rfl⟩, rfl⟩
  have he : leftComponent k w = rightComponent k x := by
    rw [hx]
    apply (normalization_infinity_fibre k _ _).mp
    rw [hz, hx]
    exact (normalization_infinity_fibre k _ _).mpr rfl
  exact leftComponent_ne_right k w x he

theorem target_components_eq : irreducibleComponents (twoGon k) =
    {targetLeftComponent k, targetRightComponent k} :=
  irreducibleComponents_eq_pair (targetLeft_isClosed k) (targetRight_isClosed k)
    (targetLeft_irreducible k) (targetRight_irreducible k) (target_components_cover k)
    (target_left_not_subset_right k) (target_right_not_subset_left k)

theorem target_components_card : Nat.card (irreducibleComponents (twoGon k)) = 2 :=
  irreducibleComponents_card_two (targetLeft_isClosed k) (targetRight_isClosed k)
    (targetLeft_irreducible k) (targetRight_irreducible k) (target_components_cover k)
    (target_left_not_subset_right k) (target_right_not_subset_left k)

end AlgebraicGeometry.Scheme.TwoGon
end
section
open CategoryTheory Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.TwoGon
open Affine
variable (k : Type u) [Field k]

/-- At either target intersection, exactly the left branch lies on the actual
left irreducible normalization component. -/
theorem left_component_fibre (a : k) (ha : a = 0 ∨ a = 1) (z : normalized k) :
    normalization k z = intersectionPoint k a ∧ z ∈ Set.range (leftComponent k) ↔
      z = leftPoint k a := by
  constructor
  · rintro ⟨hz, hm⟩
    rcases (normalization_fibre k a ha z).mp hz with h | rfl
    · exact h
    · obtain ⟨x, hx⟩ := hm
      obtain ⟨y, hy⟩ := rightPoint_on_rightComponent k a
      exact (leftComponent_ne_right k x y (hx.trans hy.symm)).elim
  · rintro rfl
    exact ⟨(normalization_fibre k a ha _).mpr (Or.inl rfl), leftPoint_on_leftComponent k a⟩

/-- At either target intersection, exactly the right branch lies on the actual
right irreducible normalization component. -/
theorem right_component_fibre (a : k) (ha : a = 0 ∨ a = 1) (z : normalized k) :
    normalization k z = intersectionPoint k a ∧ z ∈ Set.range (rightComponent k) ↔
      z = rightPoint k a := by
  constructor
  · rintro ⟨hz, hm⟩
    rcases (normalization_fibre k a ha z).mp hz with rfl | h
    · obtain ⟨y, hy⟩ := hm
      obtain ⟨x, hx⟩ := leftPoint_on_leftComponent k a
      exact (leftComponent_ne_right k x y (hx.trans hy.symm)).elim
    · exact h
  · rintro rfl
    exact ⟨(normalization_fibre k a ha _).mpr (Or.inr rfl), rightPoint_on_rightComponent k a⟩

end AlgebraicGeometry.Scheme.TwoGon
end
section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits AlgebraicGeometry Polynomial
open scoped Polynomial TensorProduct
namespace AlgebraicGeometry.Scheme.TwoGon
open Affine
open Scheme.OpenPushout Scheme.Pullback.SpecProducts Localization.Away
variable (k : Type u) [Field k]

theorem commonImage_not_infinity (x y : Scheme.PinchedLine.lineGluing k)
    (h : normalization k (leftComponent k x) = normalization k (rightComponent k y))
    (v : infinityScheme k) :
    normalization k (leftComponent k x) ≠ pushout.inr (gluingToNode k) (gluingToInfinity k) v := by
  intro hv
  have hl := (normalization_infinity_fibre k v (leftComponent k x)).mp hv
  have hr := (normalization_infinity_fibre k v (rightComponent k y)).mp (h.symm.trans hv)
  exact leftComponent_ne_right k x y (hl.trans hr.symm)

theorem commonImage_affine (x y : Scheme.PinchedLine.lineGluing k)
    (h : normalization k (leftComponent k x) = normalization k (rightComponent k y)) :
    (∃ p, pushout.inl (Scheme.PinchedLine.normalizationOverlapInclusion k)
      (Scheme.PinchedLine.gluingToInfinity k) p = x) ∧
    (∃ q, pushout.inl (Scheme.PinchedLine.normalizationOverlapInclusion k)
      (Scheme.PinchedLine.gluingToInfinity k) q = y) := by
  constructor
  · rcases Scheme.PinchedLine.lineGluing_covered k x with hx | ⟨v, rfl⟩
    · exact hx
    · have hv : leftComponent k (pushout.inr (Scheme.PinchedLine.normalizationOverlapInclusion k)
          (Scheme.PinchedLine.gluingToInfinity k) v) =
          pushout.inr (normalizationOverlapInclusion k) (gluingToInfinity k)
            (Spec.map (CommRingCat.ofHom (RingHom.fst (V k) (V k))) v) :=
        congrArg (fun f : Spec (.of (V k)) ⟶ normalized k => f v) (leftComponent_infinity k)
      exact (commonImage_not_infinity k _ _ h _
        ((normalization_infinity_fibre k _ _).mpr hv)).elim
  · rcases Scheme.PinchedLine.lineGluing_covered k y with hy | ⟨v, rfl⟩
    · exact hy
    · have hv : rightComponent k (pushout.inr (Scheme.PinchedLine.normalizationOverlapInclusion k)
          (Scheme.PinchedLine.gluingToInfinity k) v) =
          pushout.inr (normalizationOverlapInclusion k) (gluingToInfinity k)
            (Spec.map (CommRingCat.ofHom (RingHom.snd (V k) (V k))) v) :=
        congrArg (fun f : Spec (.of (V k)) ⟶ normalized k => f v) (rightComponent_infinity k)
      exact (commonImage_not_infinity k _ _ h _
        (h.trans ((normalization_infinity_fibre k _ _).mpr hv))).elim

theorem leftComponent_affine_image (p : PrimeSpectrum k[X]) :
    normalization k (leftComponent k
      (pushout.inl (Scheme.PinchedLine.normalizationOverlapInclusion k)
        (Scheme.PinchedLine.gluingToInfinity k) p)) =
    pushout.inl (gluingToNode k) (gluingToInfinity k)
      (normalizationMap k (leftComponentPrime k p)) := by
  have hp := congrArg (fun f : Spec (.of k[X]) ⟶ normalized k => f p) (leftComponent_affine k)
  simp only [Scheme.Hom.comp_apply] at hp
  rw [hp]
  exact congrArg (fun f : normalizationScheme k ⟶ twoGon k => f (leftComponentPrime k p))
    (Scheme.OpenNormalizationGluing.affine_chart (gluingToNode k) (gluingToInfinity k)
      (normalizationOverlapInclusion k) (normalizationMap k) (conductorOpenIso_over k).symm)

theorem rightComponent_affine_image (p : PrimeSpectrum k[X]) :
    normalization k (rightComponent k
      (pushout.inl (Scheme.PinchedLine.normalizationOverlapInclusion k)
        (Scheme.PinchedLine.gluingToInfinity k) p)) =
    pushout.inl (gluingToNode k) (gluingToInfinity k)
      (normalizationMap k (rightComponentPrime k p)) := by
  have hp := congrArg (fun f : Spec (.of k[X]) ⟶ normalized k => f p) (rightComponent_affine k)
  simp only [Scheme.Hom.comp_apply] at hp
  rw [hp]
  exact congrArg (fun f : normalizationScheme k ⟶ twoGon k => f (rightComponentPrime k p))
    (Scheme.OpenNormalizationGluing.affine_chart (gluingToNode k) (gluingToInfinity k)
      (normalizationOverlapInclusion k) (normalizationMap k) (conductorOpenIso_over k).symm)

theorem intersectionPoint_on_both (a : k) (ha : a = 0 ∨ a = 1) :
    intersectionPoint k a ∈ targetLeftComponent k ∩ targetRightComponent k := by
  constructor
  · exact ⟨leftPoint k a, leftPoint_on_leftComponent k a,
      (normalization_fibre k a ha _).mpr (Or.inl rfl)⟩
  · exact ⟨rightPoint k a, rightPoint_on_rightComponent k a,
      (normalization_fibre k a ha _).mpr (Or.inr rfl)⟩

/-- The two actual proper components intersect at precisely the two distinct
node points. No component-incidence certificate is assumed. -/
theorem target_components_intersection : targetLeftComponent k ∩ targetRightComponent k =
    {intersectionPoint k 0, intersectionPoint k 1} := by
  ext z
  constructor
  · rintro ⟨⟨_, ⟨x, rfl⟩, hx⟩, ⟨_, ⟨y, rfl⟩, hy⟩⟩
    have h := hx.trans hy.symm
    obtain ⟨⟨p, rfl⟩, ⟨q, rfl⟩⟩ := commonImage_affine k x y h
    have hpq : normalizationMap k (leftComponentPrime k p) =
        normalizationMap k (rightComponentPrime k q) := by
      apply (pushout.inl (gluingToNode k) (gluingToInfinity k)).isOpenEmbedding.injective
      exact (leftComponent_affine_image k p).symm.trans (h.trans (rightComponent_affine_image k q))
    rcases (affine_cross_image k p q).mp hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · left
      exact hx.symm.trans (leftComponent_affine_image k (linePoint k 0))
    · right
      exact hx.symm.trans (leftComponent_affine_image k (linePoint k 1))
  · rintro (rfl | rfl)
    · exact intersectionPoint_on_both k 0 (Or.inl rfl)
    · exact intersectionPoint_on_both k 1 (Or.inr rfl)

theorem target_components_intersection_card :
    (targetLeftComponent k ∩ targetRightComponent k).ncard = 2 := by
  rw [target_components_intersection, Set.ncard_pair (intersectionPoints_distinct k)]

end AlgebraicGeometry.Scheme.TwoGon
end
section
open CategoryTheory Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.TwoGon
open Affine
variable (k : Type u) [Field k]

theorem leftEndpoints_distinct : leftPoint k 0 ≠ leftPoint k 1 := by
  intro h
  have h0 := (normalization_fibre k 0 (Or.inl rfl) _).mpr (Or.inl (Eq.refl (leftPoint k 0)))
  have h1 := (normalization_fibre k 1 (Or.inr rfl) _).mpr (Or.inl (Eq.refl (leftPoint k 1)))
  exact intersectionPoints_distinct k (h0.symm.trans ((congrArg (normalization k) h).trans h1))

theorem rightEndpoints_distinct : rightPoint k 0 ≠ rightPoint k 1 := by
  intro h
  have h0 := (normalization_fibre k 0 (Or.inl rfl) _).mpr (Or.inr (Eq.refl (rightPoint k 0)))
  have h1 := (normalization_fibre k 1 (Or.inr rfl) _).mpr (Or.inr (Eq.refl (rightPoint k 1)))
  exact intersectionPoints_distinct k (h0.symm.trans ((congrArg (normalization k) h).trans h1))

/-- The actual branches on the left normalization component lying above the
intersection of target components are precisely its two distinct endpoints. -/
theorem left_branchSet :
    {z : normalized k | z ∈ Set.range (leftComponent k) ∧
      normalization k z ∈ targetLeftComponent k ∩ targetRightComponent k} =
      {leftPoint k 0, leftPoint k 1} := by
  rw [target_components_intersection]
  ext z
  change (z ∈ Set.range (leftComponent k) ∧
      (normalization k z = intersectionPoint k 0 ∨ normalization k z = intersectionPoint k 1)) ↔
      z = leftPoint k 0 ∨ z = leftPoint k 1
  constructor
  · rintro ⟨hz, h | h⟩
    · exact Or.inl ((left_component_fibre k 0 (Or.inl rfl) z).mp ⟨h, hz⟩)
    · exact Or.inr ((left_component_fibre k 1 (Or.inr rfl) z).mp ⟨h, hz⟩)
  · rintro (rfl | rfl)
    · have h := (left_component_fibre k 0 (Or.inl rfl) _).mpr rfl
      exact ⟨h.2, Or.inl h.1⟩
    · have h := (left_component_fibre k 1 (Or.inr rfl) _).mpr rfl
      exact ⟨h.2, Or.inr h.1⟩

theorem right_branchSet :
    {z : normalized k | z ∈ Set.range (rightComponent k) ∧
      normalization k z ∈ targetLeftComponent k ∩ targetRightComponent k} =
      {rightPoint k 0, rightPoint k 1} := by
  rw [target_components_intersection]
  ext z
  change (z ∈ Set.range (rightComponent k) ∧
      (normalization k z = intersectionPoint k 0 ∨ normalization k z = intersectionPoint k 1)) ↔
      z = rightPoint k 0 ∨ z = rightPoint k 1
  constructor
  · rintro ⟨hz, h | h⟩
    · exact Or.inl ((right_component_fibre k 0 (Or.inl rfl) z).mp ⟨h, hz⟩)
    · exact Or.inr ((right_component_fibre k 1 (Or.inr rfl) z).mp ⟨h, hz⟩)
  · rintro (rfl | rfl)
    · have h := (right_component_fibre k 0 (Or.inl rfl) _).mpr rfl
      exact ⟨h.2, Or.inl h.1⟩
    · have h := (right_component_fibre k 1 (Or.inr rfl) _).mpr rfl
      exact ⟨h.2, Or.inr h.1⟩

theorem left_branchSet_card :
    {z : normalized k | z ∈ Set.range (leftComponent k) ∧
      normalization k z ∈ targetLeftComponent k ∩ targetRightComponent k}.ncard = 2 := by
  rw [left_branchSet, Set.ncard_pair (leftEndpoints_distinct k)]

theorem right_branchSet_card :
    {z : normalized k | z ∈ Set.range (rightComponent k) ∧
      normalization k z ∈ targetLeftComponent k ∩ targetRightComponent k}.ncard = 2 := by
  rw [right_branchSet, Set.ncard_pair (rightEndpoints_distinct k)]

end AlgebraicGeometry.Scheme.TwoGon
end
section
open CategoryTheory Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.TwoGon
open Affine
variable (k : Type u) [Field k]

/-- The two-gon pinching algebra is reduced. -/
instance nodeRing_reduced : _root_.IsReduced (nodeRing k) :=
  isReduced_of_injective (nodeRing k).val Subtype.val_injective

/-- Reducedness is proved on the literal affine node and two infinity charts. -/
instance twoGon_reduced : IsReduced (twoGon k) := by
  let cover := Scheme.OpenNormalizationGluing.twoChartCover
    (gluingToNode k) (gluingToInfinity k)
  have : ∀ i, IsReduced (cover.X i) := by
    intro i
    cases i
    · change IsReduced (nodeScheme k)
      infer_instance
    · change IsReduced (infinityScheme k)
      infer_instance
  exact IsReduced.of_openCover (twoGon k) cover

/-- The two-gon is locally Noetherian. -/
instance twoGon_locallyNoetherian : IsLocallyNoetherian (twoGon k) :=
  LocallyOfFiniteType.isLocallyNoetherian (structureMap k)

end AlgebraicGeometry.Scheme.TwoGon
end
section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits AlgebraicGeometry Polynomial
open scoped Polynomial
namespace AlgebraicGeometry.Scheme.TwoGon
open Affine
variable (k : Type u) [Field k]

/-- Projection from the two-gon pinching algebra to the left polynomial component. -/
def leftProjection : nodeRing k →+* k[X] :=
  (RingHom.fst k[X] k[X]).comp (nodeRing k).val.toRingHom
/-- Projection from the two-gon pinching algebra to the right polynomial component. -/
def rightProjection : nodeRing k →+* k[X] :=
  (RingHom.snd k[X] k[X]).comp (nodeRing k).val.toRingHom

theorem leftProjection_surjective : Function.Surjective (leftProjection k) :=
  fun p => ⟨diagonal k p, rfl⟩
theorem rightProjection_surjective : Function.Surjective (rightProjection k) :=
  fun p => ⟨diagonal k p, rfl⟩

/-- The left affine component inclusion induced by polynomial projection. -/
def leftAffine : Spec (.of k[X]) ⟶ nodeScheme k := Spec.map (CommRingCat.ofHom (leftProjection k))
/-- The right affine component inclusion induced by polynomial projection. -/
def rightAffine : Spec (.of k[X]) ⟶ nodeScheme k := Spec.map (CommRingCat.ofHom (rightProjection k))
/-- The left affine component inclusion is a closed immersion. -/
instance leftAffine_closed : IsClosedImmersion (leftAffine k) :=
  IsClosedImmersion.spec_of_surjective _ (leftProjection_surjective k)
/-- The right affine component inclusion is a closed immersion. -/
instance rightAffine_closed : IsClosedImmersion (rightAffine k) :=
  IsClosedImmersion.spec_of_surjective _ (rightProjection_surjective k)

/-- The left component inclusion into the product infinity chart. -/
def leftInfinity : Spec (.of (V k)) ⟶ infinityScheme k :=
  Spec.map (CommRingCat.ofHom (RingHom.fst (V k) (V k)))
/-- The right component inclusion into the product infinity chart. -/
def rightInfinity : Spec (.of (V k)) ⟶ infinityScheme k :=
  Spec.map (CommRingCat.ofHom (RingHom.snd (V k) (V k)))
/-- The left infinity component inclusion is a closed immersion. -/
instance leftInfinity_closed : IsClosedImmersion (leftInfinity k) :=
  IsClosedImmersion.spec_of_surjective _ (fun p => ⟨(p, 0), rfl⟩)
/-- The right infinity component inclusion is a closed immersion. -/
instance rightInfinity_closed : IsClosedImmersion (rightInfinity k) :=
  IsClosedImmersion.spec_of_surjective _ (fun p => ⟨(0, p), rfl⟩)

/-- The left projective-line component mapped to the two-gon by normalization. -/
def leftTargetMap : Scheme.PinchedLine.lineGluing k ⟶ twoGon k := leftComponent k ≫ normalization k
/-- The right projective-line component mapped to the two-gon by normalization. -/
def rightTargetMap : Scheme.PinchedLine.lineGluing k ⟶ twoGon k := rightComponent k ≫
  normalization k

theorem leftTargetMap_affine :
    pushout.inl (Scheme.PinchedLine.normalizationOverlapInclusion k)
      (Scheme.PinchedLine.gluingToInfinity k) ≫
      leftTargetMap k = leftAffine k ≫ pushout.inl (gluingToNode k) (gluingToInfinity k) := by
  rw [leftTargetMap, ← Category.assoc, leftComponent_affine, Category.assoc]
  rw [show pushout.inl (normalizationOverlapInclusion k) (gluingToInfinity k) ≫ normalization k =
      normalizationMap k ≫ pushout.inl (gluingToNode k) (gluingToInfinity k) from
    Scheme.OpenNormalizationGluing.affine_chart _ _ _ _ _]
  rw [← Category.assoc]
  congr 1
  unfold normalizationMap leftAffine leftProjection
  rw [← Spec.map_comp]
  rfl

theorem rightTargetMap_affine :
    pushout.inl (Scheme.PinchedLine.normalizationOverlapInclusion k)
      (Scheme.PinchedLine.gluingToInfinity k) ≫
      rightTargetMap k = rightAffine k ≫ pushout.inl (gluingToNode k) (gluingToInfinity k) := by
  rw [rightTargetMap, ← Category.assoc, rightComponent_affine, Category.assoc]
  rw [show pushout.inl (normalizationOverlapInclusion k) (gluingToInfinity k) ≫ normalization k =
      normalizationMap k ≫ pushout.inl (gluingToNode k) (gluingToInfinity k) from
    Scheme.OpenNormalizationGluing.affine_chart _ _ _ _ _]
  rw [← Category.assoc]
  congr 1
  unfold normalizationMap rightAffine rightProjection
  rw [← Spec.map_comp]
  rfl

theorem leftTargetMap_infinity :
    pushout.inr (Scheme.PinchedLine.normalizationOverlapInclusion k)
      (Scheme.PinchedLine.gluingToInfinity k) ≫
      leftTargetMap k = leftInfinity k ≫ pushout.inr (gluingToNode k) (gluingToInfinity k) := by
  rw [leftTargetMap, ← Category.assoc, leftComponent_infinity, Category.assoc]
  exact congrArg (leftInfinity k ≫ ·) (Scheme.OpenNormalizationGluing.infinity_chart _ _ _ _ _)

theorem rightTargetMap_infinity :
    pushout.inr (Scheme.PinchedLine.normalizationOverlapInclusion k)
      (Scheme.PinchedLine.gluingToInfinity k) ≫
      rightTargetMap k = rightInfinity k ≫ pushout.inr (gluingToNode k) (gluingToInfinity k) := by
  rw [rightTargetMap, ← Category.assoc, rightComponent_infinity, Category.assoc]
  exact congrArg (rightInfinity k ≫ ·) (Scheme.OpenNormalizationGluing.infinity_chart _ _ _ _ _)

theorem componentTarget_surjectiveOnStalks
    (f : Scheme.PinchedLine.lineGluing k ⟶ twoGon k)
    (a : Spec (.of k[X]) ⟶ nodeScheme k) (v : Spec (.of (V k)) ⟶ infinityScheme k)
    [IsClosedImmersion a] [IsClosedImmersion v]
    (ha : pushout.inl (Scheme.PinchedLine.normalizationOverlapInclusion k)
      (Scheme.PinchedLine.gluingToInfinity k) ≫ f =
      a ≫ pushout.inl (gluingToNode k) (gluingToInfinity k))
    (hv : pushout.inr (Scheme.PinchedLine.normalizationOverlapInclusion k)
      (Scheme.PinchedLine.gluingToInfinity k) ≫ f =
      v ≫ pushout.inr (gluingToNode k) (gluingToInfinity k)) : SurjectiveOnStalks f := by
  apply IsZariskiLocalAtSource.of_openCover (P := @SurjectiveOnStalks)
    (Scheme.OpenNormalizationGluing.twoChartCover
      (Scheme.PinchedLine.normalizationOverlapInclusion k) (Scheme.PinchedLine.gluingToInfinity k))
  intro b
  cases b
  · change SurjectiveOnStalks
      (pushout.inl (Scheme.PinchedLine.normalizationOverlapInclusion k)
        (Scheme.PinchedLine.gluingToInfinity k) ≫ f)
    rw [ha]
    infer_instance
  · change SurjectiveOnStalks
      (pushout.inr (Scheme.PinchedLine.normalizationOverlapInclusion k)
        (Scheme.PinchedLine.gluingToInfinity k) ≫ f)
    rw [hv]
    infer_instance

/-- The left projective-line component map is surjective on stalks. -/
instance leftTargetMap_surjectiveOnStalks : SurjectiveOnStalks (leftTargetMap k) :=
  componentTarget_surjectiveOnStalks k _ _ _ (leftTargetMap_affine k) (leftTargetMap_infinity k)
/-- The right projective-line component map is surjective on stalks. -/
instance rightTargetMap_surjectiveOnStalks : SurjectiveOnStalks (rightTargetMap k) :=
  componentTarget_surjectiveOnStalks k _ _ _ (rightTargetMap_affine k) (rightTargetMap_infinity k)

theorem leftTargetMap_over : leftTargetMap k ≫ structureMap k =
  Scheme.PinchedLine.lineStructure k := by
  simp only [leftTargetMap, Category.assoc, normalization_over, normalizedStructure, leftComponent,
    Category.assoc, Iso.inv_hom_id_assoc, coprod.inl_desc]

theorem rightTargetMap_over : rightTargetMap k ≫ structureMap k =
  Scheme.PinchedLine.lineStructure k := by
  simp only [rightTargetMap, Category.assoc, normalization_over, normalizedStructure,
    rightComponent,
    Category.assoc, Iso.inv_hom_id_assoc, coprod.inr_desc]

/-- The left projective-line component map is proper. -/
instance leftTargetMap_proper : IsProper (leftTargetMap k) := by
  have : IsProper (leftTargetMap k ≫ structureMap k) := by
    rw [leftTargetMap_over]
    infer_instance
  exact IsProper.of_comp (leftTargetMap k) (structureMap k)
/-- The right projective-line component map is proper. -/
instance rightTargetMap_proper : IsProper (rightTargetMap k) := by
  have : IsProper (rightTargetMap k ≫ structureMap k) := by
    rw [rightTargetMap_over]
    infer_instance
  exact IsProper.of_comp (rightTargetMap k) (structureMap k)

/-- The only possible same-component collision is tested on the actual affine
quotient; all infinity fibres are singletons. -/
theorem componentTarget_injective
    (c : Scheme.PinchedLine.lineGluing k ⟶ normalized k) [IsOpenImmersion c]
    (a : Spec (.of k[X]) ⟶ nodeScheme k) [IsClosedImmersion a]
    (v : Spec (.of (V k)) ⟶ infinityScheme k)
    (ha : pushout.inl (Scheme.PinchedLine.normalizationOverlapInclusion k)
      (Scheme.PinchedLine.gluingToInfinity k) ≫
      (c ≫ normalization k) = a ≫ pushout.inl (gluingToNode k) (gluingToInfinity k))
    (hv : pushout.inr (Scheme.PinchedLine.normalizationOverlapInclusion k)
      (Scheme.PinchedLine.gluingToInfinity k) ≫ c =
      v ≫ pushout.inr (normalizationOverlapInclusion k) (gluingToInfinity k)) :
    Function.Injective (c ≫ normalization k) := by
  have infinity_case (x : Scheme.PinchedLine.lineGluing k) (y : Spec (.of (V k)))
      (h : normalization k (c x) = normalization k (c
        (pushout.inr (Scheme.PinchedLine.normalizationOverlapInclusion k)
          (Scheme.PinchedLine.gluingToInfinity k) y))) :
      x = pushout.inr (Scheme.PinchedLine.normalizationOverlapInclusion k)
        (Scheme.PinchedLine.gluingToInfinity k) y := by
    have hy := congrArg (fun f : Spec (.of (V k)) ⟶ normalized k => f y) hv
    simp only [Scheme.Hom.comp_apply] at hy
    apply c.isOpenEmbedding.injective
    rw [hy]
    apply (normalization_infinity_fibre k _ _).mp
    exact h.trans ((normalization_infinity_fibre k _ _).mpr hy)
  intro x y h
  change normalization k (c x) = normalization k (c y) at h
  rcases Scheme.PinchedLine.lineGluing_covered k x with ⟨p, rfl⟩ | ⟨p, rfl⟩
  · rcases Scheme.PinchedLine.lineGluing_covered k y with ⟨q, rfl⟩ | ⟨q, rfl⟩
    · have hp := congrArg (fun f : Spec (.of k[X]) ⟶ twoGon k => f p) ha
      have hq := congrArg (fun f : Spec (.of k[X]) ⟶ twoGon k => f q) ha
      simp only [Scheme.Hom.comp_apply] at hp hq
      have h' := (pushout.inl (gluingToNode k) (gluingToInfinity k)).isOpenEmbedding.injective
        (hp.symm.trans (h.trans hq))
      have hpq := a.isClosedEmbedding.injective h'
      exact congrArg _ hpq
    · exact infinity_case _ _ h
  · exact (infinity_case _ _ h.symm).symm

/-- The left projective-line component map is a closed immersion. -/
instance leftTargetMap_closedImmersion : IsClosedImmersion (leftTargetMap k) where
  toSurjectiveOnStalks := inferInstance
  isClosedEmbedding := Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (leftTargetMap k).continuous
    (componentTarget_injective k (leftComponent k) (leftAffine k) (leftInfinity k)
      (leftTargetMap_affine k) (leftComponent_infinity k)) (leftTargetMap k).isClosedMap

/-- The right projective-line component map is a closed immersion. -/
instance rightTargetMap_closedImmersion : IsClosedImmersion (rightTargetMap k) where
  toSurjectiveOnStalks := inferInstance
  isClosedEmbedding := Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (rightTargetMap k).continuous
    (componentTarget_injective k (rightComponent k) (rightAffine k) (rightInfinity k)
      (rightTargetMap_affine k) (rightComponent_infinity k)) (rightTargetMap k).isClosedMap

/-- The actual Proj projective lines occur as closed subschemes of the target. -/
def leftP1TargetMap : Scheme.ProjectiveLine.projectiveP1 k ⟶ twoGon k :=
  (Scheme.PinchedLine.ProjectiveComparison.lineIsoP1 k).inv ≫ leftTargetMap k
/-- The right component map parametrized by the native projective line. -/
def rightP1TargetMap : Scheme.ProjectiveLine.projectiveP1 k ⟶ twoGon k :=
  (Scheme.PinchedLine.ProjectiveComparison.lineIsoP1 k).inv ≫ rightTargetMap k
/-- The native projective-line parametrization of the left component is a closed immersion. -/
instance leftP1TargetMap_closed : IsClosedImmersion (leftP1TargetMap k) := by
  unfold leftP1TargetMap
  infer_instance
/-- The native projective-line parametrization of the right component is a closed immersion. -/
instance rightP1TargetMap_closed : IsClosedImmersion (rightP1TargetMap k) := by
  unfold rightP1TargetMap
  infer_instance

end AlgebraicGeometry.Scheme.TwoGon
end
section
open CategoryTheory Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.TwoGon
open Affine
variable (k : Type u) [Field k]

/-- Actual scheme-theoretic components, embedded as closed subschemes. -/
abbrev leftComponentScheme : Scheme.{u} := (leftTargetMap k).image
/-- The closed image scheme of the right projective-line component. -/
abbrev rightComponentScheme : Scheme.{u} := (rightTargetMap k).image

/-- The left closed component image identified with the native projective line. -/
def leftComponentSchemeIsoP1 : leftComponentScheme k ≅ Scheme.ProjectiveLine.projectiveP1 k :=
  (asIso (leftTargetMap k).toImage).symm ≪≫ Scheme.PinchedLine.ProjectiveComparison.lineIsoP1 k

/-- The right closed component image identified with the native projective line. -/
def rightComponentSchemeIsoP1 : rightComponentScheme k ≅ Scheme.ProjectiveLine.projectiveP1 k :=
  (asIso (rightTargetMap k).toImage).symm ≪≫ Scheme.PinchedLine.ProjectiveComparison.lineIsoP1 k

theorem leftTargetMap_range : Set.range (leftTargetMap k) = targetLeftComponent k := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨leftComponent k x, ⟨x, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩

theorem rightTargetMap_range : Set.range (rightTargetMap k) = targetRightComponent k := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨rightComponent k x, ⟨x, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩

theorem leftComponentScheme_range : Set.range (leftTargetMap k).imageι = targetLeftComponent k := by
  change Set.range (leftTargetMap k).ker.subschemeι = _
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.Hom.support_ker,
    (leftTargetMap k).isClosedEmbedding.isClosed_range.closure_eq, leftTargetMap_range]

theorem rightComponentScheme_range : Set.range (rightTargetMap k).imageι = targetRightComponent
  k := by
  change Set.range (rightTargetMap k).ker.subschemeι = _
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.Hom.support_ker,
    (rightTargetMap k).isClosedEmbedding.isClosed_range.closure_eq, rightTargetMap_range]

/-- The scheme-theoretic component images carry their reduced structure. -/
instance leftComponentScheme_reduced : IsReduced (leftComponentScheme k) :=
  isReduced_of_isOpenImmersion (asIso (leftTargetMap k).toImage).inv

/-- The right closed component image has a reduced scheme structure. -/
instance rightComponentScheme_reduced : IsReduced (rightComponentScheme k) :=
  isReduced_of_isOpenImmersion (asIso (rightTargetMap k).toImage).inv

theorem leftComponentScheme_normal : _root_.AlgebraicGeometry.Scheme.NormalStalks
  (leftComponentScheme k) :=
  normalityOfIso (asIso (leftTargetMap k).toImage).symm
    (Scheme.PinchedLine.lineGluing_normal k)

theorem rightComponentScheme_normal : _root_.AlgebraicGeometry.Scheme.NormalStalks
  (rightComponentScheme k) :=
  normalityOfIso (asIso (rightTargetMap k).toImage).symm
    (Scheme.PinchedLine.lineGluing_normal k)

end AlgebraicGeometry.Scheme.TwoGon
end
