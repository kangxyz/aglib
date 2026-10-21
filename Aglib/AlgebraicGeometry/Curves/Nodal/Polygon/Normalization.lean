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
public import Aglib.AlgebraicGeometry.Curves.Nodal.Polygon.Gluing
public import Aglib.Topology.Irreducible.ClosedCover

/-!
# The unmarked polygon curve: Normalization

Source: frozen R5 `Curves/Cyclic/Normalization.lean`, revision
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
/-! Actual irreducible component images of the cyclic gluing, including n=1. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits AlgebraicGeometry Polynomial Set
open scoped Polynomial
universe v
namespace AlgebraicGeometry.Scheme.Polygon

variable (k : Type u) [Field k] (n : ℕ)

@[reassoc] theorem componentLine_eq_sigma (i : Fin n) :
    componentLine k n i = Sigma.ι (fun _ : Fin n => Scheme.PinchedLine.lineGluing k) i ≫
      (normalizationLinesIso k n).inv := by
  simp [normalizationLinesIso, linesToNormalization]

/-- Each projective-line component is open in the disjoint normalization gluing. -/
instance componentLine_open (i : Fin n) : IsOpenImmersion (componentLine k n i) := by
  rw [componentLine_eq_sigma]
  infer_instance

@[reassoc, simp] theorem componentLine_toLines (i : Fin n) :
    componentLine k n i ≫ (normalizationLinesIso k n).hom =
      Sigma.ι (fun _ : Fin n => Scheme.PinchedLine.lineGluing k) i := by
  rw [componentLine_eq_sigma]
  simp

theorem componentLine_index_eq (i j : Fin n) (x y : Scheme.PinchedLine.lineGluing k)
    (h : componentLine k n i x = componentLine k n j y) : i = j := by
  have h' := congrArg (normalizationLinesIso k n).hom h
  simp only [← Scheme.Hom.comp_apply, componentLine_toLines] at h'
  exact congrArg Sigma.fst ((sigmaι_eq_iff _ _ _ _ _).mp h')

theorem sourceComponents_cover (z : normalizedScheme k n) :
    ∃ i x, componentLine k n i x = z := by
  obtain ⟨⟨i⟩, x, hx⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective
    (Discrete.functor (fun _ : Fin n => Scheme.PinchedLine.lineGluing k))
      ((normalizationLinesIso k n).hom z)
  change Sigma.ι (fun _ : Fin n => Scheme.PinchedLine.lineGluing k) i x =
    (normalizationLinesIso k n).hom z at hx
  refine ⟨i, x, (normalizationLinesIso k n).hom.isOpenEmbedding.injective ?_⟩
  simpa only [← Scheme.Hom.comp_apply, componentLine_toLines] using hx

theorem componentLine_range_closed (i : Fin n) : IsClosed (Set.range (componentLine k n i)) := by
  apply isOpen_compl_iff.mp
  have he : (Set.range (componentLine k n i))ᶜ =
      ⋃ (j : Fin n) (_ : j ≠ i), Set.range (componentLine k n j) := by
    ext z
    constructor
    · intro hz
      obtain ⟨j, x, rfl⟩ := sourceComponents_cover k n z
      refine Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨?_, ⟨x, rfl⟩⟩⟩
      intro e
      subst j
      exact hz ⟨x, rfl⟩
    · rintro hz ⟨x, hx⟩
      obtain ⟨j, hz⟩ := Set.mem_iUnion.mp hz
      obtain ⟨hji, y, hy⟩ := Set.mem_iUnion.mp hz
      exact hji (componentLine_index_eq k n j i y x (hy.trans hx.symm))
  rw [he]
  exact isOpen_iUnion fun j => isOpen_iUnion fun _ =>
    (componentLine k n j).isOpenEmbedding.isOpen_range

/-- The target component is an actual image, not an assigned vertex label.
For n=1 the map identifies two endpoints; no closed-immersion claim is made. -/
def targetComponent (i : Fin n) : Set (cycleScheme k n) :=
  gluedPolynomialCover k n '' Set.range (componentLine k n i)

theorem targetComponent_closed (i : Fin n) : IsClosed (targetComponent k n i) :=
  (gluedPolynomialCover k n).isClosedMap _ (componentLine_range_closed k n i)

theorem targetComponent_irreducible (i : Fin n) : IsIrreducible (targetComponent k n i) := by
  have hs : IsIrreducible (Set.range (componentLine k n i)) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (Scheme.PinchedLine.lineGluing k)).image _
        (componentLine k n i).continuous.continuousOn
  exact hs.image _ (gluedPolynomialCover k n).continuous.continuousOn

theorem targetComponents_cover (z : cycleScheme k n) : ∃ i, z ∈ targetComponent k n i := by
  obtain ⟨x, rfl⟩ := gluedPolynomialCover_surjective k n z
  obtain ⟨i, y, rfl⟩ := sourceComponents_cover k n x
  exact ⟨i, ⟨componentLine k n i y, ⟨y, rfl⟩, rfl⟩⟩

/-- The actual finite normal-source map is an isomorphism over the infinity
open; this is a fibre statement, not a global normalization assertion. -/
theorem gluedPolynomialCover_infinity_fibre (y : infinityScheme k n) (z : normalizedScheme k n) :
    gluedPolynomialCover k n z = pushout.inr (gluingToNode k n) (gluingToInfinity k n) y ↔
      z = pushout.inr (normalizationOverlapInclusion k n) (gluingToInfinity k n) y := by
  constructor
  · intro h
    have hz : z ∈ (pushout.inr (normalizationOverlapInclusion k n) (gluingToInfinity k
      n)).opensRange := by
      rw [← Scheme.OpenNormalizationGluing.preimage_infinity (gluingToNode k n)
        (gluingToInfinity k n) (normalizationOverlapInclusion k n) (polynomialCover k n)
        (conductorOpenIso_over k n).symm (conductor_preimage k n)]
      exact ⟨y, h.symm⟩
    obtain ⟨y', rfl⟩ := hz
    apply congrArg (pushout.inr (normalizationOverlapInclusion k n) (gluingToInfinity k n))
    apply (pushout.inr (gluingToNode k n) (gluingToInfinity k n)).isOpenEmbedding.injective
    simpa only [← Scheme.Hom.comp_apply, gluedPolynomialCover,
      Scheme.OpenNormalizationGluing.infinity_chart] using h
  · rintro rfl
    simp only [← Scheme.Hom.comp_apply, gluedPolynomialCover,
      Scheme.OpenNormalizationGluing.infinity_chart]

theorem targetComponent_subset_index (i j : Fin n)
    (h : targetComponent k n i ⊆ targetComponent k n j) : i = j := by
  obtain ⟨y⟩ := (inferInstance : Nonempty (Spec (.of (V k))))
  let x := pushout.inr (Scheme.PinchedLine.normalizationOverlapInclusion k)
    (Scheme.PinchedLine.gluingToInfinity k) y
  have hx : componentLine k n i x =
      pushout.inr (normalizationOverlapInclusion k n) (gluingToInfinity k n)
        (componentInfinity k n i y) :=
    congrArg (fun f : Spec (.of (V k)) ⟶ normalizedScheme k n => f y)
      (componentLine_infinity k n i)
  obtain ⟨z, ⟨w, rfl⟩, hz⟩ := h ⟨componentLine k n i x, ⟨x, rfl⟩, rfl⟩
  have he : componentLine k n j w = componentLine k n i x := by
    rw [hx]
    apply (gluedPolynomialCover_infinity_fibre k n _ _).mp
    rw [hz, hx]
    exact (gluedPolynomialCover_infinity_fibre k n _ _).mpr rfl
  exact componentLine_index_eq k n i j x w he.symm

theorem targetComponent_inventory : irreducibleComponents (cycleScheme k n) =
    Set.range (targetComponent k n) :=
  irreducibleComponents_eq_range (targetComponent k n) (targetComponent_closed k n)
    (targetComponent_irreducible k n) (targetComponents_cover k n)
      (targetComponent_subset_index k n)

/-- The component labels are identified with actual maximal irreducible sets. -/
def componentEquiv : Fin n ≃ irreducibleComponents (cycleScheme k n) :=
  Equiv.ofBijective
    (fun i => ⟨targetComponent k n i, by rw [targetComponent_inventory]; exact ⟨i, rfl⟩⟩)
    ⟨by
      intro i j h
      exact targetComponent_subset_index k n i j (congrArg Subtype.val h).subset,
     by
      rintro ⟨C, hC⟩
      rw [targetComponent_inventory] at hC
      obtain ⟨i, rfl⟩ := hC
      exact ⟨i, rfl⟩⟩

/-- Actual component cardinality is a theorem derived from the constructed
maps and image geometry, including the self-node case n=1. -/
theorem irreducibleComponents_card : Nat.card (irreducibleComponents (cycleScheme k n)) = n := by
  rw [← Nat.card_congr (componentEquiv k n)]
  simp

end AlgebraicGeometry.Scheme.Polygon
end -- noncomputable section
end
section
/-! Actual conductor quotient, node points and two endpoint branches. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits AlgebraicGeometry Polynomial Set
open scoped Polynomial
namespace AlgebraicGeometry.Scheme.Polygon
variable (k : Type u) [Field k] (n : ℕ)

/-- The actual ideal of functions vanishing on all cyclic endpoint pairs. -/
def nodeConductorIdeal : Ideal (nodeRing k n) := RingHom.ker (nodeEvaluation k n).toRingHom

/-- This ideal is precisely the conductor of the actual normalization inclusion. -/
theorem mem_nodeConductorIdeal_iff (a : nodeRing k n) :
    a ∈ nodeConductorIdeal k n ↔
      ∀ p : NormalizationRing k n, (a : NormalizationRing k n) * p ∈ nodeRing k n := by
  constructor
  · intro ha p
    change nodeEvaluation k n a = 0 at ha
    rw [mem_nodeRing]
    intro i
    have hi := congrFun ha i
    change ((a : NormalizationRing k n) i).eval 1 = 0 at hi
    change (((a : NormalizationRing k n) i) * p i).eval 1 =
      (((a : NormalizationRing k n) (finRotate n i)) * p (finRotate n i)).eval 0
    rw [eval_mul, eval_mul, ← (mem_nodeRing k n a).mp a.property i, hi, zero_mul, zero_mul]
  · intro h
    have hx := (mem_nodeRing k n _).mp (h (fun _ => X))
    change nodeEvaluation k n a = 0
    funext i
    have hi := hx i
    change ((a : NormalizationRing k n) i).eval 1 = 0
    simpa only [Pi.mul_apply, eval_mul, eval_X, mul_one, mul_zero] using hi

/-- The node scheme's actual conductor quotient is the product of n copies of k. -/
def nodeConductorQuotientEquiv : (nodeRing k n ⧸ nodeConductorIdeal k n) ≃+* NodeValues k n :=
  RingHom.quotientKerEquivOfSurjective (nodeEvaluation_surjective k n)

/-- The residue homomorphism of the polygon node with label `i`. -/
def nodeValue (i : Fin n) : nodeRing k n →+* k :=
  (Pi.evalRingHom _ i).comp (nodeEvaluation k n).toRingHom

theorem nodeValue_surjective (i : Fin n) : Function.Surjective (nodeValue k n i) := by
  intro c
  obtain ⟨a, ha⟩ := nodeEvaluation_surjective k n (fun _ => c)
  exact ⟨a, congrFun ha i⟩

/-- An actual prime ideal coming from a coordinate of the conductor quotient. -/
def nodePoint (i : Fin n) : nodeScheme k n :=
  ⟨RingHom.ker (nodeValue k n i),
    (RingHom.ker_isMaximal_of_surjective (nodeValue k n i) (nodeValue_surjective k n i)).isPrime⟩

theorem nodePoint_injective : Function.Injective (nodePoint k n) := by
  classical
  intro i j h
  by_contra hij
  obtain ⟨a, ha⟩ := nodeEvaluation_surjective k n (Pi.single i 1)
  have hj : a ∈ (nodePoint k n j).asIdeal := by
    change nodeEvaluation k n a j = 0
    rw [ha, Pi.single_eq_of_ne (Ne.symm hij)]
  have hi : a ∈ (nodePoint k n i).asIdeal := by rw [h]; exact hj
  change nodeEvaluation k n a i = 0 at hi
  rw [ha, Pi.single_eq_same] at hi
  exact one_ne_zero hi

/-- Actual polynomial-component endpoint prime. -/
def affineBranch (i : Fin n) (a : k) : Spec (.of (NormalizationRing k n)) :=
  PrimeSpectrum.sigmaToPi (fun _ : Fin n => k[X]) ⟨i, Scheme.PinchedLine.branchPoint k a⟩

@[simp] theorem affineBranch_one_map (i : Fin n) :
    polynomialCover k n (affineBranch k n i 1) = nodePoint k n i := by
  apply PrimeSpectrum.ext
  ext a
  rfl

theorem affineBranch_zero_map (i : Fin n) :
    polynomialCover k n (affineBranch k n (finRotate n i) 0) = nodePoint k n i := by
  apply PrimeSpectrum.ext
  ext a
  change ((a : NormalizationRing k n) (finRotate n i)).eval 0 = 0 ↔
    ((a : NormalizationRing k n) i).eval 1 = 0
  rw [← (mem_nodeRing k n a).mp a.property i]

theorem nodePoint_conductor (i : Fin n) : conductor k n ∈ (nodePoint k n i).asIdeal := by
  change (X * (X - 1) : k[X]).eval 1 = 0
  simp

/-- Every actual prime in the conductor locus is one of the quotient's n points. -/
theorem nodePoint_exhaustive (p : nodeScheme k n) (hp : conductor k n ∈ p.asIdeal) :
    ∃ i, nodePoint k n i = p := by
  obtain ⟨q, rfl⟩ := polynomialCover_surjective k n p
  obtain ⟨⟨i, q⟩, rfl⟩ := (PrimeSpectrum.sigmaToPi_bijective
    (fun _ : Fin n => k[X])).surjective q
  change (X * (X - 1) : k[X]) ∈ q.asIdeal at hp
  rcases Scheme.PinchedLine.branchPoint_conductor k q hp with hq | hq
  · subst q
    refine ⟨(finRotate n).symm i, ?_⟩
    simpa only [Equiv.apply_symm_apply, affineBranch] using (affineBranch_zero_map k n
      ((finRotate n).symm i)).symm
  · subst q
    exact ⟨i, (affineBranch_one_map k n i).symm⟩

/-- The node labels identified with the affine points whose prime ideal contains the conductor. -/
def nodePointEquiv : Fin n ≃ {p : nodeScheme k n // conductor k n ∈ p.asIdeal} :=
  Equiv.ofBijective (fun i => ⟨nodePoint k n i, nodePoint_conductor k n i⟩)
    ⟨fun _ _ h => nodePoint_injective k n (congrArg Subtype.val h), by
      rintro ⟨p, hp⟩
      obtain ⟨i, rfl⟩ := nodePoint_exhaustive k n p hp
      exact ⟨i, rfl⟩⟩

theorem nodePoint_card : Nat.card {p : nodeScheme k n // conductor k n ∈ p.asIdeal} = n := by
  rw [← Nat.card_congr (nodePointEquiv k n)]
  simp

/-- Actual glued node points in the global cyclic curve. -/
def gluedNodePoint (i : Fin n) : cycleScheme k n :=
  pushout.inl (gluingToNode k n) (gluingToInfinity k n) (nodePoint k n i)

theorem gluedNodePoint_injective : Function.Injective (gluedNodePoint k n) :=
  (pushout.inl (gluingToNode k n) (gluingToInfinity k n)).isOpenEmbedding.injective.comp
    (nodePoint_injective k n)

/-- Actual endpoint points in the finite normal-source scheme. -/
def gluedBranch (i : Fin n) (a : k) : normalizedScheme k n :=
  pushout.inl (normalizationOverlapInclusion k n) (gluingToInfinity k n) (affineBranch k n i a)

@[simp] theorem gluedBranch_one_map (i : Fin n) :
    gluedPolynomialCover k n (gluedBranch k n i 1) = gluedNodePoint k n i := by
  change (pushout.inl (normalizationOverlapInclusion k n) (gluingToInfinity k n) ≫
    gluedPolynomialCover k n) (affineBranch k n i 1) = _
  rw [gluedPolynomialCover, Scheme.OpenNormalizationGluing.affine_chart]
  change pushout.inl (gluingToNode k n) (gluingToInfinity k n)
    (polynomialCover k n (affineBranch k n i 1)) = _
  rw [affineBranch_one_map]
  rfl

theorem gluedBranch_zero_map (i : Fin n) :
    gluedPolynomialCover k n (gluedBranch k n (finRotate n i) 0) = gluedNodePoint k n i := by
  change (pushout.inl (normalizationOverlapInclusion k n) (gluingToInfinity k n) ≫
    gluedPolynomialCover k n) (affineBranch k n (finRotate n i) 0) = _
  rw [gluedPolynomialCover, Scheme.OpenNormalizationGluing.affine_chart]
  change pushout.inl (gluingToNode k n) (gluingToInfinity k n)
    (polynomialCover k n (affineBranch k n (finRotate n i) 0)) = _
  rw [affineBranch_zero_map]
  rfl

end AlgebraicGeometry.Scheme.Polygon
end -- noncomputable section
end
section
/-! Exhaustive actual two-branch fibres and cyclic component incidence. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits AlgebraicGeometry Polynomial Set
open scoped Polynomial
namespace AlgebraicGeometry.Scheme.Polygon
variable (k : Type u) [Field k] (n : ℕ)

/-- Distinct actual endpoint primes, even when both endpoints lie on one component. -/
theorem affineBranches_distinct (i : Fin n) :
    affineBranch k n i 1 ≠ affineBranch k n (finRotate n i) 0 := by
  intro h
  have h' := PrimeSpectrum.sigmaToPi_injective (fun _ : Fin n => k[X]) h
  exact Scheme.PinchedLine.branchPoint_distinct k
    (congrArg (fun z : Σ _ : Fin n, PrimeSpectrum k[X] => z.2) h').symm

/-- The complete actual affine fibre consists of the two cyclic endpoints. -/
theorem affineBranch_fibre (i : Fin n) (q : Spec (.of (NormalizationRing k n))) :
    polynomialCover k n q = nodePoint k n i ↔
      q = affineBranch k n i 1 ∨ q = affineBranch k n (finRotate n i) 0 := by
  constructor
  · intro h
    have hc : conductor k n ∈ (polynomialCover k n q).asIdeal := by
      rw [h]
      exact nodePoint_conductor k n i
    obtain ⟨⟨j, p⟩, rfl⟩ := (PrimeSpectrum.sigmaToPi_bijective
      (fun _ : Fin n => k[X])).surjective q
    change (X * (X - 1) : k[X]) ∈ p.asIdeal at hc
    rcases Scheme.PinchedLine.branchPoint_conductor k p hc with hp | hp
    · subst p
      have he : nodePoint k n ((finRotate n).symm j) = nodePoint k n i := by
        calc
          _ = polynomialCover k n (affineBranch k n j 0) := by
            simpa only [Equiv.apply_symm_apply] using
              (affineBranch_zero_map k n ((finRotate n).symm j)).symm
          _ = _ := h
      have hij := nodePoint_injective k n he
      have hj : j = finRotate n i := by
        simpa only [Equiv.apply_symm_apply] using congrArg (finRotate n) hij
      subst j
      exact Or.inr rfl
    · subst p
      have he : nodePoint k n j = nodePoint k n i := (affineBranch_one_map k n j).symm.trans h
      have hj := nodePoint_injective k n he
      subst j
      exact Or.inl rfl
  · rintro (rfl | rfl)
    · exact affineBranch_one_map k n i
    · exact affineBranch_zero_map k n i

theorem gluedBranches_distinct (i : Fin n) :
    gluedBranch k n i 1 ≠ gluedBranch k n (finRotate n i) 0 := by
  intro h
  exact affineBranches_distinct k n i
    ((pushout.inl (normalizationOverlapInclusion k n)
      (gluingToInfinity k n)).isOpenEmbedding.injective h)

/-- Every point of the global fibre is one of the two actual affine branches;
no additional point enters from the reciprocal infinity chart. -/
theorem gluedBranch_fibre (i : Fin n) (z : normalizedScheme k n) :
    gluedPolynomialCover k n z = gluedNodePoint k n i ↔
      z = gluedBranch k n i 1 ∨ z = gluedBranch k n (finRotate n i) 0 := by
  constructor
  · intro h
    have hz : z ∈ (pushout.inl (normalizationOverlapInclusion k n) (gluingToInfinity k
      n)).opensRange := by
      rw [← Scheme.OpenNormalizationGluing.preimage_affine (gluingToNode k n)
        (gluingToInfinity k n) (normalizationOverlapInclusion k n) (polynomialCover k n)
        (conductorOpenIso_over k n).symm]
      exact ⟨nodePoint k n i, h.symm⟩
    obtain ⟨q, rfl⟩ := hz
    have hq : polynomialCover k n q = nodePoint k n i := by
      apply (pushout.inl (gluingToNode k n) (gluingToInfinity k n)).isOpenEmbedding.injective
      simpa only [← Scheme.Hom.comp_apply, gluedPolynomialCover,
        Scheme.OpenNormalizationGluing.affine_chart, gluedNodePoint] using h
    rcases (affineBranch_fibre k n i q).mp hq with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact gluedBranch_one_map k n i
    · exact gluedBranch_zero_map k n i

/-- Exact cardinality of each actual fibre, proved from its two distinct points. -/
theorem gluedBranch_fibre_card (i : Fin n) :
    Nat.card {z : normalizedScheme k n // gluedPolynomialCover k n z = gluedNodePoint k n i} =
      2 := by
  change ({z : normalizedScheme k n | gluedPolynomialCover k n z = gluedNodePoint k n i} : Set
    _).ncard = 2
  have he : {z : normalizedScheme k n | gluedPolynomialCover k n z = gluedNodePoint k n i} =
      {gluedBranch k n i 1, gluedBranch k n (finRotate n i) 0} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, gluedBranch_fibre]
  rw [he, Set.ncard_pair (gluedBranches_distinct k n i)]

/-- The actual component affine chart takes its usual endpoint to the branch. -/
theorem gluedBranch_on_component (i : Fin n) (a : k) :
    componentLine k n i (Scheme.PinchedLine.gluedBranchPoint k a) = gluedBranch k n i a := by
  have h := congrArg (fun f : Spec (.of k[X]) ⟶ normalizedScheme k n =>
    f (Scheme.PinchedLine.branchPoint k a)) (componentLine_affine k n i)
  exact h

/-- The two branches lie on components i and i+1 respectively, with the
self-incidence retained when n=1. -/
theorem cyclic_branch_incidence (i : Fin n) :
    gluedBranch k n i 1 ∈ Set.range (componentLine k n i) ∧
      gluedBranch k n (finRotate n i) 0 ∈ Set.range (componentLine k n (finRotate n i)) :=
  ⟨⟨Scheme.PinchedLine.gluedBranchPoint k 1, gluedBranch_on_component k n i 1⟩,
   ⟨Scheme.PinchedLine.gluedBranchPoint k 0, gluedBranch_on_component k n (finRotate n i) 0⟩⟩

/-- The component membership of each actual node is exactly cyclic adjacency. -/
theorem gluedNodePoint_on_component_iff (i j : Fin n) :
    gluedNodePoint k n i ∈ targetComponent k n j ↔ j = i ∨ j = finRotate n i := by
  constructor
  · rintro ⟨z, ⟨x, rfl⟩, hx⟩
    rcases (gluedBranch_fibre k n i (componentLine k n j x)).mp hx with h | h
    · exact Or.inl (componentLine_index_eq k n j i x (Scheme.PinchedLine.gluedBranchPoint k 1)
        (h.trans (gluedBranch_on_component k n i 1).symm))
    · exact Or.inr (componentLine_index_eq k n j (finRotate n i) x
      (Scheme.PinchedLine.gluedBranchPoint k 0)
        (h.trans (gluedBranch_on_component k n (finRotate n i) 0).symm))
  · intro h
    rcases h with h | h
    · subst j
      exact ⟨gluedBranch k n i 1, (cyclic_branch_incidence k n i).1, gluedBranch_one_map k n i⟩
    · subst j
      exact ⟨gluedBranch k n (finRotate n i) 0, (cyclic_branch_incidence k n i).2,
        gluedBranch_zero_map k n i⟩

/-- The locus of the labeled nodes in the glued polygon curve. -/
def globalNodeLocus : Set (cycleScheme k n) := Set.range (gluedNodePoint k n)

/-- The labels enumerate precisely the actual affine conductor image. -/
theorem globalNodeLocus_eq_conductorImage : globalNodeLocus k n =
    pushout.inl (gluingToNode k n) (gluingToInfinity k n) ''
      {p : nodeScheme k n | conductor k n ∈ p.asIdeal} := by
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨nodePoint k n i, nodePoint_conductor k n i, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨i, rfl⟩ := nodePoint_exhaustive k n p hp
    exact ⟨i, rfl⟩

/-- This cardinality concerns the actual conductor-labelled point set, without
claiming a global nodality or singular-locus classification theorem. -/
theorem globalNodeLocus_card : (globalNodeLocus k n).ncard = n := by
  rw [globalNodeLocus, Set.ncard_range_of_injective (gluedNodePoint_injective k n)]
  simp

/-- The two endpoint points on any one normalized component are distinct. -/
theorem gluedBranch_zero_ne_one (i : Fin n) : gluedBranch k n i 0 ≠ gluedBranch k n i 1 := by
  intro h
  have h' := (pushout.inl (normalizationOverlapInclusion k n)
    (gluingToInfinity k n)).isOpenEmbedding.injective h
  have h'' := PrimeSpectrum.sigmaToPi_injective (fun _ : Fin n => k[X]) h'
  exact Scheme.PinchedLine.branchPoint_distinct k
    (congrArg (fun z : Σ _ : Fin n, PrimeSpectrum k[X] => z.2) h'')

/-- Branches are actual source points on a component above the conductor image. -/
def componentBoundaryBranches (i : Fin n) : Set (normalizedScheme k n) :=
  {z | z ∈ Set.range (componentLine k n i) ∧ gluedPolynomialCover k n z ∈ globalNodeLocus k n}

theorem componentBoundaryBranches_eq (i : Fin n) : componentBoundaryBranches k n i =
    {gluedBranch k n i 0, gluedBranch k n i 1} := by
  ext z
  constructor
  · rintro ⟨⟨x, rfl⟩, ⟨j, hj⟩⟩
    rcases (gluedBranch_fibre k n j (componentLine k n i x)).mp hj.symm with h | h
    · have e : i = j := componentLine_index_eq k n i j x (Scheme.PinchedLine.gluedBranchPoint k 1)
        (h.trans (gluedBranch_on_component k n j 1).symm)
      subst j
      exact Or.inr h
    · have e : i = finRotate n j := componentLine_index_eq k n i (finRotate n j) x
        (Scheme.PinchedLine.gluedBranchPoint k 0) (h.trans (gluedBranch_on_component k n
          (finRotate n j) 0).symm)
      exact Or.inl (by simpa only [← e] using h)
  · rintro (rfl | rfl)
    · refine ⟨⟨Scheme.PinchedLine.gluedBranchPoint k 0, gluedBranch_on_component k n i 0⟩,
        (finRotate n).symm i, ?_⟩
      simpa only [Equiv.apply_symm_apply] using (gluedBranch_zero_map k n ((finRotate n).symm
        i)).symm
    · exact ⟨⟨Scheme.PinchedLine.gluedBranchPoint k 1, gluedBranch_on_component k n i 1⟩,
        i, (gluedBranch_one_map k n i).symm⟩

/-- Actual branch degree two is derived on every normalized component. -/
theorem componentBoundaryBranches_card (i : Fin n) : (componentBoundaryBranches k n i).ncard =
  2 := by
  rw [componentBoundaryBranches_eq, Set.ncard_pair (gluedBranch_zero_ne_one k n i)]

end AlgebraicGeometry.Scheme.Polygon
end -- noncomputable section
end
