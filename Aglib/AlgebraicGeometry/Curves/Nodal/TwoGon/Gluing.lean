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
public import Aglib.AlgebraicGeometry.Curves.Nodal.TwoGon.Affine
public import Aglib.AlgebraicGeometry.Curves.Nodal.Projective
public import Aglib.AlgebraicGeometry.Gluing.Coproduct
public import Aglib.AlgebraicGeometry.Limits.SpecProducts
public import Aglib.RingTheory.Localization.Away.Products

/-!
# The literal two-component pinched curve: Gluing

Source: frozen R5 `Curves/Cyclic/TwoGon/Gluing.lean`, revision
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
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits AlgebraicGeometry Polynomial
open scoped Polynomial
namespace AlgebraicGeometry.Scheme.TwoGon
open Affine
open Scheme.OpenPushout Scheme.Pullback.SpecProducts Localization.Away
variable (k : Type u) [Field k]
/-- The conductor overlap ring of a single polynomial normalization component. -/
abbrev W := Polynomial.PinchedPair.ConductorReciprocal.W k
/-- The infinity chart ring of a single normalization component. -/
abbrev V := Polynomial.PinchedPair.infinityChartRing k
/-- The product conductor overlap ring of the two normalization components. -/
abbrev productOverlapRing := W k × W k
/-- The product infinity chart ring of the two normalization components. -/
abbrev productInfinityRing := V k × V k
/-- The common overlap scheme for the two-gon gluing. -/
abbrev overlapScheme : Scheme.{u} := Spec (.of (productOverlapRing k))
/-- The product infinity chart scheme for the two-gon gluing. -/
abbrev infinityScheme : Scheme.{u} := Spec (.of (productInfinityRing k))

/-- Concrete product localization for the two normalization components. -/
def productOverlapEquiv : normalizationOverlapRing k ≃ₐ[NormalizationRing k] productOverlapRing k :=
  Localization.Away.productLocalizationEquiv k[X] (W k)
    (Polynomial.PinchedPair.ConductorReciprocal.q k)

/-- The product overlap ring is the conductor localization of the polynomial normalization. -/
instance productOverlap_isLocalization :
    IsLocalization.Away (conductor k : NormalizationRing k) (productOverlapRing k) := by
  change IsLocalization.Away (Polynomial.PinchedPair.ConductorReciprocal.q k,
    Polynomial.PinchedPair.ConductorReciprocal.q k) (W k × W k)
  infer_instance

/-- The conductor localization of the pinched algebra equals the two overlap rings. -/
def nodeProductOverlapEquiv : nodeOverlapRing k ≃+* productOverlapRing k :=
  (conductorLocalizationEquiv k).trans (productOverlapEquiv k).toRingEquiv

@[simp] theorem nodeProductOverlapEquiv_algebraMap (a : nodeRing k) :
    nodeProductOverlapEquiv k (algebraMap (nodeRing k) (nodeOverlapRing k) a) =
      algebraMap (NormalizationRing k) (productOverlapRing k) a := by
  change productOverlapEquiv k (localizationComparison k
    (algebraMap (nodeRing k) (nodeOverlapRing k) a)) = _
  rw [show localizationComparison k (algebraMap (nodeRing k) (nodeOverlapRing k) a) =
      algebraMap (NormalizationRing k) (normalizationOverlapRing k) a from
    IsLocalization.map_eq (M := Submonoid.powers (conductor k))
      (S := nodeOverlapRing k) (T := Submonoid.powers (conductor k : NormalizationRing k))
      (Q := normalizationOverlapRing k) (g := (nodeRing k).val.toRingHom)
      (by rintro _ ⟨n, rfl⟩; exact ⟨n, by simp⟩) a]
  exact (productOverlapEquiv k).commutes a

/-- The conductor localization mapped into the two-gon node scheme. -/
def nodeOverlapInclusion : Spec (.of (nodeOverlapRing k)) ⟶ nodeScheme k :=
  Spec.map (CommRingCat.ofHom (algebraMap (nodeRing k) (nodeOverlapRing k)))
/-- The conductor localization is open in the two-gon node scheme. -/
instance nodeOverlapInclusion_open : IsOpenImmersion (nodeOverlapInclusion k) :=
  IsOpenImmersion.of_isLocalization (conductor k)

/-- The product conductor overlap mapped into the affine normalization scheme. -/
def normalizationOverlapInclusion : overlapScheme k ⟶ normalizationScheme k :=
  Spec.map (CommRingCat.ofHom (algebraMap (NormalizationRing k) (productOverlapRing k)))
/-- The product conductor overlap is open in the affine normalization scheme. -/
instance normalizationOverlapInclusion_open : IsOpenImmersion (normalizationOverlapInclusion k) :=
  IsOpenImmersion.of_isLocalization (conductor k : NormalizationRing k)

/-- The product overlap scheme identified with the conductor open of the two-gon node scheme. -/
def conductorOpenIso : overlapScheme k ≅ Spec (.of (nodeOverlapRing k)) :=
  Scheme.Spec.mapIso (nodeProductOverlapEquiv k).toCommRingCatIso.op

/-- The product conductor overlap mapped to the two-gon node chart. -/
def gluingToNode : overlapScheme k ⟶ nodeScheme k :=
  (conductorOpenIso k).hom ≫ nodeOverlapInclusion k
/-- The gluing map to the two-gon node chart is an open immersion. -/
instance gluingToNode_open : IsOpenImmersion (gluingToNode k) := by
  unfold gluingToNode
  infer_instance

theorem conductorOpenIso_over : gluingToNode k =
    normalizationOverlapInclusion k ≫ normalizationMap k := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact nodeProductOverlapEquiv_algebraMap k a

/-- Separate reciprocal infinity charts, one for each actual component. -/
def gluingToInfinity : overlapScheme k ⟶ infinityScheme k :=
  (specProductIso (W k) (W k)).hom ≫
    coprod.map (Scheme.PinchedLine.gluingToInfinity k) (Scheme.PinchedLine.gluingToInfinity k) ≫
      (specProductIso (V k) (V k)).inv
/-- The reciprocal gluing map to the product infinity chart is an open immersion. -/
instance gluingToInfinity_open : IsOpenImmersion (gluingToInfinity k) := by
  unfold gluingToInfinity
  infer_instance

/-- The two-gon obtained by gluing the pinched affine chart to the two infinity charts. -/
abbrev twoGon : Scheme.{u} := pushout (gluingToNode k) (gluingToInfinity k)
/-- The normalization obtained by gluing the two polynomial charts to their infinity charts. -/
abbrev normalized : Scheme.{u} :=
  pushout (normalizationOverlapInclusion k) (gluingToInfinity k)

/-- The affine normalization map extended across both infinity charts by gluing. -/
def normalization : normalized k ⟶ twoGon k :=
  Scheme.OpenNormalizationGluing.normalizationMap (gluingToNode k) (gluingToInfinity k)
    (normalizationOverlapInclusion k) (normalizationMap k) (conductorOpenIso_over k).symm

theorem conductor_preimage : normalizationMap k ⁻¹ᵁ (gluingToNode k).opensRange =
    (normalizationOverlapInclusion k).opensRange := by
  change normalizationMap k ⁻¹ᵁ
    ((conductorOpenIso k).hom ≫ nodeOverlapInclusion k).opensRange = _
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  have hn : (nodeOverlapInclusion k).opensRange = PrimeSpectrum.basicOpen (conductor k) :=
    Scheme.Hom.opensRange_localizationAway (R := .of (nodeRing k)) (conductor k)
  have ha : (normalizationOverlapInclusion k).opensRange =
      PrimeSpectrum.basicOpen (conductor k : NormalizationRing k) := by
    rw [SetLike.ext'_iff]
    exact PrimeSpectrum.localization_away_comap_range (productOverlapRing k)
      (conductor k : NormalizationRing k)
  rw [hn, ha]
  ext p
  rfl

/-- The normalization map of the glued two-gon is finite. -/
instance normalization_finite : IsFinite (normalization k) := by
  let := normalizationMap_finite k
  exact Scheme.OpenNormalizationGluing.normalizationMap_finite
    (gluingToNode k) (gluingToInfinity k) (normalizationOverlapInclusion k)
    (normalizationMap k) (conductorOpenIso_over k).symm (conductor_preimage k)

theorem normalization_surjective : Function.Surjective (normalization k) :=
  Scheme.OpenNormalizationGluing.normalizationMap_surjective
    (gluingToNode k) (gluingToInfinity k) (normalizationOverlapInclusion k)
    (normalizationMap k) (conductorOpenIso_over k).symm (normalizationMap_surjective k)

/-- The normalization map of the glued two-gon is surjective. -/
instance normalization_surjective_instance : Surjective (normalization k) :=
  ⟨normalization_surjective k⟩

theorem normalization_affine_isPullback :
    IsPullback (normalizationMap k)
      (pushout.inl (normalizationOverlapInclusion k) (gluingToInfinity k))
      (pushout.inl (gluingToNode k) (gluingToInfinity k)) (normalization k) :=
  Scheme.OpenNormalizationGluing.affine_isPullback
    (gluingToNode k) (gluingToInfinity k) (normalizationOverlapInclusion k)
    (normalizationMap k) (conductorOpenIso_over k).symm

theorem normalization_infinity_isPullback :
    IsPullback (𝟙 (infinityScheme k))
      (pushout.inr (normalizationOverlapInclusion k) (gluingToInfinity k))
      (pushout.inr (gluingToNode k) (gluingToInfinity k)) (normalization k) :=
  Scheme.OpenNormalizationGluing.infinity_isPullback
    (gluingToNode k) (gluingToInfinity k) (normalizationOverlapInclusion k)
    (normalizationMap k) (conductorOpenIso_over k).symm (conductor_preimage k)

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

/-- The left affine branch with coordinate `a`, viewed in the normalization gluing. -/
def leftPoint (a : k) : normalized k :=
  pushout.inl (normalizationOverlapInclusion k) (gluingToInfinity k) (leftBranch k a)
/-- The right affine branch with coordinate `a`, viewed in the normalization gluing. -/
def rightPoint (a : k) : normalized k :=
  pushout.inl (normalizationOverlapInclusion k) (gluingToInfinity k) (rightBranch k a)
/-- The image in the glued two-gon of the left affine evaluation point with coordinate `a`. -/
def intersectionPoint (a : k) : twoGon k :=
  pushout.inl (gluingToNode k) (gluingToInfinity k) (nodePoint k a)

theorem intersectionPoints_distinct : intersectionPoint k 0 ≠ intersectionPoint k 1 := by
  intro h
  exact nodePoints_distinct k ((pushout.inl (gluingToNode k)
    (gluingToInfinity k)).isOpenEmbedding.injective h)

theorem branchPoints_distinct (a b : k) : leftPoint k a ≠ rightPoint k b := by
  intro h
  exact branches_distinct k a b ((pushout.inl (normalizationOverlapInclusion k)
    (gluingToInfinity k)).isOpenEmbedding.injective h)

theorem nodePoint_not_on_overlap (a : k) (ha : a = 0 ∨ a = 1) (w : overlapScheme k) :
    gluingToNode k w ≠ nodePoint k a := by
  intro h
  have hw : nodePoint k a ∈ (gluingToNode k).opensRange := ⟨w, h⟩
  have hn : (gluingToNode k).opensRange = PrimeSpectrum.basicOpen (conductor k) := by
    change ((conductorOpenIso k).hom ≫ nodeOverlapInclusion k).opensRange = _
    rw [Scheme.Hom.opensRange_comp_of_isIso]
    exact Scheme.Hom.opensRange_localizationAway (R := .of (nodeRing k)) (conductor k)
  rw [hn] at hw
  apply hw
  change eval a (X * (X - 1) : k[X]) = 0
  rcases ha with rfl | rfl <;> simp

/-- Each of the two distinct global intersection fibres contains exactly its
left and right branch. The infinity charts add no hidden points to a fibre. -/
theorem normalization_fibre (a : k) (ha : a = 0 ∨ a = 1) (z : normalized k) :
    normalization k z = intersectionPoint k a ↔ z = leftPoint k a ∨ z = rightPoint k a := by
  have hh := Scheme.OpenNormalizationGluing.normalization_fibre
    (gluingToNode k) (gluingToInfinity k) (normalizationOverlapInclusion k)
    (normalizationMap k) (conductorOpenIso_over k).symm
    (nodePoint k a) (nodePoint_not_on_overlap k a ha) z
  change normalization k z = intersectionPoint k a ↔
      ∃ x, normalizationMap k x = nodePoint k a ∧
        pushout.inl (normalizationOverlapInclusion k) (gluingToInfinity k) x = z at hh
  rw [hh]
  simp only [affine_normalization_fibre k a ha]
  constructor
  · rintro ⟨x, hx, hxz⟩
    rcases hx with rfl | rfl
    · exact Or.inl hxz.symm
    · exact Or.inr hxz.symm
  · rintro (rfl | rfl)
    · exact ⟨leftBranch k a, Or.inl rfl, rfl⟩
    · exact ⟨rightBranch k a, Or.inr rfl, rfl⟩

theorem normalization_fibre_card (a : k) (ha : a = 0 ∨ a = 1) :
    Nat.card {z : normalized k // normalization k z = intersectionPoint k a} = 2 := by
  change ({z : normalized k | normalization k z = intersectionPoint k a} : Set _).ncard = 2
  have he : {z : normalized k | normalization k z = intersectionPoint k a} =
      {leftPoint k a, rightPoint k a} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
      normalization_fibre k a ha]
  rw [he, Set.ncard_pair (branchPoints_distinct k a a)]

end AlgebraicGeometry.Scheme.TwoGon
end
section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits AlgebraicGeometry Polynomial
open scoped Polynomial
namespace AlgebraicGeometry.Scheme.TwoGon
open Affine
open Scheme.OpenPushout Scheme.Pullback.SpecProducts Localization.Away
variable (k : Type u) [Field k]

theorem normalizationOverlap_coprod : normalizationOverlapInclusion k ≫
    (specProductIso k[X] k[X]).hom =
    (specProductIso (W k) (W k)).hom ≫
      coprod.map (Scheme.PinchedLine.normalizationOverlapInclusion k)
        (Scheme.PinchedLine.normalizationOverlapInclusion k) :=
  specProductIso_naturality (algebraMap k[X] (W k))

/-- The normalization gluing rewritten as the pushout of the two coproduct chart maps. -/
def normalizationCoprodChartsIso : normalized k ≅
    pushout (coprod.map (Scheme.PinchedLine.normalizationOverlapInclusion k)
        (Scheme.PinchedLine.normalizationOverlapInclusion k))
      (coprod.map (Scheme.PinchedLine.gluingToInfinity k) (Scheme.PinchedLine.gluingToInfinity
        k)) :=
  asIso (pushout.map (normalizationOverlapInclusion k) (gluingToInfinity k)
    (coprod.map (Scheme.PinchedLine.normalizationOverlapInclusion k)
      (Scheme.PinchedLine.normalizationOverlapInclusion k))
    (coprod.map (Scheme.PinchedLine.gluingToInfinity k) (Scheme.PinchedLine.gluingToInfinity k))
    (specProductIso k[X] k[X]).hom (specProductIso (V k) (V k)).hom
    (specProductIso (W k) (W k)).hom (normalizationOverlap_coprod k) (by
      simp [gluingToInfinity, Category.assoc]))

/-- The normalization is the actual disjoint union of the two reciprocal
projective-line gluings. -/
def normalizationLinesIso : normalized k ≅ (Scheme.PinchedLine.lineGluing k ⨿
  Scheme.PinchedLine.lineGluing k) :=
  normalizationCoprodChartsIso k ≪≫
    doublePushoutIso (Scheme.PinchedLine.normalizationOverlapInclusion k)
      (Scheme.PinchedLine.gluingToInfinity k)

/-- Canonical identification with two actual Proj projective lines. -/
def normalizationP1Iso : normalized k ≅
    (Scheme.ProjectiveLine.projectiveP1 k ⨿ Scheme.ProjectiveLine.projectiveP1 k) :=
  normalizationLinesIso k ≪≫ coprod.mapIso (Scheme.PinchedLine.ProjectiveComparison.lineIsoP1 k)
    (Scheme.PinchedLine.ProjectiveComparison.lineIsoP1 k)

/-- The canonical k-structure, expressed through the two projective lines. -/
def normalizedStructure : normalized k ⟶ Spec (.of k) :=
  (normalizationLinesIso k).hom ≫ coprod.desc (Scheme.PinchedLine.lineStructure k)
    (Scheme.PinchedLine.lineStructure k)

/-- The normalization gluing is proper over `k`. -/
instance normalizedStructure_proper : IsProper (normalizedStructure k) := by
  have := coprodDesc_proper (Scheme.PinchedLine.lineStructure k)
  unfold normalizedStructure
  infer_instance

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

/-- The restriction from the two-gon pinching algebra to the product conductor overlap ring. -/
def affineOverlapRingMap : nodeRing k →ₐ[k] productOverlapRing k :=
  ((IsScalarTower.toAlgHom k k[X] (W k)).prodMap
    (IsScalarTower.toAlgHom k k[X] (W k))).comp (nodeRing k).val

/-- The restrictions from the two infinity chart rings to their reciprocal overlap rings. -/
def infinityOverlapRingMap : productInfinityRing k →ₐ[k] productOverlapRing k :=
  (Polynomial.PinchedPair.infinityOverlapRingMap k).prodMap
    (Polynomial.PinchedPair.infinityOverlapRingMap k)

/-- The overlap algebra map from the tensor product of the affine and infinity chart rings. -/
def overlapTensorMap : nodeRing k ⊗[k] productInfinityRing k →ₐ[k] productOverlapRing k :=
  Algebra.TensorProduct.lift (affineOverlapRingMap k) (infinityOverlapRingMap k)
    (fun _ _ => Commute.all _ _)

/-- Diagonal pinched polynomials embed in the literal two-node coordinate ring. -/
def diagonalNodeMap : Polynomial.PinchedPair.nodeRing k →ₐ[k] nodeRing k where
  toFun p := diagonal k p
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- The tensor-product map induced by diagonal pinched polynomials and diagonal infinity
functions. -/
def diagonalTensorMap : Polynomial.PinchedPair.nodeRing k ⊗[k] V k →ₐ[k]
    nodeRing k ⊗[k] productInfinityRing k :=
  Algebra.TensorProduct.map (diagonalNodeMap k) ((AlgHom.id k (V k)).prod (AlgHom.id k (V k)))

theorem overlapTensorMap_diagonal (z : Polynomial.PinchedPair.nodeRing k ⊗[k] V k) :
    overlapTensorMap k (diagonalTensorMap k z) =
      (Polynomial.PinchedPair.overlapTensorMap k z, Polynomial.PinchedPair.overlapTensorMap k
        z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a b => rfl
  | add z w hz hw => simpa only [map_add, Prod.mk_add_mk] using congrArg₂ (· + ·) hz hw

theorem diagonal_mem (w : W k) : (w, w) ∈ (overlapTensorMap k).range := by
  obtain ⟨z, rfl⟩ := Polynomial.PinchedPair.overlapTensorMap_surjective k w
  exact ⟨diagonalTensorMap k z, overlapTensorMap_diagonal k z⟩

theorem infinity_mem (v : productInfinityRing k) :
    infinityOverlapRingMap k v ∈ (overlapTensorMap k).range :=
  ⟨1 ⊗ₜ[k] v, by simp [overlapTensorMap]⟩

/-- Component idempotents from the two separate infinity charts split every
pair of overlap functions. The actual overlap tensor map is surjective. -/
theorem overlapTensorMap_surjective : Function.Surjective (overlapTensorMap k) := by
  rintro ⟨x, y⟩
  change (x, y) ∈ (overlapTensorMap k).range
  have hl : ((1, 0) : productOverlapRing k) ∈ (overlapTensorMap k).range := by
    have h := infinity_mem k (1, 0)
    change ((Polynomial.PinchedPair.infinityOverlapRingMap k) 1,
      (Polynomial.PinchedPair.infinityOverlapRingMap k) 0) ∈ _ at h
    simpa only [map_one, map_zero] using h
  have hr : ((0, 1) : productOverlapRing k) ∈ (overlapTensorMap k).range := by
    have h := infinity_mem k (0, 1)
    change ((Polynomial.PinchedPair.infinityOverlapRingMap k) 0,
      (Polynomial.PinchedPair.infinityOverlapRingMap k) 1) ∈ _ at h
    simpa only [map_one, map_zero] using h
  have h := (overlapTensorMap k).range.add_mem
    ((overlapTensorMap k).range.mul_mem (diagonal_mem k x) hl)
    ((overlapTensorMap k).range.mul_mem (diagonal_mem k y) hr)
  simpa using h

theorem gluingToNode_spec : gluingToNode k =
    Spec.map (CommRingCat.ofHom (affineOverlapRingMap k).toRingHom) := by
  rw [conductorOpenIso_over]
  unfold normalizationOverlapInclusion normalizationMap affineOverlapRingMap
  rw [← Spec.map_comp]
  rfl

theorem gluingToInfinity_spec : gluingToInfinity k =
    Spec.map (CommRingCat.ofHom (infinityOverlapRingMap k).toRingHom) := by
  unfold gluingToInfinity infinityOverlapRingMap
  rw [Scheme.PinchedLine.gluingToInfinity_spec]
  rw [← Category.assoc, ← specProductIso_naturality]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rfl

theorem gluingToNode_over : gluingToNode k ≫ Spec.algebraMap k (nodeRing k) =
    Spec.algebraMap k (productOverlapRing k) := by
  rw [gluingToNode_spec]
  exact Spec.map_algHom_algebraMap (affineOverlapRingMap k)

theorem gluingToInfinity_over : gluingToInfinity k ≫
    Spec.algebraMap k (productInfinityRing k) =
    Spec.algebraMap k (productOverlapRing k) := by
  rw [gluingToInfinity_spec]
  exact Spec.map_algHom_algebraMap (infinityOverlapRingMap k)

/-- The field structure map obtained by gluing the two-gon chart maps. -/
def structureMap : twoGon k ⟶ Spec (.of k) :=
  pushout.desc (Spec.algebraMap k (nodeRing k))
    (Spec.algebraMap k (productInfinityRing k))
    ((gluingToNode_over k).trans (gluingToInfinity_over k).symm)

/-- The common overlap mapped into the product over `k` of the two-gon charts. -/
def overlapToProduct : overlapScheme k ⟶
    pullback (Spec.algebraMap k (nodeRing k))
      (Spec.algebraMap k (productInfinityRing k)) :=
  pullback.lift (gluingToNode k) (gluingToInfinity k)
    ((gluingToNode_over k).trans (gluingToInfinity_over k).symm)

theorem overlapToProduct_eq : overlapToProduct k =
    Spec.map (CommRingCat.ofHom (R := nodeRing k ⊗[k] productInfinityRing k)
      (S := productOverlapRing k) (overlapTensorMap k).toRingHom) ≫
      (pullbackSpecIso k (nodeRing k) (productInfinityRing k)).inv := by
  apply pullback.hom_ext
  · erw [overlapToProduct, pullback.lift_fst, Category.assoc, pullbackSpecIso_inv_fst,
      gluingToNode_spec, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    simp [overlapTensorMap]
  · erw [overlapToProduct, pullback.lift_snd, Category.assoc, pullbackSpecIso_inv_snd,
      gluingToInfinity_spec, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    simp [overlapTensorMap]

/-- The common overlap is a closed subscheme of the product over `k` of the two-gon charts. -/
instance overlapToProduct_closedImmersion : IsClosedImmersion (overlapToProduct k) := by
  rw [overlapToProduct_eq]
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (R := nodeRing k ⊗[k]
    productInfinityRing k)
      (S := productOverlapRing k) (overlapTensorMap k).toRingHom)) :=
    IsClosedImmersion.spec_of_surjective _ (overlapTensorMap_surjective k)
  exact IsClosedImmersion.comp _ _

/-- The glued two-gon is separated over `k`. -/
instance structureMap_separated : IsSeparated (structureMap k) := by
  have : IsSeparated (Spec.algebraMap k (nodeRing k)) := by
    unfold Spec.algebraMap
    infer_instance
  have : IsSeparated (Spec.algebraMap k (productInfinityRing k)) := by
    unfold Spec.algebraMap
    infer_instance
  have : IsClosedImmersion (pullback.lift (gluingToNode k) (gluingToInfinity k)
      ((gluingToNode_over k).trans (gluingToInfinity_over k).symm)) :=
    overlapToProduct_closedImmersion k
  exact Scheme.SeparatedGluing.separated_desc (gluingToNode k) (gluingToInfinity k)
    (Spec.algebraMap k (nodeRing k))
    (Spec.algebraMap k (productInfinityRing k))
    ((gluingToNode_over k).trans (gluingToInfinity_over k).symm)

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

theorem normalizationLinesIso_affine :
    pushout.inl (normalizationOverlapInclusion k) (gluingToInfinity k) ≫
      (normalizationLinesIso k).hom = (specProductIso k[X] k[X]).hom ≫
        coprod.map (pushout.inl (Scheme.PinchedLine.normalizationOverlapInclusion k)
          (Scheme.PinchedLine.gluingToInfinity k))
          (pushout.inl (Scheme.PinchedLine.normalizationOverlapInclusion k)
            (Scheme.PinchedLine.gluingToInfinity k)) := by
  simp [normalizationLinesIso, normalizationCoprodChartsIso, doublePushoutIso,
    doublePushoutHom, Category.assoc]

theorem normalizationLinesIso_infinity :
    pushout.inr (normalizationOverlapInclusion k) (gluingToInfinity k) ≫
      (normalizationLinesIso k).hom = (specProductIso (V k) (V k)).hom ≫
        coprod.map (pushout.inr (Scheme.PinchedLine.normalizationOverlapInclusion k)
          (Scheme.PinchedLine.gluingToInfinity k))
          (pushout.inr (Scheme.PinchedLine.normalizationOverlapInclusion k)
            (Scheme.PinchedLine.gluingToInfinity k)) := by
  simp [normalizationLinesIso, normalizationCoprodChartsIso, doublePushoutIso,
    doublePushoutHom, Category.assoc]

theorem normalizedStructure_affine :
    pushout.inl (normalizationOverlapInclusion k) (gluingToInfinity k) ≫ normalizedStructure k =
      Spec.algebraMap k (NormalizationRing k) := by
  rw [normalizedStructure, ← Category.assoc, normalizationLinesIso_affine, Category.assoc]
  have he : coprod.map
      (pushout.inl (Scheme.PinchedLine.normalizationOverlapInclusion k)
        (Scheme.PinchedLine.gluingToInfinity k))
      (pushout.inl (Scheme.PinchedLine.normalizationOverlapInclusion k)
        (Scheme.PinchedLine.gluingToInfinity k)) ≫
      coprod.desc (Scheme.PinchedLine.lineStructure k) (Scheme.PinchedLine.lineStructure k) =
      coprod.desc (Spec.algebraMap k k[X]) (Spec.algebraMap k k[X]) := by
    apply coprod.hom_ext <;>
      simp [Scheme.PinchedLine.lineStructure]
  rw [he]
  exact specProductIso_over k k[X]

theorem normalizedStructure_infinity :
    pushout.inr (normalizationOverlapInclusion k) (gluingToInfinity k) ≫ normalizedStructure k =
      Spec.algebraMap k (productInfinityRing k) := by
  rw [normalizedStructure, ← Category.assoc, normalizationLinesIso_infinity, Category.assoc]
  have he : coprod.map
      (pushout.inr (Scheme.PinchedLine.normalizationOverlapInclusion k)
        (Scheme.PinchedLine.gluingToInfinity k))
      (pushout.inr (Scheme.PinchedLine.normalizationOverlapInclusion k)
        (Scheme.PinchedLine.gluingToInfinity k)) ≫
      coprod.desc (Scheme.PinchedLine.lineStructure k) (Scheme.PinchedLine.lineStructure k) =
      coprod.desc (Spec.algebraMap k (V k)) (Spec.algebraMap k (V k)) := by
    apply coprod.hom_ext <;>
      simp [Scheme.PinchedLine.lineStructure]
  rw [he]
  exact specProductIso_over k (V k)

theorem normalization_over : normalization k ≫ structureMap k = normalizedStructure k := by
  apply pushout.hom_ext
  · rw [← Category.assoc]
    rw [show pushout.inl (normalizationOverlapInclusion k) (gluingToInfinity k) ≫ normalization k =
      normalizationMap k ≫ pushout.inl (gluingToNode k) (gluingToInfinity k) from
      Scheme.OpenNormalizationGluing.affine_chart _ _ _ _ _]
    rw [Category.assoc, structureMap, pushout.inl_desc, normalizedStructure_affine]
    exact Spec.map_algHom_algebraMap (nodeRing k).val
  · rw [← Category.assoc]
    rw [show pushout.inr (normalizationOverlapInclusion k) (gluingToInfinity k) ≫ normalization k =
      pushout.inr (gluingToNode k) (gluingToInfinity k) from
      Scheme.OpenNormalizationGluing.infinity_chart _ _ _ _ _]
    rw [structureMap, pushout.inr_desc, normalizedStructure_infinity]

/-- The glued two-gon is locally of finite type over `k`. -/
instance structureMap_finiteType : LocallyOfFiniteType (structureMap k) := by
  apply IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFiniteType)
    (Scheme.OpenNormalizationGluing.twoChartCover (gluingToNode k) (gluingToInfinity k))
  intro b
  cases b
  · change LocallyOfFiniteType
      (pushout.inl (gluingToNode k) (gluingToInfinity k) ≫ structureMap k)
    rw [structureMap, pushout.inl_desc]
    infer_instance
  · change LocallyOfFiniteType
      (pushout.inr (gluingToNode k) (gluingToInfinity k) ≫ structureMap k)
    rw [structureMap, pushout.inr_desc]
    infer_instance

/-- Properness of the literal two-gon follows from its finite surjective
normalization by two actual projective lines and proved separation. -/
instance structureMap_proper : IsProper (structureMap k) := by
  have : IsProper (normalization k ≫ structureMap k) := by
    rw [normalization_over]
    infer_instance
  exact Scheme.OpenNormalizationGluing.proper_of_surjective_proper_source
    (normalization k) (structureMap k)

end AlgebraicGeometry.Scheme.TwoGon
end
