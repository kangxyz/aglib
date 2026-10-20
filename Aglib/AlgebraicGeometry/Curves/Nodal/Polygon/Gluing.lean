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
public import Aglib.AlgebraicGeometry.Curves.Nodal.Polygon.Affine
public import Aglib.AlgebraicGeometry.Curves.Nodal.Projective
public import Aglib.AlgebraicGeometry.Limits.SpecProducts
public import Aglib.RingTheory.Localization.Away.Products

/-!
# The unmarked polygon curve: Gluing

Source: frozen R5 `Curves/Cyclic/Gluing.lean`, revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`.
The actual ring maps, gluing arrows and component indices are retained.
This leaf does not construct a marked model or assume a model-existence theorem.
-/

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Polynomial
open Scheme.Pullback.OpenIntersection Localization.Away
open scoped Polynomial
universe u

section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits AlgebraicGeometry Polynomial
open scoped Polynomial
namespace AlgebraicGeometry.Scheme.Polygon
variable (k : Type u) [Field k] (n : ℕ)

/-- The spectrum of the cyclic pinching algebra. -/
abbrev nodeScheme : Scheme.{u} := Spec (.of (nodeRing k n))

theorem nodeScheme_connected [NeZero n] : ConnectedSpace (nodeScheme k n) :=
  spectrum_connected k n

/-- The actual finite polynomial-product cover of the cyclic affine scheme.
A universal normalization characterization is a further, separate statement. -/
def polynomialCover : Spec (.of (NormalizationRing k n)) ⟶ nodeScheme k n :=
  Spec.map (CommRingCat.ofHom (algebraMap (nodeRing k n) (NormalizationRing k n)))

/-- The affine polynomial normalization cover is finite. -/
instance polynomialCover_finite : IsFinite (polynomialCover k n) := by
  apply (IsFinite.SpecMap_iff _).mpr
  exact RingHom.finite_algebraMap.mpr (normalizationFinite k n)

/-- The affine polygon node scheme is reduced. -/
instance nodeScheme_reduced : IsReduced (nodeScheme k n) := inferInstance

end AlgebraicGeometry.Scheme.Polygon
end -- noncomputable section
end
section
/-! Constructive reciprocal gluing, on the same all-n cyclic affine ring. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits AlgebraicGeometry Polynomial
open scoped Polynomial
namespace AlgebraicGeometry.Scheme.Polygon

variable (k : Type u) [Field k] (n : ℕ)

/-- The actual cyclic conductor element. -/
def conductor : nodeRing k n :=
  ⟨fun _ => X * (X - 1), by simp [mem_nodeRing]⟩

/-- Multiplication by `X * (X - 1)` in every component, producing an element of the pinching
algebra. -/
def conductorMul (p : NormalizationRing k n) : nodeRing k n :=
  ⟨fun i => X * (X - 1) * p i, by simp [mem_nodeRing]⟩

/-- The polygon node ring localized away from the conductor element. -/
abbrev nodeOverlapRing := Localization.Away (conductor k n)
/-- The product polynomial normalization ring localized away from the conductor element. -/
abbrev normalizationOverlapRing := Localization.Away (conductor k n : NormalizationRing k n)

/-- The conductor-localization map induced by the normalization inclusion. -/
def localizationComparison : nodeOverlapRing k n →+* normalizationOverlapRing k n :=
  Localization.awayMap (nodeRing k n).val.toRingHom (conductor k n)

theorem localizationComparison_bijective : Function.Bijective (localizationComparison k n) := by
  change Function.Bijective (Localization.awayMap (nodeRing k n).val.toRingHom (conductor k n))
  constructor
  · apply Localization.awayMap_injective_iff.mpr
    intro a ha
    have hz : a = 0 := Subtype.ext ha
    exact ⟨0, by simp [hz]⟩
  · apply Localization.awayMap_surjective_iff.mpr
    intro p
    exact ⟨conductorMul k n p, 1, by ext i; simp [conductorMul, conductor]⟩

/-- The conductor localization of the pinching algebra identified with that of its normalization. -/
def conductorLocalizationEquiv : nodeOverlapRing k n ≃+* normalizationOverlapRing k n :=
  RingEquiv.ofBijective (localizationComparison k n) (localizationComparison_bijective k n)

/-- The conductor overlap ring of a single polynomial normalization component. -/
abbrev W := Polynomial.PinchedPair.ConductorReciprocal.W k
/-- The infinity chart ring of a single normalization component. -/
abbrev V := Polynomial.PinchedPair.infinityChartRing k
/-- The product of the conductor overlap rings of all normalization components. -/
abbrev productOverlapRing := Fin n → W k
/-- The product of the infinity chart rings of all normalization components. -/
abbrev productInfinityRing := Fin n → V k
/-- The product of the infinity overlap rings of all normalization components. -/
abbrev productInfinityOverlapRing := Fin n → Polynomial.PinchedPair.infinityOverlapRing k
/-- The common product overlap scheme used in the polygon gluing. -/
abbrev overlapScheme : Scheme.{u} := Spec (.of (productOverlapRing k n))
/-- The product infinity chart scheme of the polygon gluing. -/
abbrev infinityScheme : Scheme.{u} := Spec (.of (productInfinityRing k n))

/-- The product overlap ring is the conductor localization of the normalization ring. -/
instance productOverlap_isLocalization :
    IsLocalization.Away (conductor k n : NormalizationRing k n) (productOverlapRing k n) :=
  finitePiLocalization k[X] (W k) (Polynomial.PinchedPair.ConductorReciprocal.q k) n

/-- The normalization conductor localization identified with the product of component overlap
rings. -/
def productOverlapEquiv : normalizationOverlapRing k n ≃ₐ[NormalizationRing k n]
    productOverlapRing k n :=
  IsLocalization.algEquiv (Submonoid.powers (conductor k n : NormalizationRing k n)) _ _

/-- The node conductor localization identified with the product overlap ring. -/
def nodeProductOverlapEquiv : nodeOverlapRing k n ≃+* productOverlapRing k n :=
  (conductorLocalizationEquiv k n).trans (productOverlapEquiv k n).toRingEquiv

@[simp] theorem nodeProductOverlapEquiv_algebraMap (a : nodeRing k n) :
    nodeProductOverlapEquiv k n (algebraMap (nodeRing k n) (nodeOverlapRing k n) a) =
      algebraMap (NormalizationRing k n) (productOverlapRing k n) a := by
  change productOverlapEquiv k n (localizationComparison k n
    (algebraMap (nodeRing k n) (nodeOverlapRing k n) a)) = _
  rw [show localizationComparison k n
      (algebraMap (nodeRing k n) (nodeOverlapRing k n) a) =
      algebraMap (NormalizationRing k n) (normalizationOverlapRing k n) a from
    IsLocalization.map_eq (M := Submonoid.powers (conductor k n))
      (S := nodeOverlapRing k n) (T := Submonoid.powers (conductor k n : NormalizationRing k n))
      (Q := normalizationOverlapRing k n) (g := (nodeRing k n).val.toRingHom)
      (by rintro _ ⟨m, rfl⟩; exact ⟨m, by simp⟩) a]
  exact (productOverlapEquiv k n).commutes a

/-- The conductor localization mapped into the polygon node scheme. -/
def nodeOverlapInclusion : Spec (.of (nodeOverlapRing k n)) ⟶ nodeScheme k n :=
  Spec.map (CommRingCat.ofHom (algebraMap (nodeRing k n) (nodeOverlapRing k n)))
/-- The conductor localization is an open subscheme of the polygon node scheme. -/
instance nodeOverlapInclusion_open : IsOpenImmersion (nodeOverlapInclusion k n) :=
  IsOpenImmersion.of_isLocalization (conductor k n)

/-- The product conductor overlap mapped into the polynomial normalization scheme. -/
def normalizationOverlapInclusion : overlapScheme k n ⟶ Spec (.of (NormalizationRing k n)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (NormalizationRing k n) (productOverlapRing k n)))
/-- The product conductor overlap is open in the polynomial normalization scheme. -/
instance normalizationOverlapInclusion_open : IsOpenImmersion (normalizationOverlapInclusion k n) :=
  IsOpenImmersion.of_isLocalization (conductor k n : NormalizationRing k n)

/-- The product overlap scheme identified with the conductor open of the polygon node scheme. -/
def conductorOpenIso : overlapScheme k n ≅ Spec (.of (nodeOverlapRing k n)) :=
  Scheme.Spec.mapIso (nodeProductOverlapEquiv k n).toCommRingCatIso.op

/-- The product conductor overlap mapped to the polygon node chart. -/
def gluingToNode : overlapScheme k n ⟶ nodeScheme k n :=
  (conductorOpenIso k n).hom ≫ nodeOverlapInclusion k n
/-- The gluing map to the polygon node chart is an open immersion. -/
instance gluingToNode_open : IsOpenImmersion (gluingToNode k n) := by
  unfold gluingToNode
  infer_instance

theorem conductorOpenIso_over : gluingToNode k n =
    normalizationOverlapInclusion k n ≫ polynomialCover k n := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact nodeProductOverlapEquiv_algebraMap k n a

/-- The reciprocal-coordinate involution applied to every component overlap ring. -/
def reciprocalEquiv : productOverlapRing k n ≃ₐ[k] productOverlapRing k n :=
  AlgEquiv.piCongrRight fun _ => Polynomial.PinchedPair.ConductorReciprocal.reciprocalEquiv k

/-- The componentwise identification of the conductor overlap with the infinity overlap. -/
def standardOverlapEquiv : productOverlapRing k n ≃+* productInfinityOverlapRing k n :=
  RingEquiv.piCongrRight fun _ => (Polynomial.PinchedPair.standardOverlapEquiv k).toRingEquiv

/-- The product infinity overlap mapped into the product infinity chart. -/
def infinityOverlapInclusion : Spec (.of (productInfinityOverlapRing k n)) ⟶ infinityScheme k n :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (productInfinityRing k n) (productInfinityOverlapRing k n)))

/-- The product infinity overlap is an open subscheme of the product infinity chart. -/
instance infinityOverlapInclusion_open : IsOpenImmersion (infinityOverlapInclusion k n) :=
  IsOpenImmersion.of_isLocalization (fun _ : Fin n => algebraMap k[X] (V k) X)

/-- Explicit reciprocal gluing on every actual normalization component. -/
def gluingToInfinity : overlapScheme k n ⟶ infinityScheme k n :=
  (Scheme.Spec.mapIso (reciprocalEquiv k n).toRingEquiv.toCommRingCatIso.op).hom ≫
    (Scheme.Spec.mapIso (standardOverlapEquiv k n).toCommRingCatIso.symm.op).hom ≫
    infinityOverlapInclusion k n

/-- The reciprocal gluing map to the product infinity chart is an open immersion. -/
instance gluingToInfinity_open : IsOpenImmersion (gluingToInfinity k n) := by
  unfold gluingToInfinity
  infer_instance

/-- The literal scheme obtained by cyclic pinching and reciprocal infinity
charts. Projective-line component and properness identifications are next. -/
abbrev cycleScheme : Scheme.{u} := pushout (gluingToNode k n) (gluingToInfinity k n)
/-- The gluing of the polynomial normalization scheme with its product infinity chart. -/
abbrev normalizedScheme : Scheme.{u} :=
  pushout (normalizationOverlapInclusion k n) (gluingToInfinity k n)

/-- The actual finite chartwise polynomial cover extended across infinity. -/
def gluedPolynomialCover : normalizedScheme k n ⟶ cycleScheme k n :=
  Scheme.OpenNormalizationGluing.normalizationMap (gluingToNode k n) (gluingToInfinity k n)
    (normalizationOverlapInclusion k n) (polynomialCover k n) (conductorOpenIso_over k n).symm

theorem conductor_preimage : polynomialCover k n ⁻¹ᵁ (gluingToNode k n).opensRange =
    (normalizationOverlapInclusion k n).opensRange := by
  change polynomialCover k n ⁻¹ᵁ
    ((conductorOpenIso k n).hom ≫ nodeOverlapInclusion k n).opensRange = _
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  have hn : (nodeOverlapInclusion k n).opensRange = PrimeSpectrum.basicOpen (conductor k n) :=
    Scheme.Hom.opensRange_localizationAway (R := .of (nodeRing k n)) (conductor k n)
  have ha : (normalizationOverlapInclusion k n).opensRange =
      PrimeSpectrum.basicOpen (conductor k n : NormalizationRing k n) := by
    rw [SetLike.ext'_iff]
    exact PrimeSpectrum.localization_away_comap_range (productOverlapRing k n)
      (conductor k n : NormalizationRing k n)
  rw [hn, ha]
  ext p
  rfl

/-- The polynomial normalization cover extended across infinity is finite. -/
instance gluedPolynomialCover_finite : IsFinite (gluedPolynomialCover k n) :=
  Scheme.OpenNormalizationGluing.normalizationMap_finite
    (gluingToNode k n) (gluingToInfinity k n) (normalizationOverlapInclusion k n)
    (polynomialCover k n) (conductorOpenIso_over k n).symm (conductor_preimage k n)

theorem polynomialCover_surjective : Function.Surjective (polynomialCover k n) :=
  RingHom.IsIntegral.comap_surjective
    (RingHom.finite_algebraMap.mpr (normalizationFinite k n)).to_isIntegral Subtype.val_injective

theorem gluedPolynomialCover_surjective : Function.Surjective (gluedPolynomialCover k n) :=
  Scheme.OpenNormalizationGluing.normalizationMap_surjective
    (gluingToNode k n) (gluingToInfinity k n) (normalizationOverlapInclusion k n)
    (polynomialCover k n) (conductorOpenIso_over k n).symm (polynomialCover_surjective k n)

/-- The polynomial normalization cover extended across infinity is surjective. -/
instance gluedPolynomialCover_surjective_instance : Surjective (gluedPolynomialCover k n) :=
  ⟨gluedPolynomialCover_surjective k n⟩

end AlgebraicGeometry.Scheme.Polygon

end -- noncomputable section
end
section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits AlgebraicGeometry Polynomial
open scoped Polynomial
namespace AlgebraicGeometry.Scheme.Polygon
variable (k : Type u) [Field k] (n : ℕ)

/-- Actual affine restriction into the overlap product. -/
def affineOverlapRingMap : nodeRing k n →ₐ[k] productOverlapRing k n :=
  ((IsScalarTower.toAlgHom k k[X] (W k)).compLeft (Fin n)).comp (nodeRing k n).val

/-- The restriction from each infinity chart ring to its reciprocal conductor overlap ring. -/
def infinityOverlapRingMap : productInfinityRing k n →ₐ[k] productOverlapRing k n :=
  (Polynomial.PinchedPair.infinityOverlapRingMap k).compLeft (Fin n)

theorem gluingToNode_spec : gluingToNode k n =
    Spec.map (CommRingCat.ofHom (affineOverlapRingMap k n).toRingHom) := by
  rw [conductorOpenIso_over]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

theorem gluingToInfinity_spec : gluingToInfinity k n =
    Spec.map (CommRingCat.ofHom (infinityOverlapRingMap k n).toRingHom) := by
  change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

end AlgebraicGeometry.Scheme.Polygon
end -- noncomputable section
end
section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Polynomial
open scoped Polynomial
namespace AlgebraicGeometry.Scheme.Polygon
variable (k : Type u) [Field k] (n : ℕ)

/-- Product of the actual component function fields. -/
abbrev RationalFunctions := Fin n → FractionRing k[X]

/-- The componentwise inclusion of the polynomial normalization ring into its rational function
fields. -/
def fractionMap : NormalizationRing k n →+* RationalFunctions k n :=
  RingHom.pi fun i => (algebraMap k[X] (FractionRing k[X])).comp (Pi.evalRingHom _ i)

/-- The product rational function fields as an algebra over the polynomial normalization ring. -/
instance normalizationFractionAlgebra : Algebra (NormalizationRing k n) (RationalFunctions k n) :=
  (fractionMap k n).toAlgebra
/-- The product rational function fields as an algebra over the cyclic pinching ring. -/
instance nodeFractionAlgebra : Algebra (nodeRing k n) (RationalFunctions k n) :=
  ((fractionMap k n).comp (nodeRing k n).val.toRingHom).toAlgebra
/-- The rational-function scalar actions are compatible with the normalization inclusion. -/
instance nodeFractionTower : IsScalarTower (nodeRing k n) (NormalizationRing k n)
    (RationalFunctions k n) where
  smul_assoc a p z := by
    funext i
    change ((a : NormalizationRing k n) i • p i) • z i =
      (a : NormalizationRing k n) i • (p i • z i)
    exact smul_assoc _ _ _

/-- Integral closure is proved componentwise in the actual function fields. -/
instance normalization_isIntegralClosure :
    IsIntegralClosure (NormalizationRing k n) (nodeRing k n) (RationalFunctions k n) := by
  constructor
  · intro x y h
    funext i
    exact IsFractionRing.injective k[X] (FractionRing k[X]) (congrFun h i)
  · intro z
    constructor
    · intro hz
      have hi (i : Fin n) : _root_.IsIntegral k[X] (z i) :=
        IsIntegral.map_of_comp_eq
          ((Pi.evalRingHom (fun _ : Fin n => k[X]) i).comp (nodeRing k n).val.toRingHom)
          (Pi.evalRingHom (fun _ : Fin n => FractionRing k[X]) i) rfl hz
      have hp (i : Fin n) : ∃ p : k[X], algebraMap k[X] (FractionRing k[X]) p = z i :=
        IsIntegrallyClosed.isIntegral_iff.mp (hi i)
      choose p hp using hp
      exact ⟨p, funext hp⟩
    · rintro ⟨z, rfl⟩
      exact IsIntegral.map_of_comp_eq (RingHom.id (nodeRing k n)) (fractionMap k n) rfl
        (Algebra.IsIntegral.isIntegral (R := nodeRing k n) z)

/-- A nonzero-divisor is exactly a tuple nonzero on every actual component. -/
theorem node_nonZeroDivisors_iff (a : nodeRing k n) :
    a ∈ nonZeroDivisors (nodeRing k n) ↔ ∀ i, (a : NormalizationRing k n) i ≠ 0 := by
  classical
  constructor
  · intro ha i hi
    have hz : conductorMul k n (Pi.single i 1) * a = 0 := by
      apply Subtype.ext
      funext j
      by_cases hji : j = i
      · subst j
        simp [conductorMul, hi]
      · simp [conductorMul, Pi.single_eq_of_ne hji]
    have hc := (mem_nonZeroDivisors_iff_right.mp ha) _ hz
    have he := congrArg (fun p : nodeRing k n => (p : NormalizationRing k n) i) hc
    change (X : k[X]) * (X - 1) * ((Pi.single i 1 : Fin n → k[X]) i) = 0 at he
    simp only [Pi.single_eq_same, mul_one] at he
    exact Polynomial.PinchedPair.conductor_ne_zero k he
  · intro ha
    apply mem_nonZeroDivisors_iff_right.mpr
    intro b hb
    apply Subtype.ext
    funext i
    have he := congrArg (fun p : nodeRing k n => (p : NormalizationRing k n) i) hb
    exact (mul_eq_zero.mp he).resolve_right (ha i)

@[simp] theorem node_fraction_apply (a : nodeRing k n) (i : Fin n) :
    algebraMap (nodeRing k n) (RationalFunctions k n) a i =
      algebraMap k[X] (FractionRing k[X]) ((a : NormalizationRing k n) i) := rfl

theorem fraction_surj (z : RationalFunctions k n) :
  ∃ x : nodeRing k n × nonZeroDivisors (nodeRing k n),
    z * algebraMap (nodeRing k n) (RationalFunctions k n) x.2 =
      algebraMap (nodeRing k n) (RationalFunctions k n) x.1 := by
  let q : Fin n → k[X] × nonZeroDivisors k[X] :=
    fun i => IsLocalization.sec (nonZeroDivisors k[X]) (z i)
  have hq (i : Fin n) : z i * algebraMap k[X] (FractionRing k[X]) (q i).2 =
      algebraMap k[X] (FractionRing k[X]) (q i).1 :=
    IsLocalization.sec_spec (nonZeroDivisors k[X]) (z i)
  let den : nodeRing k n := conductorMul k n (fun i => (q i).2)
  have hd : den ∈ nonZeroDivisors (nodeRing k n) := by
    apply (node_nonZeroDivisors_iff k n den).mpr
    intro i
    change (X * (X - 1) : k[X]) * ((q i).2 : k[X]) ≠ 0
    exact mul_ne_zero (Polynomial.PinchedPair.conductor_ne_zero k)
      (nonZeroDivisors.ne_zero (q i).2.property)
  refine ⟨(conductorMul k n (fun i => (q i).1), ⟨den, hd⟩), ?_⟩
  funext i
  simp only [Pi.mul_apply, node_fraction_apply]
  simp only [conductorMul, den]
  rw [map_mul, mul_left_comm, hq i, ← map_mul]

/-- Literal total fraction ring. Each actual component denominator is cleared
by the conductor, so the resulting denominator is in the cyclic node ring. -/
instance sameFractionRing : IsFractionRing (nodeRing k n) (RationalFunctions k n) where
  map_units a := by
    have ha := (node_nonZeroDivisors_iff k n a).mp a.property
    apply Pi.isUnit_iff.mpr
    intro i
    apply isUnit_iff_ne_zero.mpr
    exact (map_ne_zero_iff _ (IsFractionRing.injective k[X] (FractionRing k[X]))).mpr (ha i)
  surj := fraction_surj k n
  exists_of_eq {a b} h := by
    have he : a = b := by
      apply Subtype.ext
      funext i
      exact IsFractionRing.injective k[X] (FractionRing k[X]) (congrFun h i)
    exact ⟨1, by simpa using he⟩

end AlgebraicGeometry.Scheme.Polygon

end -- noncomputable section
end
section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits AlgebraicGeometry Polynomial
open scoped Polynomial
namespace AlgebraicGeometry.Scheme.Polygon

variable (k : Type u) [Field k] (n : ℕ)
/-- The coproduct of the `n` glued projective-line components. -/
abbrev linesScheme : Scheme.{u} := ∐ (fun _ : Fin n => Scheme.PinchedLine.lineGluing k)

/-- The inclusion of component `i` into the product polynomial normalization scheme. -/
def componentAffine (i : Fin n) : Spec (.of k[X]) ⟶ Spec (.of (NormalizationRing k n)) :=
  Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin n => k[X]) i))
/-- The inclusion of component `i` into the product infinity scheme. -/
def componentInfinity (i : Fin n) : Spec (.of (V k)) ⟶ infinityScheme k n :=
  Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin n => V k) i))
/-- The inclusion of component `i` into the product overlap scheme. -/
def componentOverlap (i : Fin n) : Spec (.of (W k)) ⟶ overlapScheme k n :=
  Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin n => W k) i))

@[reassoc] theorem componentOverlap_affine (i : Fin n) :
    componentOverlap k n i ≫ normalizationOverlapInclusion k n =
      Scheme.PinchedLine.normalizationOverlapInclusion k ≫ componentAffine k n i := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

@[reassoc] theorem componentOverlap_infinity (i : Fin n) :
    componentOverlap k n i ≫ gluingToInfinity k n =
      Scheme.PinchedLine.gluingToInfinity k ≫ componentInfinity k n i := by
  rw [gluingToInfinity_spec, Scheme.PinchedLine.gluingToInfinity_spec]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

/-- Each actual reciprocal projective-line gluing maps to its component. -/
def componentLine (i : Fin n) : Scheme.PinchedLine.lineGluing k ⟶ normalizedScheme k n :=
  pushout.desc
    (componentAffine k n i ≫ pushout.inl (normalizationOverlapInclusion k n) (gluingToInfinity k n))
    (componentInfinity k n i ≫ pushout.inr (normalizationOverlapInclusion k n)
      (gluingToInfinity k n))
    (by
      rw [← Category.assoc, ← componentOverlap_affine, Category.assoc, pushout.condition,
        ← Category.assoc, componentOverlap_infinity, Category.assoc])

@[reassoc, simp] theorem componentLine_affine (i : Fin n) :
    pushout.inl (Scheme.PinchedLine.normalizationOverlapInclusion k)
      (Scheme.PinchedLine.gluingToInfinity k) ≫
      componentLine k n i = componentAffine k n i ≫
        pushout.inl (normalizationOverlapInclusion k n) (gluingToInfinity k n) :=
  pushout.inl_desc _ _ _

@[reassoc, simp] theorem componentLine_infinity (i : Fin n) :
    pushout.inr (Scheme.PinchedLine.normalizationOverlapInclusion k)
      (Scheme.PinchedLine.gluingToInfinity k) ≫
      componentLine k n i = componentInfinity k n i ≫
        pushout.inr (normalizationOverlapInclusion k n) (gluingToInfinity k n) :=
  pushout.inr_desc _ _ _

/-- The product polynomial chart mapped to the coproduct of the glued projective lines. -/
def affineToLines : Spec (.of (NormalizationRing k n)) ⟶ linesScheme k n :=
  (piSpecIso k[X] n).hom ≫ Limits.Sigma.map (fun _ : Fin n =>
    pushout.inl (Scheme.PinchedLine.normalizationOverlapInclusion k)
      (Scheme.PinchedLine.gluingToInfinity k))

/-- The product infinity chart mapped to the coproduct of the glued projective lines. -/
def infinityToLines : infinityScheme k n ⟶ linesScheme k n :=
  (piSpecIso (V k) n).hom ≫ Limits.Sigma.map (fun _ : Fin n =>
    pushout.inr (Scheme.PinchedLine.normalizationOverlapInclusion k)
      (Scheme.PinchedLine.gluingToInfinity k))

@[reassoc, simp] theorem componentAffine_toLines (i : Fin n) :
    componentAffine k n i ≫ affineToLines k n =
      pushout.inl (Scheme.PinchedLine.normalizationOverlapInclusion k)
        (Scheme.PinchedLine.gluingToInfinity k) ≫
        Sigma.ι (fun _ : Fin n => Scheme.PinchedLine.lineGluing k) i := by
  unfold componentAffine affineToLines
  rw [piSpecIso_component_assoc, Limits.Sigma.ι_map]

@[reassoc, simp] theorem componentInfinity_toLines (i : Fin n) :
    componentInfinity k n i ≫ infinityToLines k n =
      pushout.inr (Scheme.PinchedLine.normalizationOverlapInclusion k)
        (Scheme.PinchedLine.gluingToInfinity k) ≫
        Sigma.ι (fun _ : Fin n => Scheme.PinchedLine.lineGluing k) i := by
  unfold componentInfinity infinityToLines
  rw [piSpecIso_component_assoc, Limits.Sigma.ι_map]

theorem toLines_compatibility :
    normalizationOverlapInclusion k n ≫ affineToLines k n =
      gluingToInfinity k n ≫ infinityToLines k n := by
  apply (cancel_epi (sigmaSpec (fun _ : Fin n => CommRingCat.of (W k)))).mp
  apply Sigma.hom_ext
  intro i
  simp only [ι_sigmaSpec_assoc]
  change componentOverlap k n i ≫ normalizationOverlapInclusion k n ≫ affineToLines k n =
    componentOverlap k n i ≫ gluingToInfinity k n ≫ infinityToLines k n
  rw [componentOverlap_affine_assoc, componentOverlap_infinity_assoc,
    componentAffine_toLines, componentInfinity_toLines, ← Category.assoc,
    ← Category.assoc, pushout.condition]

/-- The normalization gluing mapped to the coproduct of its projective-line components. -/
def normalizationToLines : normalizedScheme k n ⟶ linesScheme k n :=
  pushout.desc (affineToLines k n) (infinityToLines k n) (toLines_compatibility k n)

/-- The coproduct of the projective-line components mapped to the normalization gluing. -/
def linesToNormalization : linesScheme k n ⟶ normalizedScheme k n :=
  Sigma.desc (componentLine k n)

/-- Actual disjoint projective-line components, proved by the two universal
properties and the finite-product spectrum isomorphism. -/
def normalizationLinesIso : normalizedScheme k n ≅ linesScheme k n where
  hom := normalizationToLines k n
  inv := linesToNormalization k n
  hom_inv_id := by
    apply pushout.hom_ext
    · apply (cancel_epi (sigmaSpec (fun _ : Fin n => CommRingCat.of k[X]))).mp
      apply Sigma.hom_ext
      intro i
      simp only [ι_sigmaSpec_assoc, normalizationToLines,
        pushout.inl_desc_assoc, Category.comp_id]
      change componentAffine k n i ≫ affineToLines k n ≫ linesToNormalization k n = _
      rw [componentAffine_toLines_assoc]
      simp [linesToNormalization, componentAffine]
    · apply (cancel_epi (sigmaSpec (fun _ : Fin n => CommRingCat.of (V k)))).mp
      apply Sigma.hom_ext
      intro i
      simp only [ι_sigmaSpec_assoc, normalizationToLines,
        pushout.inr_desc_assoc, Category.comp_id]
      change componentInfinity k n i ≫ infinityToLines k n ≫ linesToNormalization k n = _
      rw [componentInfinity_toLines_assoc]
      simp [linesToNormalization, componentInfinity]
  inv_hom_id := by
    apply Sigma.hom_ext
    intro i
    simp only [linesToNormalization, Sigma.ι_comp_desc_assoc, Category.comp_id]
    apply pushout.hom_ext
    · simp only [componentLine_affine_assoc, normalizationToLines,
        pushout.inl_desc, componentAffine_toLines]
    · simp only [componentLine_infinity_assoc, normalizationToLines,
        pushout.inr_desc, componentInfinity_toLines]

/-- The normalized source is literally the finite coproduct of the existing
actual Proj projective lines. -/
def normalizationP1Iso : normalizedScheme k n ≅
    ∐ (fun _ : Fin n => Scheme.ProjectiveLine.projectiveP1 k) :=
  normalizationLinesIso k n ≪≫
    Sigma.mapIso (fun _ : Fin n => Scheme.PinchedLine.ProjectiveComparison.lineIsoP1 k)

/-- Every actual coproduct stalk is one of the existing normal P1 stalks. -/
theorem lines_normal : _root_.AlgebraicGeometry.Scheme.NormalStalks (linesScheme k n) := by
  intro z
  obtain ⟨⟨i⟩, x, hx⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective
    (Discrete.functor (fun _ : Fin n => Scheme.PinchedLine.lineGluing k)) z
  change Sigma.ι (fun _ : Fin n => Scheme.PinchedLine.lineGluing k) i x = z at hx
  subst z
  have h := Scheme.PinchedLine.lineGluing_normal k x
  let := h.1
  let := h.2
  let e := (asIso ((Sigma.ι (fun _ : Fin n => Scheme.PinchedLine.lineGluing k) i).stalkMap
    x)).commRingCatIsoToRingEquiv
  exact ⟨e.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e.symm⟩

/-- Normality of the literal glued normalization source, unconditionally. -/
theorem normalized_normal :
    _root_.AlgebraicGeometry.Scheme.NormalStalks (normalizedScheme k n) := by
  intro x
  have h := lines_normal k n ((normalizationLinesIso k n).hom x)
  let := h.1
  let := h.2
  let e := (asIso ((normalizationLinesIso k n).hom.stalkMap x)).commRingCatIsoToRingEquiv
  exact ⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e⟩

end AlgebraicGeometry.Scheme.Polygon

end -- noncomputable section
end
section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits AlgebraicGeometry Polynomial
open scoped Polynomial
namespace AlgebraicGeometry.Scheme.Polygon
variable (k : Type u) [Field k] (n : ℕ)

/-- Injectivity of the actual reciprocal infinity restriction. -/
theorem baseInfinityOverlap_injective : Function.Injective
  (Polynomial.PinchedPair.infinityOverlapRingMap k) := by
  have hV : Function.Injective (algebraMap k[X] (V k)) :=
    IsLocalization.injective (V k) (powers_le_nonZeroDivisors_of_noZeroDivisors
      (by simpa only [C_1] using X_sub_C_ne_zero (1 : k)))
  have hX : algebraMap k[X] (V k) X ≠ 0 :=
    (map_ne_zero_iff _ hV).mpr X_ne_zero
  have hL : Function.Injective (algebraMap (V k) (Polynomial.PinchedPair.infinityOverlapRing k)) :=
    IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors hX)
  exact (Polynomial.PinchedPair.ConductorReciprocal.reciprocalEquiv k).injective.comp
    ((Polynomial.PinchedPair.standardOverlapEquiv k).symm.injective.comp hL)

theorem infinityOverlapRingMap_injective : Function.Injective (infinityOverlapRingMap k n) := by
  intro p q h
  funext i
  exact baseInfinityOverlap_injective k (congrFun h i)

/-- Every infinity component has a dense actual intersection with the affine
chart, established from the injective coordinate restriction. -/
theorem infinityOverlap_dense : DenseRange (gluingToInfinity k n) := by
  rw [gluingToInfinity_spec]
  change DenseRange (PrimeSpectrum.comap (infinityOverlapRingMap k n).toRingHom)
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical]
  intro p hp
  change infinityOverlapRingMap k n p = 0 at hp
  have hz : p = 0 := infinityOverlapRingMap_injective k n (hp.trans (map_zero _).symm)
  rw [hz]
  exact Ideal.zero_mem _

theorem affineChart_dense :
    DenseRange (pushout.inl (gluingToNode k n) (gluingToInfinity k n)) := by
  intro z
  rcases Scheme.openPushout_covered (gluingToNode k n) (gluingToInfinity k n) z with
    ⟨x, rfl⟩ | ⟨y, rfl⟩
  · exact subset_closure ⟨x, rfl⟩
  · refine (infinityOverlap_dense k n).induction_on
      (p := fun v => pushout.inr (gluingToNode k n) (gluingToInfinity k n) v ∈
        closure (Set.range (pushout.inl (gluingToNode k n) (gluingToInfinity k n))))
      y (isClosed_closure.preimage (pushout.inr (gluingToNode k n) (gluingToInfinity k
        n)).continuous) ?_
    intro w
    rw [← Scheme.Hom.comp_apply, ← pushout.condition, Scheme.Hom.comp_apply]
    exact subset_closure ⟨gluingToNode k n w, rfl⟩

/-- Connectedness comes from the actual dense connected affine cyclic chart. -/
theorem cycleScheme_connected [NeZero n] : ConnectedSpace (cycleScheme k n) := by
  have := nodeScheme_connected k n
  apply connectedSpace_iff_univ.mpr
  have h := (isConnected_range (pushout.inl (gluingToNode k n)
    (gluingToInfinity k n)).continuous).closure
  simpa only [(affineChart_dense k n).closure_range] using h

end AlgebraicGeometry.Scheme.Polygon
end -- noncomputable section
end
