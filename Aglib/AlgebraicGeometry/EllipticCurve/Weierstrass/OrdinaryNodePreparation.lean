/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.SplitNodalNormalForm
public import Aglib.RingTheory.Etale.QuadraticResidue
public import Aglib.RingTheory.DiscreteValuationRing.EtaleBaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Ordinary Weierstrass nodes and their actual splitting extensions

The ordinary residue-point data retain the original equation and gradients. The extension is the
identity exactly in the split case, and the literal quadratic tangent quotient in the nonsplit
case. The generic field and residue maps are the lower native fraction and residue maps of that
same extension.

R5 revision `f8a3314ddecffcada2ec721d26d56a937bed9690`.
`Curves/LocalModels/Splitting/OrdinaryNode.lean`: source ranges [[38, 142],
[165, 202]];
SHA-256 `98414173573c407db5ce591f59486990c04ddb0c5eff81901068de1ac1e0b6c8`.
`Curves/LocalModels/Splitting/Extension.lean`: source ranges [[44, 87]];
SHA-256 `353552c928167cb9012c9a727633d1d2b63e063b1123dd0787eab7c3ce3ea3a9`.
-/

@[expose] public noncomputable section

universe u
open Polynomial IsLocalRing WeierstrassCurve
open WeierstrassCurve.SplitNodalNormalForm Algebra.QuadraticEtale
namespace WeierstrassCurve.OrdinaryNodePreparation
variable {R : Type u} [CommRing R]

/-- Both actual rational tangent slopes at the reduced origin. -/
def splitNodeAtOrigin [IsLocalRing R] (W : WeierstrassCurve R)
    (h3 : W.a₃ = 0) (h4 : W.a₄ = 0) (h6 : W.a₆ ∈ IsLocalRing.maximalIdeal R)
    (s : ResidueField R)
    (hs : s ^ 2 + residue R W.a₁ * s - residue R W.a₂ = 0)
    (hd : 2 * s + residue R W.a₁ ≠ 0) : SplitNodeData W where
  x := 0
  y := 0
  first := s
  second := -residue R W.a₁ - s
  point := by
    simp [WeierstrassCurve.Affine.Equation,
      WeierstrassCurve.Affine.evalEval_polynomial, (residue_eq_zero_iff _).mpr h6]
  gradientX := by simp [WeierstrassCurve.Affine.evalEval_polynomialX, h4]
  gradientY := by simp [WeierstrassCurve.Affine.evalEval_polynomialY, h3]
  firstRoot := by simpa using hs
  secondRoot := by
    simp only [mul_zero, add_zero]
    linear_combination hs
  distinct := by
    intro he
    apply hd
    linear_combination he

/-- Output data for a constructed finite étale local DVR extension.
The constructor below chooses R itself only when its actual residue tangent
polynomial has a root; otherwise it builds the concrete quadratic quotient. -/
structure NodeExtension [IsDomain R] [IsDiscreteValuationRing R]
    (W : WeierstrassCurve R) where
  /-- The underlying ring of the finite étale local DVR extension. -/
  ringType : Type u
  /-- The constructed extension ring has its actual commutative ring structure. -/
  [commRing : CommRing ringType]
  /-- The identity or irreducible quadratic quotient is a domain. -/
  [domain : IsDomain ringType]
  /-- The constructed local extension is a discrete valuation ring. -/
  [dvr : IsDiscreteValuationRing ringType]
  /-- The structural algebra map from the original DVR. -/
  [algebra : Algebra R ringType]
  /-- The actual extension is finite over the original DVR. -/
  [finite : Module.Finite R ringType]
  /-- The actual extension is étale over the original DVR. -/
  [etale : Algebra.Etale R ringType]
  /-- The same structural algebra map is local. -/
  [localHom : IsLocalHom (algebraMap R ringType)]
  /-- A split node of the original equation after the structural base change. -/
  splitNode : SplitNodeData (W.map (algebraMap R ringType))

attribute [instance] NodeExtension.commRing NodeExtension.domain NodeExtension.dvr
  NodeExtension.algebra NodeExtension.finite NodeExtension.etale NodeExtension.localHom

/-- Construct the splitting ring, including the genuinely quadratic nonsplit case. -/
def nodeExtension [IsDomain R] [IsDiscreteValuationRing R]
    (W : WeierstrassCurve R) (h3 : W.a₃ = 0) (h4 : W.a₄ = 0)
    (h6 : W.a₆ ∈ IsLocalRing.maximalIdeal R) (hb : IsUnit W.b₂) : NodeExtension W := by
  classical
  by_cases hs : ∃ s : ResidueField R,
      s ^ 2 + residue R W.a₁ * s - residue R W.a₂ = 0
  · let s := hs.choose
    have hsroot := hs.choose_spec
    refine { ringType := R, splitNode := ?_ }
    simpa only [Algebra.algebraMap_self, WeierstrassCurve.map_id] using
      splitNodeAtOrigin W h3 h4 h6 s hsroot
        (simple_root_of_unit_discriminant W.a₁ W.a₂ hb s hsroot)
  · have hirr := residue_polynomial_irreducible W.a₁ W.a₂ hs
    let S := Quadratic W.a₁ W.a₂
    let : IsDomain S := quadratic_domain W.a₁ W.a₂ hirr
    let : IsDiscreteValuationRing S := quadratic_dvr W.a₁ W.a₂ hirr hb
    let : Module.Finite R S := quadratic_finite W.a₁ W.a₂
    let : Algebra.Etale R S := quadratic_etale W.a₁ W.a₂ hb
    have hinj : Function.Injective (algebraMap R S) :=
      AdjoinRoot.of.injective_of_monic_of_degree_pos (polynomial_monic W.a₁ W.a₂)
        (by
          rw [Polynomial.degree_eq_natDegree (polynomial_monic W.a₁ W.a₂).ne_zero,
            polynomial_natDegree]
          norm_num)
    let : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hinj
    let : IsLocalHom (algebraMap R S) := inferInstance
    let s : ResidueField S := residue S (root W.a₁ W.a₂)
    have hsroot : s ^ 2 + residue S ((algebraMap R S) W.a₁) * s -
        residue S ((algebraMap R S) W.a₂) = 0 := by
      simpa only [map_sub, map_add, map_mul, map_pow, map_zero] using
        congrArg (residue S) (root_relation W.a₁ W.a₂)
    have hd : 2 * s + residue S ((algebraMap R S) W.a₁) ≠ 0 := by
      simpa only [map_add, map_mul, map_ofNat] using
        (residue_ne_zero_iff_isUnit (2 * root W.a₁ W.a₂ + algebraMap R S W.a₁)).mpr
          (derivative_isUnit W.a₁ W.a₂ hb)
    refine { ringType := S, splitNode := ?_ }
    apply splitNodeAtOrigin (W.map (algebraMap R S))
      (by simp [h3]) (by simp [h4]) ?_ s hsroot hd
    change ¬ IsUnit ((algebraMap R S) W.a₆)
    intro hu
    exact h6 ((isUnit_map_iff (algebraMap R S) W.a₆).mp hu)

/-- In the nonsplit case the constructed ring has rank exactly two over R. -/
lemma nodeExtension_nonsplit_rank [IsDomain R] [IsDiscreteValuationRing R]
    (W : WeierstrassCurve R) (h3 : W.a₃ = 0) (h4 : W.a₄ = 0)
    (h6 : W.a₆ ∈ IsLocalRing.maximalIdeal R) (hb : IsUnit W.b₂)
    (hno : ¬ ∃ s : ResidueField R,
      s ^ 2 + residue R W.a₁ * s - residue R W.a₂ = 0) :
    Module.finrank R (nodeExtension W h3 h4 h6 hb).ringType = 2 := by
  classical
  unfold nodeExtension
  rw [dite_eq_right hno]
  exact (AdjoinRoot.powerBasis' (polynomial_monic W.a₁ W.a₂)).finrank.trans
    (polynomial_natDegree W.a₁ W.a₂)

/-- The identity branch is used precisely when the actual tangent has a root. -/
lemma nodeExtension_split_rank [IsDomain R] [IsDiscreteValuationRing R]
    (W : WeierstrassCurve R) (h3 : W.a₃ = 0) (h4 : W.a₄ = 0)
    (h6 : W.a₆ ∈ IsLocalRing.maximalIdeal R) (hb : IsUnit W.b₂)
    (hs : ∃ s : ResidueField R,
      s ^ 2 + residue R W.a₁ * s - residue R W.a₂ = 0) :
    Module.finrank R (nodeExtension W h3 h4 h6 hb).ringType = 1 := by
  classical
  unfold nodeExtension
  rw [dite_eq_left hs]
  exact Module.finrank_self R


/-- A rational ordinary double point on the literal reduced Weierstrass cubic. -/
structure OrdinaryNodeData [IsLocalRing R] (W : WeierstrassCurve R) where
  /-- The x-coordinate of the node on the reduced Weierstrass cubic. -/
  x : ResidueField R
  /-- The y-coordinate of the node on the reduced Weierstrass cubic. -/
  y : ResidueField R
  point : (W.map (residue R)).toAffine.Equation x y
  gradientX : (W.map (residue R)).toAffine.polynomialX.evalEval x y = 0
  gradientY : (W.map (residue R)).toAffine.polynomialY.evalEval x y = 0
  ordinary : WeierstrassCurve.CriticalPoint.criticalHessianDet (W.map (residue R)) x ≠ 0

/-- A constructed integral critical translation of the original equation. -/
structure CriticalPreparation [IsLocalRing R] (W : WeierstrassCurve R) where
  /-- The integral x-translation parameter of the critical translation. -/
  r : R
  /-- The integral y-translation parameter of the critical translation. -/
  t : R
  a3 : (translate W r t).a₃ = 0
  a4 : (translate W r t).a₄ = 0
  a6 : (translate W r t).a₆ ∈ IsLocalRing.maximalIdeal R
  b2 : IsUnit (translate W r t).b₂

/-- Hensel solves the actual gradient system; no critical point is supplied. -/
def prepareOrdinaryNode [HenselianLocalRing R]
    {W : WeierstrassCurve R} (d : OrdinaryNodeData W) : CriticalPreparation W :=
  Classical.choice (by
    obtain ⟨r, t, _, _, _, _, h3, h4, hb, h6, _⟩ :=
      WeierstrassCurve.CriticalPoint.exists_critical_translation
        W d.x d.y d.point d.gradientX d.gradientY d.ordinary
    exact ⟨⟨r, t, h3, h4, h6, hb⟩⟩)

open WeierstrassCurve.CriticalPoint

namespace CriticalPreparation
variable [IsLocalRing R] {W : WeierstrassCurve R}

/-- The scale-one admissible change to the constructed critical point. -/
def change (d : CriticalPreparation W) : WeierstrassCurve.VariableChange R :=
  ⟨1, d.r, 0, d.t⟩

@[simp] lemma change_equation (d : CriticalPreparation W) :
    d.change • W = translate W d.r d.t := rfl

end CriticalPreparation

namespace CriticalPreparation
variable [IsDomain R] [IsDiscreteValuationRing R] {W : WeierstrassCurve R}
/-- The finite étale splitting extension of the actual translated tangent cone. -/
def extension (d : CriticalPreparation W) : NodeExtension (d.change • W) :=
  nodeExtension _ d.a3 d.a4 d.a6 d.b2

end CriticalPreparation
end WeierstrassCurve.OrdinaryNodePreparation

namespace WeierstrassCurve.OrdinaryNodePreparation.NodeExtension
open IsDiscreteValuationRing.EtaleBaseChange AlgebraicGeometry
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {W : WeierstrassCurve R} (d : NodeExtension W)

/-- The fraction field of the constructed finite étale local DVR extension. -/
abbrev genericField := FractionRing d.ringType

/-- The constructed local étale extension is faithfully flat. -/
instance faithfullyFlat : Module.FaithfullyFlat R d.ringType :=
  Module.FaithfullyFlat.of_flat_of_isLocalHom

lemma ramificationIndexOne (r : R) :
    IsDiscreteValuationRing.addVal d.ringType (algebraMap R d.ringType r) =
      IsDiscreteValuationRing.addVal R r := IsDiscreteValuationRing.unramified_addVal r

/-- The canonical map of the actual residue fields. -/
def residueEmbedding : ResidueField R →+* ResidueField d.ringType :=
  algebraMap (ResidueField R) (ResidueField d.ringType)

@[simp] lemma residueEmbedding_compatible (r : R) :
    d.residueEmbedding (residue R r) = residue d.ringType (algebraMap R d.ringType r) := rfl

lemma etaleBaseMap : Etale (Spec.map (CommRingCat.ofHom (algebraMap R d.ringType))) := by
  exact (HasRingHomProperty.Spec_iff (P := @Etale)).2
    (RingHom.etale_algebraMap.mpr inferInstance)

/-- The constructed extension is smooth, hence is the regular base change
needed by the accepted normalization comparison. -/
lemma smoothBaseMap : Smooth (Spec.map (CommRingCat.ofHom (algebraMap R d.ringType))) := by
  let := d.etaleBaseMap
  infer_instance


variable {F : Type u} [Field F] [Algebra R F] [IsFractionRing R F]

/-- The actual fraction-field embedding extending the same ring map. -/
def embedding : F →+* d.genericField := fractionEmbedding (R := R) (S := d.ringType) (F := F)

lemma compatible : (d.embedding (F := F)).comp (algebraMap R F) =
    (algebraMap d.ringType d.genericField).comp (algebraMap R d.ringType) :=
  fractionEmbedding_compatible (R := R) (S := d.ringType) (F := F)

/-- The algebra structure induced by the actual fraction-field embedding. -/
@[instance_reducible]
def genericAlgebra : Algebra F d.genericField := fractionAlgebra (R := R) (S := d.ringType) (F := F)

lemma genericAlgebra_tower : let := d.genericAlgebra (F := F)
    IsScalarTower R F d.genericField := fractionAlgebra_tower (R := R) (S := d.ringType) (F := F)

lemma genericAlgebra_finite : let := d.genericAlgebra (F := F)
    Module.Finite F d.genericField := fractionAlgebra_finite (R := R) (S := d.ringType) (F := F)

end WeierstrassCurve.OrdinaryNodePreparation.NodeExtension
