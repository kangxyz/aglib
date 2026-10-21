/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Abel.Inverse
public import Aglib.AlgebraicGeometry.Curves.Abel.FiniteCartierDegree
public import Aglib.AlgebraicGeometry.Curves.Picard.Degree.ProperCurveProductFormula
public import Aglib.AlgebraicGeometry.Curves.Picard.NormDegree.OrderFormula
public import Aglib.AlgebraicGeometry.Curves.RiemannRoch.HighDegreeVanishing
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.QuasiCompactSeparated
public import Aglib.AlgebraicGeometry.Cohomology.Vanishing.Noetherian
public import Aglib.AlgebraicGeometry.Group.PointedMorphism
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Normality
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Dimension
public import Aglib.AlgebraicGeometry.Properties.Normal.Components

/-!
# The Abel class and an existing proper curve group law

The existing evaluation-divisor inverse is used only on actual locally
Noetherian test schemes. Equality on residue-field points gives injectivity
on reduced test schemes. No representing scheme is assumed or constructed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.RelativePicard.Classes
open AlgebraicGeometry.Scheme.OverField.Curve

universe u

namespace AlgebraicGeometry.Scheme.Group.PointDivisor

attribute [local instance] Over.cartesianMonoidalCategory

variable (hnormal : SmoothFieldNormality.{u}) (hcomp : NormalComponentsOpen.{u})
variable (hreg : SmoothFieldRegularity.{u}) (hclosed : SmoothClosedPointDimension.{u})
variable (hdim : SmoothFieldDimension.{u})
variable (hprod : Curve.Picard.Degree.ProperCurveProductFormula.{u})
variable (htensor : ModuleTensorPullback.{u}) (hcartier : Curve.Abel.FiniteCartierIdealDegree.{u})
variable (hbase : RelativeCartierIdealBaseChange.{u}) (hdivisor : SmoothRelativeDivisorIdeal.{u})
variable (hnorm : Curve.Picard.NormDegree.FiniteMorphismNormOrder.{u})
variable (hgenus : Cohomology.ProperStructureCohomologyBaseChange.{u})
variable (hrr : LineBundleRiemannRoch.{u}) (hvanish : LineBundleHighDegreeVanishing.{u})
variable (hhigher : Cohomology.NoetherianSheafCohomologyVanishing.{u})
variable {k : Type u} [Field k] (X : FScheme k) (hX : Curve.Properties X)
variable (o : 𝟙_ (FScheme k) ⟶ X) (hg : coherentGenus k X = 1)

local notation "pointClass" => Curve.Abel.degreeZeroAbelClass hnormal hcomp hreg hclosed hdim
  hprod htensor X hX hcartier hdivisor hbase o.left (Over.w o)

include hnorm hgenus hrr hvanish hhigher hg in
/-- The actual normalized Abel class detects morphisms from every reduced
test scheme. Only residue-field tests, not a Picard representing witness,
are used to prove this injectivity. -/
theorem pointClass_injective_of_isReduced (T : FScheme k) [IsReduced T.left] :
    Function.Injective (pointClass T) := by
  let : SmoothOfRelativeDimension 1 X.hom := hX.smooth
  let : IsProper X.hom := hX.proper
  intro f g hfg
  apply Over.OverMorphism.ext
  apply ext_of_fromSpecResidueField_eq f.left g.left X.hom Set.univ dense_univ
  · intro t _
    let K := T.left.residueField t
    let s : Spec (.of K) ⟶ Base k := T.left.fromSpecResidueField t ≫ T.hom
    let q : Over.mk s ⟶ T := Over.homMk (T.left.fromSpecResidueField t)
    have hc : pointClass (Over.mk s) (q ≫ f) = pointClass (Over.mk s) (q ≫ g) := by
      rw [Curve.Abel.degreeZeroAbelClass_naturality,
        Curve.Abel.degreeZeroAbelClass_naturality, hfg]
    have he : q ≫ f = q ≫ g :=
      Curve.Abel.normalizedAbelClass_field_injective hnormal hcomp hreg hclosed hdim hprod
        htensor hcartier hbase hdivisor hnorm hgenus hrr hvanish hhigher X hX o.left (Over.w o)
        hg K s (congrArg Subtype.val hc)
    exact congrArg Over.Hom.left he
  · exact (Over.w f).trans (Over.w g).symm

variable (hregular : FibrewiseRegularLineBundle.{u})
variable (hlocal : SmoothRelativeCartierLocality.{u})
variable (G : Grp (FScheme k)) (hG : Curve.Properties G.X)
variable (hgenusOne : coherentGenus k G.X = 1)

local notation "groupClass" => Curve.Abel.degreeZeroAbelClass hnormal hcomp hreg hclosed hdim
  hprod htensor G.X hG hcartier hdivisor hbase (Over.Hom.left η[G.X]) (Over.w η[G.X])

/-- The constant identity point has zero normalized Abel class. -/
theorem pointClass_one (T : FScheme k) : groupClass T (1 : T ⟶ G.X) = 0 := by
  convert Curve.Abel.degreeZeroAbelClass_origin hnormal hcomp hreg hclosed hdim hprod htensor
    G.X hG hcartier hdivisor hbase η[G.X].left (Over.w η[G.X]) T using 1
  congr 1

include hnorm hgenus hrr hvanish hhigher hregular hlocal hgenusOne in
/-- Over an algebraically closed field, the Abel class of the literal group
multiplication is the sum of the two projection classes. The evaluation
divisor constructs a candidate sum map; proper product rigidity identifies
that map with the given multiplication. -/
theorem pointClass_multiplication_of_isAlgClosed [IsAlgClosed k] :
    groupClass (G.X ⊗ G.X) μ[G.X] =
      groupClass (G.X ⊗ G.X) (fst G.X G.X) +
        groupClass (G.X ⊗ G.X) (snd G.X G.X) := by
  let : SmoothOfRelativeDimension 1 G.X.hom := hG.smooth
  let : Smooth G.X.hom := SmoothOfRelativeDimension.smooth 1 G.X.hom
  let : IsProper G.X.hom := hG.proper
  let : GeometricallyIntegral G.X.hom := curveProperties_geometricallyIntegral hnormal hcomp hG
  let : IsIntegral G.X.left := curveProperties_isIntegral hnormal hcomp hG
  let : IsLocallyNoetherian G.X.left := LocallyOfFiniteType.isLocallyNoetherian G.X.hom
  have : IsIntegral (G.X ⊗ G.X).left := by dsimp; infer_instance
  have : IsReduced (𝟙_ (FScheme k) ⊗ G.X).left := by dsimp; infer_instance
  have : IsReduced (G.X ⊗ 𝟙_ (FScheme k)).left := by dsimp; infer_instance
  have : LocallyOfFiniteType (G.X ⊗ G.X).hom := by
    change LocallyOfFiniteType (pullback.fst G.X.hom G.X.hom ≫ G.X.hom)
    infer_instance
  have : IsLocallyNoetherian (G.X ⊗ G.X).left :=
    LocallyOfFiniteType.isLocallyNoetherian (G.X ⊗ G.X).hom
  let a := groupClass (G.X ⊗ G.X) (fst G.X G.X) +
    groupClass (G.X ⊗ G.X) (snd G.X G.X)
  let c : G.X ⊗ G.X ⟶ G.X := Curve.Abel.inverseCandidate hnormal hcomp hreg hclosed hdim
    hprod htensor hcartier hbase hdivisor hnorm hgenus hrr hvanish hhigher G.X hG η[G.X].left
    (Over.w η[G.X]) hgenusOne (G.X ⊗ G.X) a hregular hlocal
  have hc : groupClass (G.X ⊗ G.X) c = a :=
    Curve.Abel.inverseCandidate_class hnormal hcomp hreg hclosed hdim hprod htensor hcartier
      hbase hdivisor hnorm hgenus hrr hvanish hhigher G.X hG η[G.X].left (Over.w η[G.X])
      hgenusOne (G.X ⊗ G.X) a hregular hlocal
  have hl : (η[G.X] ▷ G.X) ≫ c = (λ_ G.X).hom := by
    apply pointClass_injective_of_isReduced hnormal hcomp hreg hclosed hdim hprod htensor
      hcartier hbase hdivisor hnorm hgenus hrr hvanish hhigher G.X hG η[G.X] hgenusOne
    rw [Curve.Abel.degreeZeroAbelClass_naturality, hc]
    dsimp only [a]
    rw [map_add, ← Curve.Abel.degreeZeroAbelClass_naturality,
      ← Curve.Abel.degreeZeroAbelClass_naturality]
    simp only [whiskerRight_fst, whiskerRight_snd, leftUnitor_hom]
    have hz : fst (𝟙_ (FScheme k)) G.X ≫ η[G.X] =
        (1 : 𝟙_ (FScheme k) ⊗ G.X ⟶ G.X) := by
      rw [CategoryTheory.Hom.one_def]
      congr 1
    rw [hz, pointClass_one, zero_add]
  have hr : (G.X ◁ η[G.X]) ≫ c = (ρ_ G.X).hom := by
    apply pointClass_injective_of_isReduced hnormal hcomp hreg hclosed hdim hprod htensor
      hcartier hbase hdivisor hnorm hgenus hrr hvanish hhigher G.X hG η[G.X] hgenusOne
    rw [Curve.Abel.degreeZeroAbelClass_naturality, hc]
    dsimp only [a]
    rw [map_add, ← Curve.Abel.degreeZeroAbelClass_naturality,
      ← Curve.Abel.degreeZeroAbelClass_naturality]
    simp only [whiskerLeft_fst, whiskerLeft_snd, rightUnitor_hom]
    have hz : snd G.X (𝟙_ (FScheme k)) ≫ η[G.X] =
        (1 : G.X ⊗ 𝟙_ (FScheme k) ⟶ G.X) := by
      rw [CategoryTheory.Hom.one_def]
      congr 1
      exact Subsingleton.elim _ _
    rw [hz, pointClass_one, add_zero]
  have he : c = μ[G.X] := by
    apply div_eq_one.mp
    exact PointedMorphism.rigidity_of_integral_tensor_of_isAlgClosed G.X G.X (c / μ[G.X])
      (by simp only [GrpObj.comp_div, hl, MonObj.one_mul, div_self', Hom.one_def])
      (by simp only [GrpObj.comp_div, hr, MonObj.mul_one, div_self', Hom.one_def])
  exact he ▸ hc

include hnorm hgenus hrr hvanish hhigher hregular hlocal hgenusOne in
/-- On every test scheme, the original group operation becomes addition of
the actual normalized Abel classes. No reducedness or Noetherianity is
required of this test scheme. -/
theorem pointClass_mul_of_isAlgClosed [IsAlgClosed k] (T : FScheme k) (f g : T ⟶ G.X) :
    groupClass T (f * g) = groupClass T f + groupClass T g := by
  have h := congrArg
    (Curve.RelativePicard.degreeZeroMap hnormal hcomp hreg hclosed hdim hprod htensor G.X hG
      η[G.X].left (Over.w η[G.X]) (lift f g))
    (pointClass_multiplication_of_isAlgClosed hnormal hcomp hreg hclosed hdim hprod htensor
      hcartier hbase hdivisor hnorm hgenus hrr hvanish hhigher hregular hlocal G hG hgenusOne)
  rw [map_add, ← Curve.Abel.degreeZeroAbelClass_naturality,
    ← Curve.Abel.degreeZeroAbelClass_naturality,
    ← Curve.Abel.degreeZeroAbelClass_naturality] at h
  simpa only [lift_fst, lift_snd, Hom.mul_def] using h

include hnorm hgenus hrr hvanish hhigher hregular hlocal hgenusOne in
/-- Literal powers of scheme-valued points induce integer multiplication of
their Abel classes, over every algebraically closed base field. -/
theorem pointClass_pow_of_isAlgClosed [IsAlgClosed k] (T : FScheme k)
    (f : T ⟶ G.X) (n : ℕ) : groupClass T (f ^ n) = n • groupClass T f := by
  induction n with
  | zero =>
    rw [pow_zero, pointClass_one, zero_nsmul]
  | succ n ih =>
    rw [pow_succ, pointClass_mul_of_isAlgClosed hnormal hcomp hreg hclosed hdim hprod htensor
      hcartier hbase hdivisor hnorm hgenus hrr hvanish hhigher hregular hlocal G hG hgenusOne,
      ih, add_nsmul, one_nsmul]

end AlgebraicGeometry.Scheme.Group.PointDivisor

namespace AlgebraicGeometry.Scheme.Group.PointDivisor

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (G : Grp (FScheme k)) (hG : Curve.Properties G.X)

/-- The existing normalized Abel class with its native geometric suppliers.
This is the same actual degree-zero Picard class, with no representation data. -/
abbrev degreeZeroPointClass (T : FScheme k) (f : T ⟶ G.X) :=
  Curve.Abel.degreeZeroAbelClass smoothFieldNormality normalComponentsOpen smoothFieldRegularity
    smoothClosedPointDimension smoothFieldDimension Curve.Picard.Degree.properCurveProductFormula
    moduleTensorPullback G.X hG Curve.Abel.FiniteCartierDegree.finiteCartierIdealDegree
    smoothRelativeDivisorIdeal relativeCartierIdealBaseChange η[G.X].left (Over.w _) T f

/-- Actual group multiplication maps to addition of native Abel classes,
using the proved geometric, cohomological and Cartier suppliers. -/
theorem degreeZeroPointClass_mul [IsAlgClosed k] (hg : coherentGenus k G.X = 1)
    (T : FScheme k) (f g : T ⟶ G.X) :
    degreeZeroPointClass G hG T (f * g) =
      degreeZeroPointClass G hG T f + degreeZeroPointClass G hG T g :=
  pointClass_mul_of_isAlgClosed smoothFieldNormality normalComponentsOpen smoothFieldRegularity
    smoothClosedPointDimension smoothFieldDimension Curve.Picard.Degree.properCurveProductFormula
    moduleTensorPullback Curve.Abel.FiniteCartierDegree.finiteCartierIdealDegree
    relativeCartierIdealBaseChange smoothRelativeDivisorIdeal
    Curve.Picard.NormDegree.finiteMorphismNormOrder
    Cohomology.properStructureCohomologyBaseChange lineBundleRiemannRoch
    lineBundleHighDegreeVanishing Cohomology.noetherianSheafCohomologyVanishing
    fibrewiseRegularLineBundle smoothRelativeCartierLocality G hG hg T f g

/-- The literal multiplication power induces scalar multiplication of the
actual native Abel class on every test scheme. -/
theorem degreeZeroPointClass_pow [IsAlgClosed k] (hg : coherentGenus k G.X = 1)
    (T : FScheme k) (f : T ⟶ G.X) (n : ℕ) :
    degreeZeroPointClass G hG T (f ^ n) = n • degreeZeroPointClass G hG T f :=
  pointClass_pow_of_isAlgClosed smoothFieldNormality normalComponentsOpen smoothFieldRegularity
    smoothClosedPointDimension smoothFieldDimension Curve.Picard.Degree.properCurveProductFormula
    moduleTensorPullback Curve.Abel.FiniteCartierDegree.finiteCartierIdealDegree
    relativeCartierIdealBaseChange smoothRelativeDivisorIdeal
    Curve.Picard.NormDegree.finiteMorphismNormOrder
    Cohomology.properStructureCohomologyBaseChange lineBundleRiemannRoch
    lineBundleHighDegreeVanishing Cohomology.noetherianSheafCohomologyVanishing
    fibrewiseRegularLineBundle smoothRelativeCartierLocality G hG hg T f n

end AlgebraicGeometry.Scheme.Group.PointDivisor
