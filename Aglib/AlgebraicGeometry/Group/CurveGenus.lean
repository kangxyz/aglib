/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.MultiplicationDegree
public import Aglib.AlgebraicGeometry.Curves.RiemannHurwitz.CanonicalDegree
public import Aglib.AlgebraicGeometry.Modules.Differentials.Diagonal

/-!
# Native coherent genus of a smooth proper group curve

The difference map identifies the diagonal ideal with the pullback of the
identity ideal. Restricting this equality to the diagonal proves that the actual
diagonal conormal line bundle has zero Picard class, without a genus assumption.
The canonical conormal comparison and native canonical-degree formula then prove
`Curve.coherentGenus k G.X = 1` for a smooth proper geometrically connected group curve.
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
open AlgebraicGeometry.Scheme.Modules.Differentials

universe u

namespace AlgebraicGeometry.Scheme.Group

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (G : Grp (FScheme k))
variable [SmoothOfRelativeDimension 1 G.X.hom] [IsSeparated G.X.hom]

/-- The actual diagonal ideal restricted to the diagonal. -/
def diagonalConormalLineBundle : LineBundle G.X.left :=
  pullbackLineBundle (pullback.diagonal G.X.hom)
    (diagonalIdealLineBundle smoothRelativeDivisorIdeal G.X.hom)

/-- The diagonal conormal line bundle of the original smooth group curve is trivial
in its native Picard group. This requires no properness or genus hypothesis. -/
theorem diagonalConormalLineBundle_class_eq_zero :
    classOf G.X.left (diagonalConormalLineBundle G) = 0 := by
  change pullbackClass (lift (𝟙 G.X) (𝟙 G.X)).left
    (classOf _ (diagonalIdealLineBundle smoothRelativeDivisorIdeal G.X.hom)) = 0
  have he := congrArg
    (fun a : PicardGroup (G.X ⊗ G.X).left =>
      pullbackClass (lift (𝟙 G.X) (𝟙 G.X)).left a)
    (Multiplication.pullback_identityIdealClass_difference G)
  apply he.symm.trans
  rw [← pullbackClass_comp, ← Over.comp_left]
  have hd : lift (𝟙 G.X) (𝟙 G.X) ≫ Multiplication.difference G =
      (1 : G.X ⟶ G.X) := by
    simp only [Multiplication.difference, GrpObj.comp_div, lift_fst, lift_snd, div_self']
  rw [hd, Multiplication.pullback_identityIdealClass_one]

/-- Native canonical degree reduces genus one to the actual diagonal-conormal
comparison. The comparison is an explicit remaining geometric hypothesis. -/
theorem coherentGenus_eq_one_of_diagonalConormalIso (hG : Curve.Properties G.X)
    (e : (diagonalConormalLineBundle G).val ≅ differentialSheaf G.X) :
    Curve.coherentGenus k G.X = 1 := by
  have hclass : classOf G.X.left (Curve.canonicalLineBundle G.X hG.smooth) = 0 := by
    have he : classOf G.X.left (Curve.canonicalLineBundle G.X hG.smooth) =
        classOf G.X.left (diagonalConormalLineBundle G) := Quotient.sound ⟨e.symm⟩
    exact he.trans (diagonalConormalLineBundle_class_eq_zero G)
  have hdegree := Curve.curveDegree_canonical smoothFieldNormality normalComponentsOpen
    smoothFieldRegularity smoothClosedPointDimension smoothFieldDimension
    Curve.Picard.Degree.properCurveProductFormula G.X hG Curve.smoothCanonicalDegree
  rw [hclass, map_zero] at hdegree
  omega


/-- The original diagonal conormal line bundle is the native field differential sheaf. -/
def diagonalConormalIso : (diagonalConormalLineBundle G).val ≅ differentialSheaf G.X :=
  Diagonal.conormalIsoOfAffineBase (.of k) G.X.hom ≪≫
    Curve.Duality.relativeFieldDifferentialIso G.X

omit [SmoothOfRelativeDimension 1 G.X.hom] [IsSeparated G.X.hom] in
/-- Every smooth proper geometrically connected group curve has native coherent genus one. -/
theorem coherentGenus_eq_one (hG : Curve.Properties G.X) :
    Curve.coherentGenus k G.X = 1 := by
  let : SmoothOfRelativeDimension 1 G.X.hom := hG.smooth
  let : IsProper G.X.hom := hG.proper
  exact coherentGenus_eq_one_of_diagonalConormalIso G hG (diagonalConormalIso G)

end AlgebraicGeometry.Scheme.Group
