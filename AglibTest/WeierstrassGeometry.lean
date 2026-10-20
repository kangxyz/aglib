import Aglib.AlgebraicGeometry.Curves.GenericExtension
import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.PointedGroup
import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.CoordinateGroup
import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.PointedAgreement
import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.VariableChangeChart
import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.FunctionField

/-! Focused checks of the original structural arrows, field maps and point map. -/

noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.OverField
open WeierstrassCurve WeierstrassCurve.Projective

universe u

example {k : Type u} [Field k] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (sx : X ⟶ Spec (.of k)) (sy : Y ⟶ Spec (.of k))
    (hx : IsProper sx) (hs : SmoothOfRelativeDimension 1 sx)
    (hn : NormalStalks X) (hy : IsProper sy)
    (g : Spec X.functionField ⟶ Y)
    (hg : g ≫ sy = X.fromSpecStalk (genericPoint X) ≫ sx) :
    ∃ f : X ⟶ Y, f ≫ sy = sx ∧ X.fromSpecStalk (genericPoint X) ≫ f = g :=
  Scheme.FunctionField.GenericExtension.normalProperCurveGenericExtension
    k X Y sx sy hx hs hn hy g hg

example {k : Type u} [Field k] (W : WeierstrassCurve k) :
    infinitySection W ≫ structureMap W = 𝟙 _ := infinitySection_structure W

example {k K : Type u} [Field k] [Field K] (W : WeierstrassCurve k)
    (f : k →+* K) (hΔ : W.Δ ≠ 0) (P : (W.map f).toAffine.Point) :
    coordinateExtensionEquiv W f hΔ P = coordinatePointExtension W f P := rfl

example {k K : Type u} [Field k] [Field K] (W : WeierstrassCurve k)
    (f : k →+* K) (x y : K) (h : (W.map f).toAffine.Equation x y) :
    affinePointEvalExtension W f x y h (affineX W) = x :=
  affinePointEvalExtension_x W f x y h

example {k : Type u} [Field k] (W : WeierstrassCurve k) (v : VariableChange k) :
    (VariableChange.affineSpecIso W v).hom =
      Spec.map (CommRingCat.ofHom (VariableChange.affineEquiv W v).toRingHom) := rfl

example {k : Type u} [Field k] (W : WeierstrassCurve k) [IsIntegral (scheme W)] :
    affineFunctionFieldEquiv W (functionX W) =
      algebraMap (affineRing W) (FractionRing (affineRing W)) (affineX W) :=
  affineFunctionFieldEquiv_functionX W
