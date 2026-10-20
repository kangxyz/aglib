/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.FundamentalGroup.Field.RootActions
public import Aglib.AlgebraicGeometry.FundamentalGroup.Field.CyclotomicCharacter

/-!
# Fundamental-group action on the actual root module

Source: `R5Lab.Aglib.RingTheory.RootsOfUnity.FundamentalGroupAction`,
revision `f8a3314ddecffcada2ec721d26d56a937bed9690`. Exact field, action, embedding and
explicit-data hypotheses are retained. Native objects and maps are reused.
-/

@[expose] public section

noncomputable section
open _root_.AlgebraicGeometry.Scheme.FiniteEtale
open _root_.AlgebraicGeometry.Scheme.FiniteEtale.Cyclotomic
namespace AlgebraicGeometry.Scheme.FiniteEtale.Cyclotomic.RootCoordinates
variable {F : Type} [Field F] [CharZero F]

variable (n : ℕ) [NeZero n]

@[instance_reducible] instance arithmeticRootAction : DistribMulAction
  (_root_.AlgebraicGeometry.Scheme.FiniteEtale.Cyclotomic.Coefficients.ArithmeticGroup F)
  (RootModule n F) where
  smul g z :=
    _root_.AlgebraicGeometry.Scheme.FiniteEtale.Cyclotomic.TensorActions.rootGaloisLinear F n
    ((_root_.AlgebraicGeometry.Scheme.FiniteEtale.FieldGalois.fundamentalGroupContinuousEquiv
      F).symm g) z
  one_smul z := by
    apply (_root_.AlgebraicGeometry.Scheme.FiniteEtale.Cyclotomic.RootCoordinates.rootCoordinate
      n F).injective
    change _root_.AlgebraicGeometry.Scheme.FiniteEtale.Cyclotomic.RootCoordinates.rootCoordinate n F
      (_root_.AlgebraicGeometry.Scheme.FiniteEtale.Cyclotomic.TensorActions.rootGaloisLinear F n
((_root_.AlgebraicGeometry.Scheme.FiniteEtale.FieldGalois.fundamentalGroupContinuousEquiv
          F).symm 1) z) = _
    simp only
      [_root_.AlgebraicGeometry.Scheme.FiniteEtale.Cyclotomic.TensorActions.rootGalois_coordinate,
      map_one, Units.val_one, _root_.one_mul]
  mul_smul g h z := by
    apply (_root_.AlgebraicGeometry.Scheme.FiniteEtale.Cyclotomic.RootCoordinates.rootCoordinate
      n F).injective
    change _root_.AlgebraicGeometry.Scheme.FiniteEtale.Cyclotomic.RootCoordinates.rootCoordinate n F
      (_root_.AlgebraicGeometry.Scheme.FiniteEtale.Cyclotomic.TensorActions.rootGaloisLinear F n
((_root_.AlgebraicGeometry.Scheme.FiniteEtale.FieldGalois.fundamentalGroupContinuousEquiv
          F).symm (g * h)) z) =
      _root_.AlgebraicGeometry.Scheme.FiniteEtale.Cyclotomic.RootCoordinates.rootCoordinate n F
        (_root_.AlgebraicGeometry.Scheme.FiniteEtale.Cyclotomic.TensorActions.rootGaloisLinear F n
((_root_.AlgebraicGeometry.Scheme.FiniteEtale.FieldGalois.fundamentalGroupContinuousEquiv
            F).symm g)
          (_root_.AlgebraicGeometry.Scheme.FiniteEtale.Cyclotomic.TensorActions.rootGaloisLinear F n
((_root_.AlgebraicGeometry.Scheme.FiniteEtale.FieldGalois.fundamentalGroupContinuousEquiv
              F).symm h) z))
    simp only
      [_root_.AlgebraicGeometry.Scheme.FiniteEtale.Cyclotomic.TensorActions.rootGalois_coordinate,
      map_mul, Units.val_mul, _root_.mul_assoc]
  smul_zero g := map_zero _
  smul_add g := map_add _

/-- Primitive-root coordinates intertwine the natural root action with chi. -/
theorem rootCoordinate_equivariant (g :
  _root_.AlgebraicGeometry.Scheme.FiniteEtale.Cyclotomic.Coefficients.ArithmeticGroup F) (z :
  RootModule n F) :
    _root_.AlgebraicGeometry.Scheme.FiniteEtale.Cyclotomic.RootCoordinates.rootCoordinate n F (g
      • z) =
      (_root_.AlgebraicGeometry.Scheme.FiniteEtale.Cyclotomic.Coefficients.arithmeticCharacter F
        n g : ZMod n) *
        _root_.AlgebraicGeometry.Scheme.FiniteEtale.Cyclotomic.RootCoordinates.rootCoordinate n
        F z :=
  _root_.AlgebraicGeometry.Scheme.FiniteEtale.Cyclotomic.TensorActions.rootGalois_coordinate F n _ z

end AlgebraicGeometry.Scheme.FiniteEtale.Cyclotomic.RootCoordinates
