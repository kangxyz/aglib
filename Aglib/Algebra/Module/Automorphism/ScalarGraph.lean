/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Module.CommutingAutomorphisms.LocalLength
public import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
Actual one-torus action and the right scalar graph in the maintained two-torus.
No comparison map or product-matching proposition is supplied as data.
-/
/-!
## Migration source

Native extraction from `lean/R5Lab/Aglib/Algebra/Module/Automorphism/ScalarGraph.lean` at R5
revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`bdb81aeed078b729fdf1a13a5f964e43417275c0d744a29372743b54d4c5da6c`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped _root_.TensorProduct
namespace Module.Automorphism.ScalarGraph
open Module.CommutingAutomorphisms CommutingAutomorphisms.LaurentSupport
universe u
variable {R : Type u} [CommRing R]

/-- The character group of the one-dimensional torus, written multiplicatively. -/
abbrev OneCharacter := Multiplicative ℤ
/-- The one-variable Laurent polynomial algebra over `R`. -/
abbrev OneLaurent (R : Type u) [CommRing R] := MonoidAlgebra R OneCharacter

/-- The character action sending an integer exponent to the corresponding power of `X.a`. -/
def oneExponent (X : Object R) : OneCharacter →* (X.carrier ≃ₗ[R] X.carrier) where
  toFun m := X.a ^ m.toAdd
  map_one' := by simp
  map_mul' m n := by change X.a ^ (m.toAdd+n.toAdd) = _; exact zpow_add _ _ _

/-- The Laurent polynomial representation obtained by evaluating the variable at `X.a`. -/
def oneRepresentation (X : Object R) : OneLaurent R →ₐ[R] Module.End R X.carrier :=
  MonoidAlgebra.lift R _ OneCharacter
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (oneExponent X))

@[simp] theorem oneRepresentation_single (X : Object R) (m : OneCharacter) (r : R) :
    oneRepresentation X (MonoidAlgebra.single m r) = r • (X.a ^ m.toAdd).toLinearMap := by
  simp [oneRepresentation, oneExponent, MonoidAlgebra.lift_single]

/-- The ideal of Laurent polynomials acting as zero on `X`. -/
def oneSupportIdeal (X : Object R) : Ideal (OneLaurent R) :=
  RingHom.ker (oneRepresentation X)
/-- The quotient of the Laurent algebra by the annihilator of its action on `X`. -/
abbrev OneSupport (X : Object R) := OneLaurent R ⧸ oneSupportIdeal X

/-- The literal graph pullback on each character: x^i y^j ↦ f^j x^i. -/
def graphExponent (f : Rˣ) : Character →* OneLaurent R where
  toFun m := MonoidAlgebra.single (Multiplicative.ofAdd m.toAdd.1) (↑(f ^ m.toAdd.2) : R)
  map_one' := by simp [MonoidAlgebra.one_def]
  map_mul' m n := by
    change MonoidAlgebra.single (Multiplicative.ofAdd (m.toAdd.1+n.toAdd.1))
      (↑(f ^ (m.toAdd.2+n.toAdd.2)) : R) = _
    rw [zpow_add]
    simp [MonoidAlgebra.single_mul_single]

/-- The Laurent algebra map substituting the unit `f` for the second coordinate. -/
def graphMap (f : Rˣ) : Laurent R →ₐ[R] OneLaurent R :=
  MonoidAlgebra.lift R _ Character (graphExponent f)

@[simp] theorem graphMap_single (f : Rˣ) (m : Character) (r : R) :
    graphMap f (MonoidAlgebra.single m r) =
      MonoidAlgebra.single (Multiplicative.ofAdd m.toAdd.1) (r * (↑(f^m.toAdd.2) : R)) := by
  simp [graphMap, graphExponent, MonoidAlgebra.lift_single]

/-- The inclusion of one-variable characters as the first coordinate of two-variable characters. -/
def includeExponent : OneCharacter →* Character where
  toFun m := Multiplicative.ofAdd (m.toAdd, 0)
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The inclusion of the one-variable Laurent algebra into the first Laurent coordinate. -/
def firstInclude (R : Type u) [CommRing R] : OneLaurent R →ₐ[R] Laurent R :=
  MonoidAlgebra.mapDomainAlgHom R R includeExponent

@[simp] theorem graphMap_firstInclude (f : Rˣ) (p : OneLaurent R) :
    graphMap f (firstInclude R p) = p := by
  induction p using MonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp [hp, hq]
  | single m r => simp [firstInclude, includeExponent]

theorem graphMap_surjective (f : Rˣ) : Function.Surjective (graphMap f) :=
  fun p => ⟨firstInclude R p, graphMap_firstInclude f p⟩

@[simp] theorem graphMap_first (f : Rˣ) :
    graphMap f (firstCoordinate R) = MonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ)) 1 := by
  simp [firstCoordinate, monomial]

@[simp] theorem graphMap_second (f : Rˣ) :
    graphMap f (secondCoordinate R) = algebraMap R (OneLaurent R) (f : R) := by
  simp [secondCoordinate, monomial, MonoidAlgebra.coe_algebraMap]

/-- Same original carrier with (A,f·identity), preserving the coordinate order. -/
def graphObject (X : Object R) (f : Rˣ) : CommutingAutomorphisms.Object R where
  carrier := X.carrier
  a := X.a
  b := LinearEquiv.smulOfUnit f
  commute x := by
    change X.a ((f : R) • x) = (f : R) • X.a x
    exact X.a.map_smul (f : R) x

/-- The actual tensor module with the right scalar is its original module. -/
def tensorGraphIso (X : Object R) (f : Rˣ) :
    CommutingAutomorphisms.Object.Iso (X.tensor (Object.unit f)) (graphObject X f) where
  linearEquiv := TensorProduct.rid R X.carrier
  commute_a z := by
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp [hx, hy]
    | tmul x r =>
      change (TensorProduct.rid R X.carrier) (X.a x ⊗ₜ[R] r) =
        X.a ((TensorProduct.rid R X.carrier) (x ⊗ₜ[R] r))
      simp
  commute_b z := by
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp [hx, hy]
    | tmul x r =>
      change (TensorProduct.rid R X.carrier) (x ⊗ₜ[R] ((f : R) * r)) =
        (f : R) • ((TensorProduct.rid R X.carrier) (x ⊗ₜ[R] r))
      simp [mul_smul]

theorem graph_b_zpow (X : Object R) (f : Rˣ) (k : ℤ) (x : X.carrier) :
    ((graphObject X f).b^k) x = (↑(f^k) : R) • x := by
  change ((DistribMulAction.toModuleAut R X.carrier f)^k) x = _
  rw [← map_zpow]
  rfl

/-- The entire maintained Laurent action factors through the graph pullback. -/
theorem representation_graph (X : Object R) (f : Rˣ) (p : Laurent R) :
    representation (graphObject X f) p = oneRepresentation X (graphMap f p) := by
  induction p using MonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp [hp, hq]
  | single m r =>
    rw [representation_single, graphMap_single, oneRepresentation_single]
    ext x
    change r • ((X.a^m.toAdd.1) (((graphObject X f).b^m.toAdd.2) x)) = _
    rw [graph_b_zpow, (X.a^m.toAdd.1).map_smul, mul_smul]
    rfl

/-- Exact equality of original annihilators, not only one coordinate relation. -/
theorem supportIdeal_graph (X : Object R) (f : Rˣ) :
    supportIdeal (graphObject X f) = (oneSupportIdeal X).comap (graphMap f).toRingHom := by
  ext p
  change representation (graphObject X f) p = 0 ↔ oneRepresentation X (graphMap f p) = 0
  rw [representation_graph]

theorem supportIdeal_tensor_graph (X : Object R) (f : Rˣ) :
    supportIdeal (X.tensor (Object.unit f)) =
      (oneSupportIdeal X).comap (graphMap f).toRingHom :=
  (CommutingAutomorphisms.supportIdeal_iso (tensorGraphIso X f)).trans (supportIdeal_graph X f)

/-- Scalar-graph substitution followed by the quotient onto the one-variable support algebra. -/
def graphToSupport (X : Object R) (f : Rˣ) : Laurent R →ₐ[R] OneSupport X :=
  (Ideal.Quotient.mkₐ R (oneSupportIdeal X)).comp (graphMap f)

theorem graphToSupport_surjective (X : Object R) (f : Rˣ) :
    Function.Surjective (graphToSupport X f) :=
  Ideal.Quotient.mk_surjective.comp (graphMap_surjective f)

theorem graphToSupport_kernel (X : Object R) (f : Rˣ) :
    RingHom.ker (graphToSupport X f) = supportIdeal (graphObject X f) := by
  rw [supportIdeal_graph]
  ext p
  exact Ideal.Quotient.eq_zero_iff_mem

/-- The original graph support algebra is exactly the one-torus support. -/
def graphSupportEquiv (X : Object R) (f : Rˣ) :
    Support (graphObject X f) ≃ₐ[R] OneSupport X :=
  (Ideal.quotientEquivAlgOfEq R (graphToSupport_kernel X f).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (graphToSupport_surjective X f))

@[simp] theorem graphSupportEquiv_mk (X : Object R) (f : Rˣ) (p : Laurent R) :
    graphSupportEquiv X f (Ideal.Quotient.mk (supportIdeal (graphObject X f)) p) =
      Ideal.Quotient.mk (oneSupportIdeal X) (graphMap f p) := rfl

/-- The actual tensor-object support algebra, with no substitute module. -/
def tensorSupportEquiv (X : Object R) (f : Rˣ) :
    Support (X.tensor (Object.unit f)) ≃ₐ[R] OneSupport X :=
  (Ideal.quotientEquivAlgOfEq R
    (CommutingAutomorphisms.supportIdeal_iso (tensorGraphIso X f))).trans
    (graphSupportEquiv X f)

end Module.Automorphism.ScalarGraph
