/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ResidueField.Constants
public import Aglib.AlgebraicGeometry.ResidueField.CurveCoordinates

/-! # Structural constant-field actions in actual curve residue fields

The affine-chart residue isomorphism respects the original structure morphism.
This gives the algebraic/function-field dichotomy on the original residue field,
not just on an abstract isomorphic field with an unrelated constant-field map.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k]

/-- Naturality of the actual residue constants, without finiteness or point restrictions. -/
theorem residueConstants_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    (p : Y ⟶ Spec (.of k)) (x : X) :
    (f.residueFieldMap x).hom.comp (residueConstants Y p (f x)) =
      residueConstants X (f ≫ p) x := by
  have he : Spec.preimage (Y.fromSpecResidueField (f x) ≫ p) ≫ f.residueFieldMap x =
      Spec.preimage (X.fromSpecResidueField x ≫ (f ≫ p)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, ← Category.assoc,
      Hom.SpecMap_residueFieldMap_fromSpecResidueField, Category.assoc]
  exact congrArg CommRingCat.Hom.hom he

/-- The native affine residue isomorphism preserves the displayed structural scalars. -/
def specResidueAlgebraEquiv (R : CommRingCat.{u}) (p : Spec R ⟶ Spec (.of k))
    (x : Spec R) :
    letI := (Spec.preimage p).hom.toAlgebra
    letI := residueAlgebra (Spec R) p x
    (Spec R).residueField x ≃ₐ[k] x.asIdeal.ResidueField := by
  letI := (Spec.preimage p).hom.toAlgebra
  letI := residueAlgebra (Spec R) p x
  let e := (Spec.residueFieldIso R x).commRingCatIsoToRingEquiv
  have he : Spec.preimage p ≫ CommRingCat.ofHom (algebraMap R x.asIdeal.ResidueField) ≫
      (Spec.residueFieldIso R x).inv =
      Spec.preimage ((Spec R).fromSpecResidueField x ≫ p) := by
    apply Spec.map_injective
    simp only [Spec.map_comp, Spec.map_preimage]
    rw [Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
  refine { e with commutes' := ?_ }
  intro a
  have ha := congrArg (fun f : CommRingCat.of k ⟶ (Spec R).residueField x => f a) he
  have ha' : e.symm (algebraMap k x.asIdeal.ResidueField a) =
      algebraMap k ((Spec R).residueField x) a := ha
  rw [← ha']
  exact e.apply_symm_apply _

/-- Actual residue fields on finite-type curves are algebraic or algebraic over
one rational variable, compatibly with the original structural constant map. -/
theorem residueField_algebraic_or_ratFunc (X : Scheme.{u}) (p : X ⟶ Spec (.of k))
    [LocallyOfFiniteType p] (hdim : topologicalKrullDim X ≤ 1) (x : X) :
    letI := residueAlgebra X p x
    Algebra.IsAlgebraic k (X.residueField x) ∨
      ∃ a : Algebra (RatFunc k) (X.residueField x),
        letI := a
        Algebra.IsAlgebraic (RatFunc k) (X.residueField x) ∧
          IsScalarTower k (RatFunc k) (X.residueField x) := by
  obtain ⟨R, f, y, hf, hxy, hft, hd, _⟩ :=
    exists_curve_residueField_coordinates X p hdim x
  let : IsOpenImmersion f := hf
  subst x
  let := residueAlgebra X p (f y)
  let := residueAlgebra (Spec R) (f ≫ p) y
  let := (Spec.preimage (f ≫ p)).hom.toAlgebra
  let : Algebra.FiniteType k R := hft
  let ef : X.residueField (f y) ≃ₐ[k] (Spec R).residueField y :=
    { (asIso (f.residueFieldMap y)).commRingCatIsoToRingEquiv with
      commutes' := fun a => congrArg (fun h : k →+* (Spec R).residueField y => h a)
        (residueConstants_naturality f p y) }
  let e : X.residueField (f y) ≃ₐ[k] y.asIdeal.ResidueField :=
    ef.trans (specResidueAlgebraEquiv R (f ≫ p) y)
  rcases Ideal.residueField_algebraic_or_ratFunc_of_dim_le_one k R y.asIdeal hd with h | ⟨a, ha, ht⟩
  · left
    let := h
    exact e.symm.isAlgebraic
  · right
    let := a
    let := ha
    let := ht
    let b : Algebra (RatFunc k) (X.residueField (f y)) :=
      (e.symm.toRingHom.comp (algebraMap (RatFunc k) y.asIdeal.ResidueField)).toAlgebra
    refine ⟨b, ?_⟩
    let := b
    have ee : X.residueField (f y) ≃ₐ[RatFunc k] y.asIdeal.ResidueField :=
      { e.toRingEquiv with commutes' := fun z => e.apply_symm_apply _ }
    refine ⟨ee.symm.isAlgebraic, ?_⟩
    exact IsScalarTower.of_algebraMap_eq (fun z => by
      change algebraMap k (X.residueField (f y)) z =
        e.symm (algebraMap (RatFunc k) y.asIdeal.ResidueField (algebraMap k (RatFunc k) z))
      rw [← IsScalarTower.algebraMap_apply k (RatFunc k) y.asIdeal.ResidueField]
      exact (e.symm.commutes z).symm)

end AlgebraicGeometry.Scheme
