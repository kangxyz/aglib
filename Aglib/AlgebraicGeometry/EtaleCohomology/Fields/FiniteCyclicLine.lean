/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.SylowLine
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.FiniteSetRepresentation
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.Algebra.Category.Grp.AB

/-! # Prime-to-p cyclic subobjects of genuine finite locally constant sheaves

The original finite coefficient is represented by its proved finite-etale
group scheme. The genuine prime-to-p cyclic line is transported back through
that exact representing isomorphism and the original inverse-image functor.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.FiniteEtale.FieldGalois.OverRing

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Fields

open MarkedCoefficients

universe u

attribute [local instance] hasSheafifyLarge

/-- Every nontrivial finite prime-torsion local system acquires an actual
constant prime-cyclic subobject over an actual prime-to-p field extension. -/
theorem exists_primeTo_field_cyclic_mono_of_finiteLocallyConstant
    (E Ω : Type u) [Field E] [Field Ω] [Algebra E Ω]
    [IsGalois E Ω] [IsSepClosed Ω]
    (F : AbelianSheaf.{u, u + 1} (Spec (.of E)))
    (hF : IsFiniteLocallyConstant F) {p : ℕ} [Fact p.Prime]
    (hp : KilledBy p F) [Nontrivial (coefficientFiber (basePoint E Ω) F)] :
    ∃ M : IntermediateField E Ω, FiniteDimensional E M ∧
      (Module.finrank E M).Coprime p ∧
      ∃ q : ConstantFinite.coefficient (ULift.{u} (ZMod p)) (Spec (.of M)) ⟶
        (inverseImage (Spec.algebraMap E M)).obj F, Mono q := by
  let R := CoefficientRepresentation.ofFiniteLocallyConstant F (stacks03RV _) hF
  let s := basePoint E Ω
  let e := R.fiberPointEquiv s
  let : Nontrivial (PointModule s R.group) := e.symm.toEquiv.nontrivial
  let T := (Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})
  let : HasFilteredColimitsOfSize.{u, u} AddCommGrpCat.{u + 1} :=
    hasFilteredColimitsOfSize_of_univLE.{u, u, u + 1, u + 1}
  let : AB5OfSize.{u, u} AddCommGrpCat.{u + 1} :=
    AB5OfSize_of_univLE.{u, u, u + 1, u + 1} _
  let : T.Additive := Functor.additive_of_preserves_binary_products T
  have hf (a : coefficientFiber s F) : p • a = 0 := by
    have h := congrArg (fun q : F ⟶ F => T.map q) hp
    rw [Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero] at h
    have hh := congrArg (fun q : T.obj F ⟶ T.obj F => q a) h
    simpa using hh
  have hp' (a : PointModule s R.group) : p • a = 0 := by
    apply e.symm.injective
    rw [map_nsmul, map_zero]
    exact hf (e.symm a)
  obtain ⟨M, hfin, hdegree, q, hq⟩ := exists_primeTo_field_cyclic_mono E Ω R.group hp'
  let := hq
  refine ⟨M, hfin, hdegree,
    q ≫ (inverseImage (Spec.algebraMap E M)).map R.iso.hom, ?_⟩
  infer_instance

end AlgebraicGeometry.Scheme.EtaleCohomology.Fields
