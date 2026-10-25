/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.FiniteGaloisCover
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.FiniteCoefficientPullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.ConstantFinite.Basic
public import Mathlib.Algebra.Group.Shrink

/-! # Actual finite Galois constant trivializations at a generic field

A finite locally constant coefficient on a field spectrum becomes an actual
finite constant sheaf over a produced finite Galois intermediate field. The
finite value is resized to the scheme universe, and the original inverse-image
composition and constant transports are retained. No perfection or coefficient
order condition is used.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators

universe u

attribute [local instance] hasSheafifyLarge

/-- A produced finite Galois field and a small finite abelian constant value,
with the original coefficient inverse image and an actual trivialization. -/
structure FiniteGaloisConstantTrivialization (K : Type u) [Field K]
    (F : AbelianSheaf.{u, u + 1} (Spec (.of K))) where
  /-- The actual finite Galois intermediate field. -/
  extension : FiniteGaloisIntermediateField K (SeparableClosure K)
  /-- The finite value lies in the original scheme universe. -/
  value : AddCommGrpCat.{u}
  /-- Its underlying group is finite. -/
  finite_value : Finite value
  /-- The original inverse image is the actual finite constant coefficient. -/
  iso : (inverseImage (Spec.algebraMap K extension)).obj F ≅
    ConstantFinite.coefficient value (Spec (.of extension))

/-- Finite local constancy supplies an actual finite Galois constant
trivialization, including its small finite abelian value. -/
def finiteGaloisConstantTrivialization (K : Type u) [Field K]
    (F : AbelianSheaf.{u, u + 1} (Spec (.of K))) (hF : IsFiniteLocallyConstant F) :
    FiniteGaloisConstantTrivialization K F := by
  apply Classical.choice
  obtain ⟨t⟩ := hF
  obtain ⟨i, y, _⟩ := t.covers (default : Spec (.of K))
  have : Etale (t.chart i).hom := (t.chart i).prop
  obtain ⟨L, s, hs⟩ := Fields.exists_finiteGalois_point K (t.chart i).hom y
  let A := t.value i
  have : Finite A := t.finite_value i
  let := Fintype.ofFinite A
  have : Small.{u} A := Small.mk'
    ((Fintype.equivFin A).trans (Equiv.ulift.{u}).symm)
  let B : AddCommGrpCat.{u} := AddCommGrpCat.of (Shrink.{u} A)
  have : Finite B := Finite.of_equiv A (equivShrink A)
  let e : ConstantFinite.value B ≅ A :=
    AddEquiv.toAddCommGrpIso (AddEquiv.ulift.trans (Shrink.addEquiv (α := A)))
  refine ⟨{ extension := L, value := B, finite_value := inferInstance, iso := ?_ }⟩
  exact eqToIso (congrArg (fun q => (inverseImage q).obj F) hs.symm) ≪≫
    (inverseImageComp (t.chart i).hom s).app F ≪≫
      (inverseImage s).mapIso (t.trivialization i) ≪≫
      (inverseImageConstantIso s).app A ≪≫
      (constantSheaf (Scheme.smallEtaleTopology (Spec (.of L)))
        AddCommGrpCat.{u + 1}).mapIso e.symm

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators
