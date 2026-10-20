/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Finite.ClosedPoints
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Degrees, closed fibres and field norms of actual finite morphisms
-/

@[expose] public section


noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Scheme.Hom
universe u
variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
variable (f : X ⟶ Y) [IsDominant f] [IsFinite f]
/-- All actual closed points above a given closed point, without choosing a branch. -/
def ClosedFibre (y : ClosedPoint Y) := {x : ClosedPoint X // Scheme.closedPointMap f x = y}

instance (y : ClosedPoint Y) : Finite (ClosedFibre f y) := by
  have h : {x : ClosedPoint X | Scheme.closedPointMap f x = y}.Finite := by
    apply ((f.finite_preimage_singleton y.val).preimage_embedding
      ⟨Subtype.val, Subtype.val_injective⟩).subset
    intro x hx
    exact congrArg Subtype.val hx
  exact h.to_subtype

noncomputable instance (y : ClosedPoint Y) : Fintype (ClosedFibre f y) := Fintype.ofFinite _

/-- The residue-field algebra structure induced by the residue-field map of `f` at `x`. -/
@[instance_reducible] def relativeResidueAlgebra (x : ClosedPoint X) :
    Algebra (Y.residueField (f x.val)) (X.residueField x.val) :=
  (f.residueFieldMap x.val).hom.toAlgebra

/-- The integer-valued degree is the cast of Mathlib's actual residue degree. -/
abbrev residueDegreeInt (x : ClosedPoint X) : ℤ := (f.residueDegree x.val : ℤ)

/-- The degree of the induced function-field extension, measured by its vector-space dimension. -/
def fieldDegree : ℕ :=
  letI := Scheme.functionFieldMapAlgebra f
  Module.finrank Y.functionField X.functionField

/-- The multiplicative norm for the function-field extension induced by `f`. -/
def fieldNorm : X.functionField →* Y.functionField :=
  letI := Scheme.functionFieldMapAlgebra f
  Algebra.norm Y.functionField

end AlgebraicGeometry.Scheme.Hom

/- Migration source: R5Lab/Aglib/AlgebraicGeometry/Morphisms/Finite/Norm.lean
Frozen packet R5 f8a3314ddecffcada2ec721d26d56a937bed9690.
SHA-256 2d9a905ddd477ec44c015a1008f9d23f5b569e01f7403f0ae8a721d053e44cd1.
Native names and imports replace source wrappers; stated conditions and maps are retained. -/
