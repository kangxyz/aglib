/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Differentials.Basic
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Rank
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/- Interface migration basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original mathematical and construction source identities are retained. -/

/-!
# General geometric properties of the constructed differential sheaf

These two retained families concern the independently constructed universal
Kähler differential sheaf and its canonical map. Neither assumes a curve,
genus, canonical degree, or Riemann–Hurwitz formula.

`SmoothDifferentialRank` is the arbitrary-field, every-relative-dimension
specialization of Stacks 02G1 and 02G2. The pinned mathlib hypothesis is
expressed by standard smooth affine charts; the standard sheaf theorem
identifies their actual differentials with finite local free bases.
`EtaleDifferentialPullback` is Stacks 04BX with identity map on the base field.
The map is identified by `differentialPushforwardMap_d` and
`differentialPullbackMap_adjoint` in `Basic`, giving d(a) ↦ d(f# a).
These primary statements/proofs and visible comments were inspected
2026-10-09. Their full external dependency chains were not independently proved.

Application K2-018#prop:k2018-arithmetic-characters, expose.tex lines 341–445,
source e73d98b1b5c1e5abcdebf7d058e436d792b87982; frozen engineering basis
7f86e4a1763cc4ec35e9b0a8acd659750355a0de and unchanged pins.
-/

@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField
namespace AlgebraicGeometry.Scheme.Modules.Differentials
universe u

/-- General smooth rank theorem on the actual differential sheaf, in all
relative dimensions and over every field. Stacks 02G1/02G2. -/
def SmoothDifferentialRank : Prop :=
  ∀ (F : Type u) [Field F] (X : FScheme F) (n : ℕ),
    SmoothOfRelativeDimension n X.hom →
      AlgebraicGeometry.Scheme.Modules.SheafHasRank (differentialSheaf X) n

/-- General étale invariance of the actual canonical differential map.
Stacks 04BX, with the base identity as the second étale morphism. -/
def EtaleDifferentialPullback : Prop :=
  ∀ (F : Type u) [Field F] (X Y : FScheme F) (f : X ⟶ Y),
    Etale f.left → IsIso (differentialPullbackMap f)

variable {F : Type u} [Field F]

theorem smoothDifferential_finiteLocallyFree
    (hstandard : SmoothDifferentialRank.{u}) (X : FScheme F) (n : ℕ)
    (hX : SmoothOfRelativeDimension n X.hom) :
    AlgebraicGeometry.Scheme.Modules.SheafFiniteLocallyFree (differentialSheaf X) := by
  exact (hstandard F X n hX).isFiniteLocallyFree

/-- The isomorphism is induced by the canonical differential pullback map. -/
def etaleDifferentialIso (hstandard : EtaleDifferentialPullback.{u})
    {X Y : FScheme F} (f : X ⟶ Y) [Etale f.left] :
    (Scheme.Modules.pullback f.left).obj (differentialSheaf Y) ≅ differentialSheaf X := by
  letI := hstandard F X Y f inferInstance
  exact asIso (differentialPullbackMap f)

@[simp]
theorem etaleDifferentialIso_hom (hstandard : EtaleDifferentialPullback.{u})
    {X Y : FScheme F} (f : X ⟶ Y) [Etale f.left] :
    (etaleDifferentialIso hstandard f).hom = differentialPullbackMap f := rfl
end AlgebraicGeometry.Scheme.Modules.Differentials
