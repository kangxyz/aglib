/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.ActualCoverQuotients
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.CoverFiberCoproducts
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.CoverEpimorphisms

/-! Actual Galois-category dictionaries for finite-etale covers.

For every scheme, the universal 03RV producer and the arbitrary finite-action
sheaf construction supply the PreGaloisCategory quotient field. For a connected
scheme and a separably closed field-valued point, the actual point-lift fibre
has every pinned FiberFunctor field. No Galois, fibre-functor, representability,
quotient, or local-splitting premise remains in the public dictionaries. -/

@[expose] public section

noncomputable section
set_option autoImplicit false

open _root_.CategoryTheory _root_.CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.FiniteEtale
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (fiberToFinite)

universe u

instance actualCoverFiberFunctor {X : Scheme.{u}} [ConnectedSpace X]
    {K : Type u} [Field K] [IsSepClosed K] (s : Spec (CommRingCat.of K) ⟶ X) :
    PreGaloisCategory.FiberFunctor (fiberToFinite s) where
  preservesQuotientsByFiniteGroups G _ _ :=
    actualCoverFiber_preservesFiniteGroupQuotients s G

/-- The existential in GaloisCategory can name the user's actual point-lift
fibre functor, rather than an unrelated equivalent fibre. -/
theorem actualCoverGaloisCategoryAt {X : Scheme.{u}} [ConnectedSpace X]
    {K : Type u} [Field K] [IsSepClosed K] (s : Spec (CommRingCat.of K) ⟶ X) :
    GaloisCategory (Scheme.FiniteEtale X) where
  toPreGaloisCategory := actualCoverPreGaloisCategory X
  hasFiberFunctor := ⟨fiberToFinite s, actualCoverFiberFunctor s⟩

/-- A connected scheme has a geometric point, obtained from an algebraic
closure of a residue field, so its actual cover category is Galois. -/
instance actualCoverGaloisCategory (X : Scheme.{u}) [ConnectedSpace X] :
    GaloisCategory (Scheme.FiniteEtale X) :=
  actualCoverGaloisCategoryAt
    (algebraicClosureResiduePoint X (Classical.choice (inferInstance : Nonempty X)))

end AlgebraicGeometry.Scheme.FiniteEtale

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 7c2facc9b174520ea12428ee16a25c06e2d65a2a29ccc661d00c5971241129b4.
Definitions, hypotheses and universes are retained modulo native names. -/
