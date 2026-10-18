/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.CoverFiberQuotients
public import Aglib.AlgebraicGeometry.Cohomology.EtaleH1.FiniteSetRepresentation

/-! Instantiate the actual finite-group quotient construction using the
universal constructive Stacks03RV producer. No representability hypothesis is
retained in these dictionaries. -/

@[expose] public section

noncomputable section
set_option autoImplicit false

open _root_.CategoryTheory _root_.CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleH1

namespace AlgebraicGeometry.Scheme.FiniteEtale
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (fiberToFinite)

universe u

instance actualCoverPreGaloisCategory (X : Scheme.{u}) : PreGaloisCategory (Scheme.FiniteEtale X) :=
  coverPreGaloisOfStacks03RV (stacks03RV X)

instance actualCoverSectionSheaf_preservesFiniteGroupQuotients (X : Scheme.{u})
    (G : Type u) [Group G] [Finite G] :
    PreservesColimitsOfShape (SingleObj G) (finiteCoverSectionSheafFunctor X) :=
  coverSectionSheaf_preservesFiniteGroupQuotients (stacks03RV X) G

instance actualCoverFiber_preservesFiniteGroupQuotients {X : Scheme.{u}}
    {K : Type u} [Field K] [IsSepClosed K] (s : Spec (CommRingCat.of K) ⟶ X)
    (G : Type u) [Group G] [Finite G] :
    PreservesColimitsOfShape (SingleObj G) (fiberToFinite s) :=
  coverFiber_preservesFiniteGroupQuotients s (stacks03RV X) G

instance actualCoverFiber_reflectsIsomorphisms {X : Scheme.{u}} [ConnectedSpace X]
    {K : Type u} [Field K] [IsSepClosed K] (s : Spec (CommRingCat.of K) ⟶ X) :
    (fiberToFinite s).ReflectsIsomorphisms :=
  coverFiber_reflectsIsomorphisms s

end AlgebraicGeometry.Scheme.FiniteEtale

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 3274bff4fe584b0b60534a008510d6e5db97a0dc8b38f627c747bd1fa07f4625.
Definitions, hypotheses and universes are retained modulo native names. -/
