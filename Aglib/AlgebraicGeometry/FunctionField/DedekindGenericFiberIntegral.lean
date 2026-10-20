/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.DedekindGenericFiber

/-!
# Integrality of the actual dominant generic fibre

The literal generic-fibre projection is a dominant preimmersion, hence its source
is irreducible. Its actual stalk equivalences transport reducedness from the
integral model, proving integrality with no regularity, flatness or finiteness
assumption on the model morphism.

Source: `R5Lab/Aglib/AlgebraicGeometry/FunctionField/IntegralGenericFiber.lean`,
revision `f8a3314ddecffcada2ec721d26d56a937bed9690`, lines 28–53, SHA-256
`63383ada445fed0b0e98bb6e295cff489a12ceab56749482b78b2befaa33fb4b`.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open AlgebraicGeometry.Scheme.LocalRing.GenericFiber (baseMap projection scheme stalkEquiv)

universe u

namespace AlgebraicGeometry.Scheme.FunctionField.DedekindGenericFiber

/-- A dominant preimmersion into an irreducible scheme has irreducible source. -/
theorem irreducible_of_dominant_preimmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsPreimmersion f] [IsDominant f] [IrreducibleSpace Y] : IrreducibleSpace X := by
  have hr : IsIrreducible (Set.range f) := isIrreducible_iff_closure.mp (by
    rw [f.denseRange.closure_range]
    exact IrreducibleSpace.isIrreducible_univ Y)
  let := Subtype.irreducibleSpace hr
  exact f.isEmbedding.toHomeomorph.irreducibleSpace_iff.mpr inferInstance

/-- The actual fraction-field pullback of a dominant integral Dedekind-base scheme is integral. -/
theorem integral_genericFiber (A K : Type u) [CommRing A] [IsDedekindDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    {X : Scheme.{u}} [IsIntegral X] (q : X ⟶ Spec (.of A)) [IsDominant q] :
    IsIntegral (scheme A K q) := by
  let : IsPreimmersion (baseMap A K) := LocalRing.GenericFiber.baseMap_preimmersion A K
  let : IrreducibleSpace (scheme A K q) :=
    irreducible_of_dominant_preimmersion (projection A K q)
  let (x : scheme A K q) : IsDomain ((scheme A K q).presheaf.stalk x) :=
    (stalkEquiv A K q x).symm.toMulEquiv.isDomain _
  let : IsReduced (scheme A K q) := isReduced_of_isReduced_stalk _
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end AlgebraicGeometry.Scheme.FunctionField.DedekindGenericFiber
