/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Approximation.FinitePresentationEnvelope.Absolute
public import Aglib.AlgebraicGeometry.Descent.FiniteType.IntegerFiniteTypeHull

/-!
# Separated finite-presentation hulls over quasi-separated bases

The actual arithmetic approximation of a quasi-compact quasi-separated source
supplies the diagram required by the separated finite-presentation hull construction.
The arithmetic structural maps are the native maps to the lifted integer spectrum.
The original source, its structural morphism, and the closed factorization are retained.

No approximation diagram or Noetherian hypothesis is a premise of these theorems.
This gives a finite-presentation hull, not a proper compactification.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- A separated locally finite-type map from a quasi-compact scheme to a
quasi-separated base factors through a separated finitely presented morphism
by an actual closed immersion of its original source. -/
theorem exists_separated_finitePresentation_factorization_of_compactSpace
    {X S : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace S]
    (f : X ⟶ S) [LocallyOfFiniteType f] [IsSeparated f] :
    ∃ (Y : Scheme.{u}) (e : X ⟶ Y) (g : Y ⟶ S),
      CompactSpace Y ∧ QuasiSeparatedSpace Y ∧ IsClosedImmersion e ∧
      LocallyOfFinitePresentation g ∧ QuasiCompact g ∧ IsSeparated g ∧ e ≫ g = f := by
  let : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  obtain ⟨M⟩ := FinitePresentationEnvelope.nonempty_system X
  have (i : M.Index) : LocallyOfFiniteType (Products.toIntegerBase (M.diagram.obj i)) := by
    change LocallyOfFiniteType (specULiftZIsTerminal.from (M.diagram.obj i))
    exact M.finiteType i
  have (i : M.Index) : QuasiCompact (Products.toIntegerBase (M.diagram.obj i)) := by
    let : IsNoetherian (M.diagram.obj i) := ⟨⟩
    infer_instance
  exact exists_separated_finitePresentation_factorization_of_integerFiniteType_isLimit
    M.diagram ⟨X, M.projection⟩ M.isLimit f

/-- Every separated finite-type morphism to a quasi-compact quasi-separated
base has a separated finite-presentation hull containing its original source
as a closed subscheme, with the original structural map as composite. -/
theorem exists_separated_finitePresentation_factorization_of_qcqs
    {X S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (f : X ⟶ S) [QuasiCompact f] [LocallyOfFiniteType f] [IsSeparated f] :
    ∃ (Y : Scheme.{u}) (e : X ⟶ Y) (g : Y ⟶ S),
      CompactSpace Y ∧ QuasiSeparatedSpace Y ∧ IsClosedImmersion e ∧
      LocallyOfFinitePresentation g ∧ QuasiCompact g ∧ IsSeparated g ∧ e ≫ g = f := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  exact exists_separated_finitePresentation_factorization_of_compactSpace f

end AlgebraicGeometry.Scheme
