/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FiniteType.FinitePresentationHull
public import Aglib.AlgebraicGeometry.Products.IntegerFiniteTypeProperties

/-!
Finite-type integer stages supply the finite-presentation stage hypotheses of
an actual-diagram separated hull. Only the fixed lifted integer base is used
as a Noetherian scheme; no such hypothesis is placed on the original schemes.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u

namespace AlgebraicGeometry.Scheme
open Products

/-- An actual approximation with finite-type integer stages suffices for the
separated finite-presentation hull; existence of that diagram remains explicit. -/
theorem exists_separated_finitePresentation_factorization_of_integerFiniteType_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, LocallyOfFiniteType (toIntegerBase (D.obj i))]
    [∀ i, QuasiCompact (toIntegerBase (D.obj i))]
    {S : Scheme.{u}} [QuasiSeparatedSpace S] (f : c.pt ⟶ S)
    [LocallyOfFiniteType f] [IsSeparated f] :
    ∃ (Y : Scheme.{u}) (e : c.pt ⟶ Y) (g : Y ⟶ S),
      CompactSpace Y ∧ QuasiSeparatedSpace Y ∧ IsClosedImmersion e ∧
      LocallyOfFinitePresentation g ∧ QuasiCompact g ∧ IsSeparated g ∧ e ≫ g = f := by
  have (i : I) : CompactSpace (D.obj i) := (integerFiniteType_stage_properties (D.obj i)).1
  have (i : I) : QuasiSeparatedSpace (D.obj i) :=
    (integerFiniteType_stage_properties (D.obj i)).2.1
  have (i : I) : LocallyOfFinitePresentation (toIntegerBase (D.obj i)) :=
    (integerFiniteType_stage_properties (D.obj i)).2.2.1
  have (i : I) : QuasiSeparated (toIntegerBase (D.obj i)) :=
    (integerFiniteType_stage_properties (D.obj i)).2.2.2
  exact exists_separated_finitePresentation_factorization_of_isLimit D c hc f

end AlgebraicGeometry.Scheme
