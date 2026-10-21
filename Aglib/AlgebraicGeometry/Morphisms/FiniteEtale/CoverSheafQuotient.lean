/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.FiniteCoverSheafBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.RepresentedTorsor
public import Mathlib.CategoryTheory.Limits.Creates
public import Mathlib.CategoryTheory.Sites.Limits

/-! Actual sheaf colimits and their represented-cover universal property.
The finite local constancy premise is displayed explicitly until supplied by
local equivariant splitting. No raw orbit presheaf is asserted to be a sheaf. -/

@[expose] public section

noncomputable section
set_option autoImplicit false

open _root_.CategoryTheory _root_.CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCohomology

namespace AlgebraicGeometry.Scheme.FiniteEtale

universe u v w

instance finiteCoverSectionSheafFunctor_full (X : Scheme.{u}) :
    (finiteCoverSectionSheafFunctor X).Full where
  map_surjective {Y Z} q := by
    refine ⟨ObjectProperty.homMk (finiteRepresentedSetSheafPreimage q), ?_⟩
    exact finiteRepresentedSetSheafMap_preimage q

instance finiteCoverSectionSheafFunctor_faithful (X : Scheme.{u}) :
    (finiteCoverSectionSheafFunctor X).Faithful where
  map_injective {Y Z} f g h := by
    apply ObjectProperty.hom_ext _
    exact (finiteRepresentedSetSheafHomEquiv Y Z).injective h

variable {X : Scheme.{u}} {J : Type v} [Category.{w} J]
    (D : J ⥤ Scheme.FiniteEtale X)
    [HasColimit (D ⋙ finiteCoverSectionSheafFunctor X)]

/-- Colimit taken in the actual category of small-etale sheaves. -/
abbrev coverDiagramSheafColimit : SetSheaf X :=
  colimit (D ⋙ finiteCoverSectionSheafFunctor X)

/-- The exact fully faithful Yoneda construction creates the cover colimit
when its sheaf colimit is finite locally constant and 03RV is available. -/
@[instance_reducible] def coverCreatesColimitOfFiniteLocalConstancy (hRV : Stacks03RV X)
    (h : IsFiniteLocallyConstantSet (coverDiagramSheafColimit D)) :
    CreatesColimit D (finiteCoverSectionSheafFunctor X) := by
  let rep := hRV.representable (coverDiagramSheafColimit D) h
  exact createsColimitOfFullyFaithfulOfIso rep.choose rep.choose_spec.some

theorem hasCoverColimitOfFiniteLocalConstancy (hRV : Stacks03RV X)
    (h : IsFiniteLocallyConstantSet (coverDiagramSheafColimit D)) : HasColimit D := by
  let := coverCreatesColimitOfFiniteLocalConstancy D hRV h
  exact hasColimit_of_created D (finiteCoverSectionSheafFunctor X)

end AlgebraicGeometry.Scheme.FiniteEtale

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 6e2cac449850d39d46fff5d09d3ea11ac510fe09f6d3436779a905f408577288.
Definitions, hypotheses and universes are retained modulo native names. -/
