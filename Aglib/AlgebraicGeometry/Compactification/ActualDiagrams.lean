/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.NoetherianLimit
public import Aglib.AlgebraicGeometry.Descent.FiniteType.IntegerFiniteTypeHull

/-!
Nagata reduction with both actual approximation diagrams explicit. The source
diagram constructs a separated finite-presentation hull. The base diagram
descends that hull to a Noetherian stage, where the proved compactification
is base-changed and the original source is recovered by schematic image.
No existence of either approximation diagram is assumed implicitly.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits
universe u

namespace AlgebraicGeometry.Scheme
open Products

/-- Actual integer-type approximation diagrams for the original source and
base give a schematically dense compactification of the original morphism.
This is conditional on the two explicitly supplied limit constructions. -/
theorem Hom.exists_schematicallyDense_compactification_of_integerFiniteType_isLimits
    {I J : Type u} [Category.{u} I] [IsCofiltered I]
    [Category.{u} J] [IsCofiltered J]
    (DX : I ⥤ Scheme.{u}) (cX : Cone DX) (hcX : IsLimit cX)
    (DS : J ⥤ Scheme.{u}) (cS : Cone DS) (hcS : IsLimit cS)
    [∀ {i j} (q : i ⟶ j), IsAffineHom (DX.map q)]
    [∀ {i j} (q : i ⟶ j), IsAffineHom (DS.map q)]
    [∀ i, LocallyOfFiniteType (toIntegerBase (DX.obj i))]
    [∀ i, QuasiCompact (toIntegerBase (DX.obj i))]
    [∀ j, LocallyOfFiniteType (toIntegerBase (DS.obj j))]
    [∀ j, QuasiCompact (toIntegerBase (DS.obj j))]
    (f : cX.pt ⟶ cS.pt) [LocallyOfFiniteType f] [IsSeparated f] :
    ∃ C : f.Compactification, IsSchemeTheoreticallyDominant C.j := by
  have (i : I) : CompactSpace (DX.obj i) := (integerFiniteType_stage_properties (DX.obj i)).1
  have (i : I) : QuasiSeparatedSpace (DX.obj i) :=
    (integerFiniteType_stage_properties (DX.obj i)).2.1
  have (j : J) : IsNoetherian (DS.obj j) := isNoetherian_of_integerFiniteType (DS.obj j)
  have (j : J) : CompactSpace (DS.obj j) := inferInstance
  have (j : J) : QuasiSeparatedSpace (DS.obj j) := inferInstance
  have : CompactSpace cX.pt := compactSpace_of_isLimit DX cX hcX
  obtain ⟨j⟩ := IsCofiltered.nonempty (C := J)
  have : IsAffineHom (cS.π.app j) := isAffineHom_π_app DS cS hcS j
  have : QuasiSeparatedSpace cS.pt :=
    quasiSeparatedSpace_of_quasiSeparated (X := cS.pt) (Y := DS.obj j) (cS.π.app j)
  obtain ⟨Y, e, g, hYc, hYqs, he, hgfp, hgqc, hgsep, hef⟩ :=
    exists_separated_finitePresentation_factorization_of_integerFiniteType_isLimit DX cX hcX f
  let : CompactSpace Y := hYc
  let : QuasiSeparatedSpace Y := hYqs
  let : IsClosedImmersion e := he
  let : LocallyOfFinitePresentation g := hgfp
  let : QuasiCompact g := hgqc
  let : IsSeparated g := hgsep
  obtain ⟨C⟩ := Hom.exists_compactification_of_noetherian_isLimit DS cS hcS g
  have : QuasiSeparatedSpace C.Xbar :=
    quasiSeparatedSpace_of_quasiSeparated (X := C.Xbar) (Y := cS.pt) C.p
  let h : cX.pt ⟶ C.Xbar := e ≫ C.j
  have : QuasiCompact h := inferInstance
  have hf : h ≫ C.p = f := by
    dsimp [h]
    rw [Category.assoc, C.fac, hef]
  exact ⟨Hom.Compactification.ofImmersion f h C.p hf, inferInstance⟩

end AlgebraicGeometry.Scheme
