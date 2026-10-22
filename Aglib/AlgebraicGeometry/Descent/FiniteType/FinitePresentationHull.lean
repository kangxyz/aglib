/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FiniteType.Immersion
public import Aglib.AlgebraicGeometry.Descent.FiniteType.SeparatedFixedTarget
public import Aglib.AlgebraicGeometry.Morphisms.ClosedImmersion.FinitePresentationApproximation
public import Aglib.AlgebraicGeometry.Morphisms.Immersion.CompactFactorization

/-!
# Finite-presentation hulls from an actual supplied approximation

The first construction uses actual products and compact-open trimming. The
second replaces an actual closed factorization by a separated finitely presented
one using the literal original-source limit cone and varying-source separatedness
descent. Absolute approximation existence remains an explicit separate input.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

open Products

/-- A supplied actual approximation with finitely presented integer stages gives
an actual closed factorization through a qcqs finitely presented target. -/
theorem exists_closed_finitePresentation_factorization_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    [∀ i, LocallyOfFinitePresentation (toIntegerBase (D.obj i))]
    [∀ i, QuasiCompact (toIntegerBase (D.obj i))]
    [∀ i, QuasiSeparated (toIntegerBase (D.obj i))]
    {S : Scheme.{u}} [QuasiSeparatedSpace S] (f : c.pt ⟶ S) [LocallyOfFiniteType f] :
    ∃ (Y : Scheme.{u}) (e : c.pt ⟶ Y) (g : Y ⟶ S),
      CompactSpace Y ∧ QuasiSeparatedSpace Y ∧ IsClosedImmersion e ∧
      LocallyOfFinitePresentation g ∧ QuasiCompact g ∧ QuasiSeparated g ∧ e ≫ g = f := by
  let : CompactSpace c.pt := compactSpace_of_isLimit D c hc
  obtain ⟨i, hi⟩ := exists_isImmersion_integerBasePair_of_isLimit D c hc f
  let e : c.pt ⟶ pullback (toIntegerBase (D.obj i)) (toIntegerBase S) :=
    integerBasePair (c.π.app i) f
  let g := pullback.snd (toIntegerBase (D.obj i)) (toIntegerBase S)
  let : IsImmersion e := hi
  obtain ⟨W, hWc, _, _, hWqs, _, hgfp, hgqc, hgqs, eW, heW, _, hfac⟩ :=
    Hom.exists_compactOpen_closed_factorization (X := c.pt) e g f
      (integerBasePair_snd (c.π.app i) f)
  exact ⟨W.toScheme, eW, W.ι ≫ g, isCompact_iff_compactSpace.mp hWc,
    hWqs, heW, hgfp, hgqc, hgqs, hfac⟩

/-- Improve an actual closed factorization to a separated finitely presented one.
This uses varying-source separatedness of the actual original-source limit. -/
theorem exists_separated_finitePresentation_factorization_of_closed
    {X Y S : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
    [QuasiSeparatedSpace S] (e : X ⟶ Y) [IsClosedImmersion e]
    (g : Y ⟶ S) [LocallyOfFinitePresentation g] [QuasiCompact g]
    (f : X ⟶ S) (hef : e ≫ g = f) [IsSeparated f] :
    ∃ (Z : Scheme.{u}) (j : X ⟶ Z) (h : Z ⟶ S),
      CompactSpace Z ∧ QuasiSeparatedSpace Z ∧ IsClosedImmersion j ∧
      LocallyOfFinitePresentation h ∧ QuasiCompact h ∧ IsSeparated h ∧ j ≫ h = f := by
  classical
  let D := e.finitePresentationApproximationDiagram
  let c := e.finitePresentationApproximationCone
  let t : D ⟶ (Functor.const _).obj S :=
    e.finitePresentationApproximationStructure ≫ (Functor.const _).map g
  have (J : (IdealSheafData.FiniteTypeSubideal e.ker)ᵒᵖ) : CompactSpace (D.obj J) :=
    QuasiCompact.compactSpace_of_compactSpace (X := D.obj J) (Y := Y)
      (e.finitePresentationApproximationStructure.app J)
  have (J : (IdealSheafData.FiniteTypeSubideal e.ker)ᵒᵖ) : QuasiSeparatedSpace (D.obj J) :=
    quasiSeparatedSpace_of_quasiSeparated (X := D.obj J) (Y := Y)
      (e.finitePresentationApproximationStructure.app J)
  have (J : (IdealSheafData.FiniteTypeSubideal e.ker)ᵒᵖ) :
      LocallyOfFinitePresentation (t.app J) := by
    dsimp [t]
    infer_instance
  have (J : (IdealSheafData.FiniteTypeSubideal e.ker)ᵒᵖ) : QuasiCompact (t.app J) := by
    dsimp [t]
    infer_instance
  have hcompat (J : (IdealSheafData.FiniteTypeSubideal e.ker)ᵒᵖ) : c.π.app J ≫ t.app J = f := by
    change ((e.toImage ≫ IdealSheafData.inclusion J.unop.property.1) ≫
      (e.finitePresentationApproximationStructure.app J ≫ g) : X ⟶ S) = f
    rw [← Category.assoc, e.finitePresentationApproximationCone_comp, hef]
  let i : (IdealSheafData.FiniteTypeSubideal e.ker)ᵒᵖ := Classical.choice inferInstance
  obtain ⟨J, hJ⟩ := exists_isSeparated_app_of_isLimit_of_quasiSeparatedSpace
    D t c e.finitePresentationApproximationConeIsLimit f hcompat i
  exact ⟨D.obj J.left, c.π.app J.left, t.app J.left, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, hJ, hcompat J.left⟩

/-- Conditional separated finite-presentation hull, built from an explicit actual
approximation diagram rather than a hidden hull or approximation provider. -/
theorem exists_separated_finitePresentation_factorization_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    [∀ i, LocallyOfFinitePresentation (toIntegerBase (D.obj i))]
    [∀ i, QuasiCompact (toIntegerBase (D.obj i))]
    [∀ i, QuasiSeparated (toIntegerBase (D.obj i))]
    {S : Scheme.{u}} [QuasiSeparatedSpace S] (f : c.pt ⟶ S)
    [LocallyOfFiniteType f] [IsSeparated f] :
    ∃ (Y : Scheme.{u}) (e : c.pt ⟶ Y) (g : Y ⟶ S),
      CompactSpace Y ∧ QuasiSeparatedSpace Y ∧ IsClosedImmersion e ∧
      LocallyOfFinitePresentation g ∧ QuasiCompact g ∧ IsSeparated g ∧ e ≫ g = f := by
  obtain ⟨Y, e, g, hYc, hYqs, he, hgfp, hgqc, hgqs, hef⟩ :=
    exists_closed_finitePresentation_factorization_of_isLimit D c hc f
  let := hYc
  let := hYqs
  let := he
  let := hgfp
  let := hgqc
  let := hgqs
  exact exists_separated_finitePresentation_factorization_of_closed e g f hef

end AlgebraicGeometry.Scheme
