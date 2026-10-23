/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Basic
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-! # Finite values of actual constant-diagram colimits

A diagram with finitely many objects and finite abelian values has finite
original colimits: the concrete direct-sum quotient is finite. Applying the
actual constant-sheaf functor therefore gives finite locally constant
colimits, with no restriction on the base scheme. This is a value-level
ingredient; producing common local trivializations of arbitrary diagrams
remains a separate obligation.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteColimits

universe u v w

attribute [local instance] hasSheafifyLarge

/-- The original colimit of finite abelian values is finite whenever its
object family is finite. No bound on the number of diagram arrows is needed. -/
theorem finite_of_isColimit {J : Type v} [Category.{w} J] [Finite J]
    (D : J ⥤ AddCommGrpCat.{u}) [∀ j, Finite (D.obj j)]
    {c : Cocone D} (hc : IsColimit c) : Finite c.pt := by
  classical
  let := Fintype.ofFinite J
  have : Finite (DFinsupp (fun j => D.obj j)) :=
    Finite.of_equiv (∀ j, D.obj j) DFinsupp.equivFunOnFintype.symm
  have : Finite (AddCommGrpCat.Colimits.Quot D) :=
    Finite.of_surjective (QuotientAddGroup.mk' (AddCommGrpCat.Colimits.Relations D))
      (QuotientAddGroup.mk'_surjective _)
  have : Small.{u} (AddCommGrpCat.Colimits.Quot D) := inferInstance
  have : Finite (Shrink.{u} (AddCommGrpCat.Colimits.Quot D)) :=
    Finite.of_equiv _ (equivShrink _)
  let e := hc.coconePointUniqueUpToIso (AddCommGrpCat.Colimits.colimitCoconeIsColimit D)
  exact Finite.of_equiv (Shrink.{u} (AddCommGrpCat.Colimits.Quot D))
    (Iso.addCommGroupIsoToAddEquiv e.symm).toEquiv

/-- The chosen colimit has the same finite original additive value. -/
theorem finite_colimit {J : Type v} [Category.{w} J] [Finite J]
    (D : J ⥤ AddCommGrpCat.{u}) [∀ j, Finite (D.obj j)] :
    Finite (Limits.colimit D : AddCommGrpCat.{u}) :=
  finite_of_isColimit D (colimit.isColimit D)

/-- An actual constant-value diagram with finitely many finite values has
finite locally constant original colimits on every scheme. -/
theorem isFiniteLocallyConstant_constantDiagramColimit (X : Scheme.{u})
    {J : Type v} [Category.{w} J] [Finite J]
    (D : J ⥤ AddCommGrpCat.{u + 1}) [∀ j, Finite (D.obj j)]
    {c : Cocone (D ⋙ constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})}
    (hc : IsColimit c) : IsFiniteLocallyConstant c.pt := by
  let C := constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}
  let : C.IsLeftAdjoint := (constantAdjunction X).isLeftAdjoint
  have : Finite (Limits.colimit D : AddCommGrpCat.{u + 1}) := finite_colimit D
  let e : c.pt ≅ C.obj (Limits.colimit D) :=
    hc.coconePointUniqueUpToIso (isColimitOfPreserves C (colimit.isColimit D))
  exact (isFiniteLocallyConstant_iff_of_iso e).mpr ⟨finiteConstantTrivialization X _⟩

/-- A zero original abelian sheaf is finite locally constant via its actual
isomorphism to the constant sheaf of the finite trivial abelian group. -/
theorem isFiniteLocallyConstant_of_isZero {X : Scheme.{u}}
    {F : AbelianSheaf.{u, u + 1} X} (hF : IsZero F) : IsFiniteLocallyConstant F := by
  let A : AddCommGrpCat.{u + 1} := AddCommGrpCat.of PUnit.{u + 2}
  let C := constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}
  let : C.IsLeftAdjoint := (constantAdjunction X).isLeftAdjoint
  have hA : IsZero A := AddCommGrpCat.isZero_of_subsingleton A
  let e : F ≅ C.obj A := hF.iso (C.map_isZero hA)
  exact (isFiniteLocallyConstant_iff_of_iso e).mpr ⟨finiteConstantTrivialization X A⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteColimits
