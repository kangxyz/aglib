/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.IsoOpenUnitCokernel
public import Aglib.AlgebraicGeometry.EtaleCohomology.Vanishing.BoundedHypercohomology
public import Aglib.AlgebraicGeometry.EtaleCohomology.Vanishing.DimensionZero
public import Aglib.CategoryTheory.Sites.SheafCohomology.Vanishing.ExactSequence

/-! # Original cohomology vanishing through a finite modification

The original surjective unit embeds the coefficient in the finite direct
image of its actual inverse image. Its original cokernel is supported on
the displayed closed complement of the isomorphism open. The genuine short
exact sequence descends vanishing with the preceding-degree boundary term.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Vanishing

universe u eX eY eZ

attribute [local instance] hasSheafifyLarge

/-- Vanishing descends through an actual finite surjection which is an
isomorphism over the supplied open, provided the original unit cokernel's
closed restriction vanishes in the preceding degree. All Ext universes are
independent, and no field, properness or torsion hypothesis is imposed. -/
theorem subsingleton_H_of_finiteModification
    {Y U Z X : Scheme.{u}} (c : Y ⟶ X) [IsFinite c] [Surjective c]
    (j : U ⟶ X) [IsOpenImmersion j] [IsIso (pullback.snd c j)]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (hcomp : Set.range j = (Set.range i)ᶜ)
    [HasExt.{eX} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{eY} (AbelianSheaf.{u, u + 1} Y)]
    [HasExt.{eZ} (AbelianSheaf.{u, u + 1} Z)]
    (F : AbelianSheaf.{u, u + 1} X) (n : ℕ)
    (hY : Subsingleton (Sheaf.H.{eY} ((inverseImage c).obj F) (n + 1)))
    (hZ : Subsingleton (Sheaf.H.{eZ} ((inverseImage i).obj
      (cokernel ((inverseImageAdjunction c).unit.app F))) n)) :
    Subsingleton (Sheaf.H.{eX} F (n + 1)) := by
  let η := (inverseImageAdjunction c).unit.app F
  let : Mono η := inverseImageAdjunction_unit_mono_of_surjective c F
  let S := ShortComplex.mk η (cokernel.π η) (cokernel.condition η)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel η }
  let : Subsingleton (Sheaf.H.{eY} ((inverseImage c).obj F) (n + 1)) := hY
  let : Subsingleton (Sheaf.H.{eX} S.X₂ (n + 1)) :=
    (Finite.finiteCohomologyDirectImageAddEquiv.{u, eY, eX}
      c ((inverseImage c).obj F) (n + 1)).injective.subsingleton
  let : Subsingleton (Sheaf.H.{eX} S.X₃ n) :=
    subsingleton_H_of_closedSupport i (cokernel η)
      (Finite.unit_cokernel_closedSupport c j i hcomp F) n hZ
  apply Sheaf.H.subsingleton_left_of_surjective hS n (n + 1) rfl
  intro x
  exact ⟨0, Subsingleton.elim _ _⟩

/-- An actual finite surjection which is an isomorphism away from a
zero-dimensional closed boundary descends original cohomology vanishing
above degree one on a proper scheme over a separably closed field.
The coefficient is arbitrary, with independent source and target Ext sizes. -/
theorem subsingleton_H_of_finiteModification_dimensionZero
    {k : Type u} [Field k] [IsSepClosed k]
    {Y U Z X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProper p]
    (c : Y ⟶ X) [IsFinite c] [Surjective c]
    (j : U ⟶ X) [IsOpenImmersion j] [IsIso (pullback.snd c j)]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (hcomp : Set.range j = (Set.range i)ᶜ)
    (hdimZ : topologicalKrullDim Z ≤ 0)
    [HasExt.{eX} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{eY} (AbelianSheaf.{u, u + 1} Y)]
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) (hq : 1 < q)
    (hY : Subsingleton (Sheaf.H.{eY} ((inverseImage c).obj F) q)) :
    Subsingleton (Sheaf.H.{eX} F q) := by
  let : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} Z) := HasExt.standard _
  cases q with
  | zero => omega
  | succ n =>
    exact subsingleton_H_of_finiteModification c j i hcomp F n hY
      (subsingleton_H_of_proper_dimension_le_zero (i ≫ p) hdimZ
        ((inverseImage i).obj (cokernel ((inverseImageAdjunction c).unit.app F))) n
        (by omega))

end AlgebraicGeometry.Scheme.EtaleCohomology.Vanishing
