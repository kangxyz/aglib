/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Vanishing.CurveFiniteConstants
public import Aglib.AlgebraicGeometry.EtaleCohomology.Vanishing.DimensionZero
public import Aglib.AlgebraicGeometry.EtaleCohomology.Vanishing.PGroupCoefficients
public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.AbelianShortExact

/-! # Curve vanishing across a zero-dimensional closed boundary

Original open-closed localization and arbitrary-coefficient zero-dimensional
acyclicity compare vanishing before and after extension by zero in degrees
above one. Finite constants and actual p-group trivializations then give
unconditional original-cohomology vanishing for the displayed coefficients.
The boundary, its dimension, and the actual trivialization remain explicit.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Vanishing

open Constructible.Modules

universe u r e

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable {k : Type u} [Field k] [IsSepClosed k]
  {X U Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
  [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]
  (j : U ⟶ X) [IsOpenImmersion j] (i : Z ⟶ X) [IsClosedImmersion i]
  (hcomp : Set.range j = (Set.range i)ᶜ)
  (hdimZ : topologicalKrullDim Z ≤ 0)

include f i hcomp hdimZ

/-- A zero-dimensional proper closed boundary does not affect vanishing in
degrees above one. This uses the actual localization arrows and arbitrary
abelian coefficients, without torsion or constructibility. -/
theorem subsingleton_H_etaleLowerShriek_restrict_iff
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) (hq : 1 < q) :
    Subsingleton (Sheaf.H.{e}
      ((etaleLowerShriek j).obj ((inverseImage j).obj F)) q) ↔
      Subsingleton (Sheaf.H.{e} F q) := by
  let : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} Z) := HasExt.standard _
  let S := abelianLocalizationShortComplex j i hcomp F
  have hS : S.ShortExact := abelianLocalization_shortExact j i hcomp F
  have hboundary (a : ℕ) (ha : 0 < a) : Subsingleton (Sheaf.H.{e} S.X₃ a) := by
    let : Subsingleton (Sheaf.H.{u + 2} ((inverseImage i).obj F) a) :=
      subsingleton_H_of_proper_dimension_le_zero (i ≫ f) hdimZ
        ((inverseImage i).obj F) a ha
    exact (Finite.finiteCohomologyDirectImageAddEquiv.{u, u + 2, e}
      i ((inverseImage i).obj F) a).injective.subsingleton
  constructor
  · intro h
    let : Subsingleton (Sheaf.H.{e} S.X₁ q) := h
    let : Subsingleton (Sheaf.H.{e} S.X₃ q) := hboundary q (by omega)
    exact Sheaf.H.subsingleton_middle_of_shortExact hS q
  · intro h
    let : Subsingleton (Sheaf.H.{e} S.X₂ q) := h
    let : Subsingleton (Sheaf.H.{e} S.X₃ (q - 1)) := hboundary (q - 1) (by omega)
    apply Sheaf.H.subsingleton_left_of_surjective hS (q - 1) q (by omega)
    intro x
    exact ⟨0, Subsingleton.elim _ _⟩

/-- Finite constant values on the open have zero high cohomology after the
actual extension by zero to a proper curve with zero-dimensional boundary. -/
theorem subsingleton_H_etaleLowerShriek_constant
    (hdim : topologicalKrullDim X ≤ 1)
    (A : AddCommGrpCat.{u + 1}) [Finite A] (q : ℕ) (hq : 2 < q) :
    Subsingleton (Sheaf.H.{e} ((etaleLowerShriek j).obj
      ((constantSheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A)) q) := by
  let F := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A
  let : Subsingleton (Sheaf.H.{e} F q) :=
    constant_subsingleton_H_of_proper_dimension_le_one f hdim A q hq
  let : Subsingleton (Sheaf.H.{e}
      ((etaleLowerShriek j).obj ((inverseImage j).obj F)) q) :=
    (subsingleton_H_etaleLowerShriek_restrict_iff f j i hcomp hdimZ F q (by omega)).mpr
      inferInstance
  let d : (inverseImage j).obj F ≅
      (constantSheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A :=
    (inverseImageConstantIso j).app A
  exact (cohomologyMapIso_bijective
    ((etaleLowerShriek j).mapIso d) q).surjective.subsingleton

/-- Finite modules over a finite ring give the actual constant-coefficient
input to p-group induction after scalar forgetting and extension by zero. -/
theorem subsingleton_H_etaleLowerShriek_constantModule
    (hdim : topologicalKrullDim X ≤ 1)
    (R : Type r) [CommRing R] [Finite R]
    (M : ModuleCat.{u + 1} R) [Module.Finite R M] (q : ℕ) (hq : 2 < q) :
    Subsingleton (Sheaf.H.{e} ((etaleLowerShriek j).obj
      ((moduleUnderlying R U).obj
        ((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M))) q) := by
  let : Finite M := Module.finite_of_finite R
  let A := (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).obj M
  let : Subsingleton (Sheaf.H.{e} ((etaleLowerShriek j).obj
      ((constantSheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A)) q) :=
    subsingleton_H_etaleLowerShriek_constant f j i hcomp hdimZ hdim A q hq
  let d : (moduleUnderlying R U).obj
      ((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M) ≅
        (constantSheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A :=
    (moduleConstantUnderlyingIso R U).app M
  exact (cohomologyMapIso_bijective
    ((etaleLowerShriek j).mapIso d) q).injective.subsingleton

/-- Actual prime-killed module coefficients trivialized by the supplied
p-group cover vanish above degree two after extension by zero. The ring is
finite, but need not have characteristic equal to the chosen prime. -/
theorem subsingleton_H_etaleLowerShriek_of_pGroup_trivialization
    (hdim : topologicalKrullDim X ≤ 1)
    (R : Type r) [CommRing R] [Finite R] [ConnectedSpace U]
    (Y : Scheme.FiniteEtale U) [PreGaloisCategory.IsGalois Y]
    [Surjective Y.obj.hom] [ConnectedSpace Y.obj.left]
    [CompactSpace Y.obj.left] [QuasiSeparatedSpace Y.obj.left]
    (p : ℕ) [Fact p.Prime] (hY : IsPGroup p (Aut Y))
    (F : ModuleSheaf R U) (M : ModuleCat.{u + 1} R) [Module.Finite R M]
    (hM : ∀ m : M, p • m = 0)
    (t : (moduleInverseImage R Y.obj.hom).obj F ≅
      (constantSheaf Y.obj.left.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M)
    (q : ℕ) (hq : 2 < q) :
    Subsingleton (Sheaf.H.{e}
      ((etaleLowerShriek j).obj ((moduleUnderlying R U).obj F)) q) := by
  exact subsingleton_H_obj_of_pGroup_trivialization Y p hY
    (moduleUnderlying R U ⋙ etaleLowerShriek j) q
    (fun N _ _ => subsingleton_H_etaleLowerShriek_constantModule
      f j i hcomp hdimZ hdim R N q hq) F M hM t

end AlgebraicGeometry.Scheme.EtaleCohomology.Vanishing
