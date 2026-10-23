/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Pullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.FiniteCoefficientPullback
public import Aglib.CategoryTheory.Sites.SheafCohomology.Slice.ExtComparison

/-! # Original cohomology of exact direct images

The exact-adjunction comparison is normalized by the original inverse image
of the constant integer sheaf. In particular, original geometric pullback
corresponds to the original coefficient map induced by the adjunction unit.
Exactness of direct image is an explicit input; this leaf does not assert
finite-etale exactness or any cohomological vanishing.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Fields

universe u w w'

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (f : S ⟶ X)

/-- The actual direct image preserves the same coefficient annihilator. -/
theorem killedBy_directImage (F : AbelianSheaf.{u, u + 1} S) {n : ℕ}
    (hF : KilledBy n F) : KilledBy n ((directImage f).obj F) := by
  have h := congrArg (fun a : F ⟶ F => (directImage f).map a) hF
  simpa [KilledBy] using h

/-- The coefficient of finite coinduction retains the original annihilator. -/
theorem killedBy_directImage_inverseImage (F : AbelianSheaf.{u, u + 1} X) {n : ℕ}
    (hF : KilledBy n F) :
    KilledBy n ((directImage f).obj ((inverseImage f).obj F)) :=
  killedBy_directImage f _ (killedBy_pullback f hF)

variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)]
  [PreservesFiniteColimits (directImage f)]

/-- Shapiro's comparison for the actual direct image, whenever that functor
is exact. Source and target Ext universes remain independent. -/
def directImageCohomologyEquiv (F : AbelianSheaf.{u, u + 1} S) (q : ℕ) :
    Sheaf.H.{w'} F q ≃+ Sheaf.H.{w} ((directImage f).obj F) q :=
  (inverseImageAdjunction f).sourceExtComparison
    ((inverseImageConstantIso f).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))) F q

/-- The comparison retains the literal adjunction unit and integer transport. -/
theorem directImageCohomologyEquiv_apply (F : AbelianSheaf.{u, u + 1} S) (q : ℕ)
    (a : Sheaf.H.{w'} F q) :
    directImageCohomologyEquiv f F q a =
      (Ext.mk₀ ((inverseImageAdjunction f).unit.app _ ≫
        (directImage f).map
          ((inverseImageConstantIso f).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom)).comp
        (a.mapExactFunctor (directImage f)) (Nat.zero_add q) :=
  (inverseImageAdjunction f).sourceExtComparison_apply _ F q a

/-- Under the exact-adjunction comparison, original pullback is exactly the
original cohomology map of the coefficient adjunction unit. -/
theorem directImageCohomologyEquiv_cohomologyPullback
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) (a : Sheaf.H.{w} F q) :
    directImageCohomologyEquiv f ((inverseImage f).obj F) q
      (cohomologyPullback f F q a) =
        Sheaf.H.map ((inverseImageAdjunction f).unit.app F) q a := by
  let e := (inverseImageConstantIso f).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  change (inverseImageAdjunction f).extEquiv
      ((Ext.mk₀ e.hom).comp
        ((Ext.mk₀ e.inv).comp (a.mapExactFunctor (inverseImage f)) (Nat.zero_add q))
          (Nat.zero_add q)) = _
  rw [Ext.mk₀_comp_mk₀_assoc, e.hom_inv_id, Ext.mk₀_id_comp]
  have h := (inverseImageAdjunction f).extEquiv_naturality_left a
    (Ext.mk₀ (𝟙 ((inverseImage f).obj F))) (Nat.add_zero q)
  rw [Ext.comp_mk₀_id, Adjunction.extEquiv_mk₀] at h
  have hunit : (inverseImageAdjunction f).homEquiv F ((inverseImage f).obj F)
      (𝟙 ((inverseImage f).obj F)) = (inverseImageAdjunction f).unit.app F :=
    (inverseImageAdjunction f).homEquiv_id F
  exact h.trans (congrArg (fun k => a.comp (Ext.mk₀ k) (Nat.add_zero q)) hunit)

/-- A class killed by the original geometric pullback is killed by the
actual coefficient unit, without replacing either cohomology group. -/
theorem unit_cohomologyMap_eq_zero_of_pullback_eq_zero
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) (a : Sheaf.H.{w} F q)
    (ha : cohomologyPullback f F q a = 0) :
    Sheaf.H.map ((inverseImageAdjunction f).unit.app F) q a = 0 := by
  rw [← directImageCohomologyEquiv_cohomologyPullback, ha, map_zero]

end AlgebraicGeometry.Scheme.EtaleCohomology.Fields
