/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H0.CyclicSectionPullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.DegreeZeroPullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.BoundaryNaturality
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.BaseChangeCoefficientGlobalSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.GlobalSectionsNaturality
public import Aglib.Algebra.Homology.DerivedCategory.Ext.ZMod
public import Aglib.CategoryTheory.Sites.Point.SectionValues.OriginalMap

/-! # Original root higher-section generator transport

This is the actual cyclic section and original coefficient exchange. No curve,
point, trace, or properness model enters the transport of an arbitrary class.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

universe u w w'

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (p : X ⟶ S) (n : ℕ)
    (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤)))

/-- The original proper-exchange expression, before using properness. -/
def rootsHigherImagePullbackMap {T : Scheme.{u}} (t : T ⟶ S) (q : ℕ) :
    (inverseImage t).obj ((higherDirectImage p q).obj (mu X n)) ⟶
      (higherDirectImage (pullback.snd p t) q).obj (mu (pullback p t) n) :=
  (higherBaseChangeMap p (pullback.snd p t) t (pullback.fst p t)
    (IsPullback.of_hasPullback p t).w.symm q).app (mu X n) ≫
      (higherDirectImage (pullback.snd p t) q).map
        (rootsPullbackIso (pullback.fst p t) n hn hinv).hom

/-- The whole original roots arrow retains its defining factors before evaluation. -/
theorem rootsHigherImagePullbackMap_eq {T : Scheme.{u}} (t : T ⟶ S) (q : ℕ) :
    rootsHigherImagePullbackMap p n hn hinv t q =
      (higherBaseChangeMap p (pullback.snd p t) t (pullback.fst p t)
        (IsPullback.of_hasPullback p t).w.symm q).app (mu X n) ≫
          (higherDirectImage (pullback.snd p t) q).map
            (rootsPullbackIso (pullback.fst p t) n hn hinv).hom := rfl

/-- Original coefficient annihilation kills the section of every original class. -/
theorem rootsHigherSection_killed [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
    (q : ℕ) (x : Sheaf.H.{w} (mu X n) q) :
    n • cohomologyToHigherSections p (mu X n) q x = 0 := by
  rw [← map_nsmul]
  rw [Ext.nsmul_eq_zero_of_nsmul_id_right n (mu_killedBy X n), map_zero]

/-- The original roots exchange sends the original higher section to the
higher section of the original coefficient pullback class. -/
theorem rootsHigherImagePullbackMap_cohomologyToHigherSections
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
    {T : Scheme.{u}} (t : T ⟶ S)
    [HasExt.{w'} (AbelianSheaf.{u, u + 1} (pullback p t))]
    (q : ℕ) (x : Sheaf.H.{w} (mu X n) q) :
    (globalSections T).map (rootsHigherImagePullbackMap p n hn hinv t q)
      (globalSectionsPullback t _
        (cohomologyToHigherSections.{u, w} p (mu X n) q x)) =
    cohomologyToHigherSections.{u, w'} (pullback.snd p t) (mu (pullback p t) n) q
      (Kummer.rootsCohomologyPullback.{u, w, w'} (pullback.fst p t) n hn hinv q x) := by
  have h := higherBaseChangeMap_coefficientGlobalSections_hom.{u, w, w'}
    p (pullback.snd p t) t (pullback.fst p t)
    (IsPullback.of_hasPullback p t).w.symm
    (mu X n) (mu (pullback p t) n)
    (rootsPullbackIso (pullback.fst p t) n hn hinv).hom q
  exact OriginalSectionValues.mapped_germHom_apply_of_values (globalSections T)
    (rootsHigherImagePullbackMap p n hn hinv t q)
    (rootsHigherImagePullbackMap_eq p n hn hinv t q) (globalSectionsPullback t _)
    (cohomologyToHigherSections.{u, w} p (mu X n) q)
    (cohomologyToHigherSections.{u, w'} (pullback.snd p t) (mu (pullback p t) n) q) h
    (fun z => (globalSections T).map (rootsHigherImagePullbackMap p n hn hinv t q)
      (globalSectionsPullback t _
        (cohomologyToHigherSections.{u, w} p (mu X n) q z)))
    (fun _ => rfl) x
    (cohomologyToHigherSections.{u, w'} (pullback.snd p t) (mu (pullback p t) n) q
      (Kummer.rootsCohomologyPullback.{u, w, w'} (pullback.fst p t) n hn hinv q x)) rfl

/-- The original cyclic generator is transported to the original pulled-back
class, with independent source and target Ext worlds. -/
theorem rootsHigherSectionMap_pullback_adjoint_one
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
    {T : Scheme.{u}} (t : T ⟶ S)
    [HasExt.{w'} (AbelianSheaf.{u, u + 1} (pullback p t))]
    (q : ℕ) (x : Sheaf.H.{w} (mu X n) q) :
    (constantAdjunction T).homEquiv _ _
      (((inverseImageConstantIso t).app (ConstantFinite.value (ULift.{u} (ZMod n)))).inv ≫
        (inverseImage t).map (cyclicSectionMap _ n
          (cohomologyToHigherSections.{u, w} p (mu X n) q x)
          (rootsHigherSection_killed p n q x)) ≫
        rootsHigherImagePullbackMap p n hn hinv t q)
      (ULift.up (ULift.up (1 : ZMod n))) =
    cohomologyToHigherSections.{u, w'} (pullback.snd p t) (mu (pullback p t) n) q
      (Kummer.rootsCohomologyPullback.{u, w, w'} (pullback.fst p t) n hn hinv q x) := by
  exact (cyclicSectionMap_pullback_adjoint_one t _ _
    (rootsHigherImagePullbackMap p n hn hinv t q) n
    (cohomologyToHigherSections.{u, w} p (mu X n) q x)
    (rootsHigherSection_killed p n q x)).trans
      (rootsHigherImagePullbackMap_cohomologyToHigherSections.{u, w, w'}
        p n hn hinv t q x)

end AlgebraicGeometry.Scheme.EtaleCohomology
