/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.CoverEffacement
public import Aglib.AlgebraicGeometry.EtaleCohomology.SlicePullback.SourceSquare

/-! # Classwise effacement for original scheme pullback

The established integer-source square transports finite Galois effacement
from represented-source Ext to the original all-degree scheme pullback.
Source and target Ext universes remain independent. The intermediate slice
uses its native standard Ext universe only inside the proof.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Fields

universe u w w'

attribute [local instance] hasSheafifyLarge

/-- Vanishing after original represented-source restriction implies vanishing
after original geometric pullback, with exactly the established source square. -/
theorem cohomologyPullback_eq_zero_of_represented_precomp_eq_zero
    {X : Scheme.{u}} (U : X.Etale)
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{w'} (AbelianSheaf.{u, u + 1} U.left)]
    (F : AbelianSheaf.{u, u + 1} X) (n : ℕ) (α : Sheaf.H.{w} F n)
    (hα : (Ext.mk₀ (representedIntegerAugmentation U)).comp α (Nat.zero_add n) = 0) :
    cohomologyPullback.{u, w, w'} (X := X) (S := U.left) U.hom F n α = 0 := by
  let : HasExt.{u + 2}
      (Sheaf ((Scheme.smallEtaleTopology X).over U) AddCommGrpCat.{u + 1}) :=
    HasExt.standard _
  let e := ((Sheaf.functorH.{u + 2, u + 1, u, u + 1}
    ((Scheme.smallEtaleTopology X).over U) n).mapIso
      ((inverseImageSliceInverseIso U).app F)).addCommGroupIsoToAddEquiv
  let s := sliceCohomologyEquiv.{u, u + 1, u + 2, w'} U
    ((inverseImage (X := X) (S := U.left) U.hom).obj F) n
  let d := Sheaf.SliceCohomology.sliceComparison.{w, u + 2, u + 1, u, u + 1}
    (Scheme.smallEtaleTopology X) U F n
  apply s.injective
  apply e.injective
  have h := cohomologyPullback_sliceComparison.{u, w, w', u + 2} (X := X) U F n α
  have hz : e (s 0) = 0 := (congrArg e (map_zero s)).trans (map_zero e)
  exact h.trans ((congrArg d hα).trans ((map_zero d).trans hz.symm))

open Scheme.FiniteEtale Scheme.FiniteEtale.FieldGalois.Arbitrary

/-- Every positive original cohomology class vanishes after the original
pullback to an actual finite Galois field cover. -/
theorem exists_finiteGalois_cohomologyPullback_eq_zero
    (K : Type u) [Field K]
    [HasExt.{w} (AbelianSheaf.{u, u + 1} (Spec (.of K)))]
    [∀ L : FiniteGaloisIntermediateField K (SeparableClosure K),
      HasExt.{w'} (AbelianSheaf.{u, u + 1} (Spec (.of L)))]
    (F : AbelianSheaf.{u, u + 1} (Spec (.of K))) [HasInjectiveResolution F]
    (n : ℕ) (α : Sheaf.H.{w} F (n + 1)) :
    ∃ L : FiniteGaloisIntermediateField K (SeparableClosure K),
      cohomologyPullback.{u, w, w'} (Spec.algebraMap K L) F (n + 1) α = 0 := by
  obtain ⟨L, hL⟩ := exists_finiteGalois_ext_eq_zero K F n α
  refine ⟨L, ?_⟩
  let U := (toEtale _).obj (finiteFieldCover K L)
  let : HasExt.{w'} (AbelianSheaf.{u, u + 1} U.left) :=
    inferInstanceAs (HasExt.{w'} (AbelianSheaf.{u, u + 1} (Spec (.of L))))
  apply cohomologyPullback_eq_zero_of_represented_precomp_eq_zero
    (X := Spec (.of K)) U F (n + 1) α
  have hterminal : StrictlyLocal.terminalIsTerminal K =
      etaleTerminalIsTerminal (Spec (.of K)) := Subsingleton.elim _ _
  simpa only [representedIntegerAugmentation, hterminal] using hL

end AlgebraicGeometry.Scheme.EtaleCohomology.Fields
