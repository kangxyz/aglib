/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Finite.LocalNormAlgebra
public import Aglib.AlgebraicGeometry.Spec.CompletionLocalRing
public import Aglib.RingTheory.AdicCompletion.FiniteSemilocal

/-!
# Actual completed branches of the full finite local model

The full localized inverse-image algebra is the existing `LocalNormAlgebra.Ring`.
Its maximal branches are identified with the closed-fibre quotient branches used
by `FiniteSemilocal`. The same localization equivalence identifies their actual
maximal-adic completions with the original source-stalk completions. The original
stalk map, generic restriction and residue map remain explicit.

No uncompleted source stalk is assumed finite over the target stalk. Neither
normality, regularity, Noetherianity nor domainhood of a completion is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing
open IsDiscreteValuationRing.FiniteNorm

namespace AlgebraicGeometry.Scheme.Hom.LocalNormAlgebra

universe u

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (f : X ⟶ Y) [IsDominant f] [IsFinite f]
  (U : Y.Opens) (hU : IsAffineOpen U) (y : U) [Nonempty U]

attribute [local instance] chartAlgebra stalkAlgebra functionFieldAlgebra branchStalkAlgebra

local notation "R" => Y.presheaf.stalk y.val
local notation "S" => Ring f U hU y

omit [Nonempty U] in
/-- A maximal branch of the full finite algebra lies over the original target
stalk's maximal ideal, by integrality of this entire algebra. -/
theorem completionBranch_contraction (q : MaximalSpectrum S) :
    q.asIdeal.comap (algebraMap R S) = maximalIdeal R := by
  let : q.asIdeal.IsMaximal := q.isMaximal
  exact IsLocalRing.eq_maximalIdeal
    (Ideal.isMaximal_under_of_isIntegral_of_isMaximal q.asIdeal)

/-- The existing maximal branch, viewed as a maximal point of the original
closed-fibre quotient used by the full completion decomposition. -/
def completionBranch (q : MaximalSpectrum S) :
    AdicCompletion.FiniteSemilocal.Branch R S := by
  let : q.asIdeal.IsPrime := q.isMaximal.isPrime
  exact AdicCompletion.FiniteSemilocal.branchOfPrime R S q.asIdeal
    (completionBranch_contraction f U hU y q)

omit [Nonempty U] in
/-- Passing to the closed-fibre branch does not change its original ideal. -/
theorem branchIdeal_completionBranch (q : MaximalSpectrum S) :
    AdicCompletion.FiniteSemilocal.branchIdeal R S (completionBranch f U hU y q) =
      q.asIdeal := by
  let : q.asIdeal.IsPrime := q.isMaximal.isPrime
  exact AdicCompletion.FiniteSemilocal.branchIdeal_branchOfPrime R S q.asIdeal
    (completionBranch_contraction f U hU y q)

/-- The two branch presentations localize the same full finite algebra at
exactly the same maximal ideal. -/
def completionBranchLocalizationEquiv (q : MaximalSpectrum S) :
    AdicCompletion.FiniteSemilocal.Local R S (completionBranch f U hU y q) ≃ₐ[S]
      Localization.AtPrime q.asIdeal := by
  let : IsLocalization.AtPrime
      (AdicCompletion.FiniteSemilocal.Local R S (completionBranch f U hU y q))
      q.asIdeal := by
    have h :
        (AdicCompletion.FiniteSemilocal.branchIdeal R S (completionBranch f U hU y q)).primeCompl =
          q.asIdeal.primeCompl := by
      ext s
      change s ∉ AdicCompletion.FiniteSemilocal.branchIdeal R S
        (completionBranch f U hU y q) ↔ s ∉ q.asIdeal
      rw [branchIdeal_completionBranch]
    exact (congrArg (fun M : Submonoid S => IsLocalization M
      (AdicCompletion.FiniteSemilocal.Local R S (completionBranch f U hU y q))) h).mp
        inferInstance
  exact IsLocalization.algEquiv q.asIdeal.primeCompl _ _

/-- The actual branch localization is the original source stalk. -/
def completionBranchLocalEquiv (q : MaximalSpectrum S) :
    AdicCompletion.FiniteSemilocal.Local R S (completionBranch f U hU y q) ≃+*
      X.presheaf.stalk (branchPoint f U hU y q) :=
  (completionBranchLocalizationEquiv f U hU y q).toRingEquiv.trans
    (branchStalkEquiv f U hU y q).toRingEquiv

/-- The comparison retains the original target-stalk map, including its
specified equality of the image point with the original target point. -/
theorem completionBranchLocalEquiv_stalkMap (q : MaximalSpectrum S) :
    (completionBranchLocalEquiv f U hU y q).toRingHom.comp
      (algebraMap R
        (AdicCompletion.FiniteSemilocal.Local R S (completionBranch f U hU y q))) =
      stalkMapAt f (branchPoint f U hU y q) y.val (branchPoint_map f U hU y q) := by
  ext r
  change branchStalkEquiv f U hU y q
      (completionBranchLocalizationEquiv f U hU y q (algebraMap R _ r)) = _
  rw [IsScalarTower.algebraMap_apply R S
    (AdicCompletion.FiniteSemilocal.Local R S (completionBranch f U hU y q)),
    AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply R S (Localization.AtPrime q.asIdeal)]
  exact RingHom.congr_fun (branchStalkEquiv_stalkMap f U hU y q) r

/-- Both local presentations have the same original generic restriction map.
The fraction-field action is the already constructed branch localization action. -/
theorem completionBranchLocalEquiv_fraction (q : MaximalSpectrum S) :
    letI := branchFractionAlgebra (L := X.functionField) q
    (algebraMap (X.presheaf.stalk (branchPoint f U hU y q)) X.functionField).comp
      (completionBranchLocalEquiv f U hU y q).toRingHom =
        (algebraMap (Localization.AtPrime q.asIdeal) X.functionField).comp
          (completionBranchLocalizationEquiv f U hU y q).toRingHom := by
  let := branchFractionAlgebra (L := X.functionField) q
  change ((algebraMap (X.presheaf.stalk (branchPoint f U hU y q)) X.functionField).comp
    (branchStalkEquiv f U hU y q).toRingHom).comp
      (completionBranchLocalizationEquiv f U hU y q).toRingHom = _
  rw [branchStalkEquiv_fraction]

/-- The actual completed factor is the maximal-adic completion of the original
source stalk, obtained by completing the same local-ring equivalence. -/
def completedBranchStalkEquiv (q : MaximalSpectrum S) :
    AdicCompletion.FiniteSemilocal.Completed R S (completionBranch f U hU y q) ≃+*
      AdicCompletion (maximalIdeal (X.presheaf.stalk (branchPoint f U hU y q)))
        (X.presheaf.stalk (branchPoint f U hU y q)) :=
  Scheme.LocalRing.completionCongr (completionBranchLocalEquiv f U hU y q)

/-- Completion transport preserves every original local element. -/
theorem completedBranchStalkEquiv_algebraMap (q : MaximalSpectrum S)
    (z : AdicCompletion.FiniteSemilocal.Local R S (completionBranch f U hU y q)) :
    completedBranchStalkEquiv f U hU y q (algebraMap _ _ z) =
      algebraMap (X.presheaf.stalk (branchPoint f U hU y q)) _
        (completionBranchLocalEquiv f U hU y q z) :=
  Scheme.LocalRing.completionCongr_algebraMap (completionBranchLocalEquiv f U hU y q) z

/-- The canonical completed-base action gives the original stalk map on every
original base element, not an independently selected completed-ring embedding. -/
theorem completedBranchStalkEquiv_base (q : MaximalSpectrum S) (r : R) :
    letI := AdicCompletion.FiniteSemilocal.baseAlgebra R S (completionBranch f U hU y q)
    completedBranchStalkEquiv f U hU y q
      (algebraMap (AdicCompletion (maximalIdeal R) R) _
        (algebraMap R (AdicCompletion (maximalIdeal R) R) r)) =
      algebraMap (X.presheaf.stalk (branchPoint f U hU y q)) _
        (stalkMapAt f (branchPoint f U hU y q) y.val (branchPoint_map f U hU y q) r) := by
  let := AdicCompletion.FiniteSemilocal.baseAlgebra R S (completionBranch f U hU y q)
  rw [AdicCompletion.FiniteSemilocal.base_algebraMap,
    completedBranchStalkEquiv_algebraMap]
  exact congrArg (algebraMap (X.presheaf.stalk (branchPoint f U hU y q)) _)
    (RingHom.congr_fun (completionBranchLocalEquiv_stalkMap f U hU y q) r)

omit [Nonempty U] in
/-- The original base-to-branch localization map is local by the actual closed
point contraction. This does not assert that the localization is a finite module. -/
theorem completionBranch_isLocalHom (q : MaximalSpectrum S) :
    IsLocalHom (algebraMap R
      (AdicCompletion.FiniteSemilocal.Local R S (completionBranch f U hU y q))) :=
  AdicCompletion.FiniteLocalization.isLocalHom
    (AdicCompletion.FiniteSemilocal.branchIdeal R S (completionBranch f U hU y q))
    (AdicCompletion.FiniteSemilocal.branch_contraction R S (completionBranch f U hU y q))

attribute [local instance] completionBranch_isLocalHom

/-- The residue equivalence is induced by the same original stalk equivalence. -/
def completionBranchResidueEquiv (q : MaximalSpectrum S) :
    ResidueField
      (AdicCompletion.FiniteSemilocal.Local R S (completionBranch f U hU y q)) ≃+*
        X.residueField (branchPoint f U hU y q) :=
  ResidueField.mapEquiv (completionBranchLocalEquiv f U hU y q)

/-- The branch residue comparison preserves the original structural residue map. -/
theorem completionBranchResidueEquiv_stalkMap (q : MaximalSpectrum S) :
    (completionBranchResidueEquiv f U hU y q).toRingHom.comp
      (ResidueField.map (algebraMap R
        (AdicCompletion.FiniteSemilocal.Local R S (completionBranch f U hU y q)))) =
      ResidueField.map
        (stalkMapAt f (branchPoint f U hU y q) y.val (branchPoint_map f U hU y q)) := by
  ext a
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective a
  change IsLocalRing.residue (X.presheaf.stalk (branchPoint f U hU y q))
      (completionBranchLocalEquiv f U hU y q (algebraMap R _ r)) =
    IsLocalRing.residue (X.presheaf.stalk (branchPoint f U hU y q))
      (stalkMapAt f (branchPoint f U hU y q) y.val (branchPoint_map f U hU y q) r)
  exact congrArg (IsLocalRing.residue (X.presheaf.stalk (branchPoint f U hU y q)))
    (RingHom.congr_fun (completionBranchLocalEquiv_stalkMap f U hU y q) r)

/-- Every actual closed source point above the selected target point is an
actual completed factor of the full finite local algebra. Its comparison keeps
the original source stalk and the original target-stalk coefficient map. -/
theorem exists_completedBranchStalkEquiv
    (x : X) (hx : IsClosed ({x} : Set X)) (hfx : f x = y.val) :
    ∃ q : MaximalSpectrum S, branchPoint f U hU y q = x ∧
      ∃ e : AdicCompletion.FiniteSemilocal.Completed R S (completionBranch f U hU y q) ≃+*
          AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x),
        letI := AdicCompletion.FiniteSemilocal.baseAlgebra R S (completionBranch f U hU y q)
        ∀ r : R, e
          (algebraMap (AdicCompletion (maximalIdeal R) R) _
            (algebraMap R (AdicCompletion (maximalIdeal R) R) r)) =
          algebraMap (X.presheaf.stalk x) _ (stalkMapAt f x y.val hfx r) := by
  obtain ⟨q, rfl⟩ := exists_branch f U hU y x hx hfx
  exact ⟨q, rfl, completedBranchStalkEquiv f U hU y q,
    completedBranchStalkEquiv_base f U hU y q⟩

end AlgebraicGeometry.Scheme.Hom.LocalNormAlgebra
