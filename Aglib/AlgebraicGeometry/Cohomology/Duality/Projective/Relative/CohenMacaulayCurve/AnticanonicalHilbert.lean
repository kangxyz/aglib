/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.FiniteScheme
public import Aglib.AlgebraicGeometry.Cohomology.Exact.Euler
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.CohenMacaulayCurve.Generation.RegularCanonicalSection
public import Aglib.AlgebraicGeometry.Modules.Invertible.Power.Pullback
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Tensor.Exact

/-!
# The Hilbert function from an actual anticanonical Cartier divisor

The original ideal row computes the section dimension of the full finite
Cartier divisor. Its original tensor rows then compute every positive power
of the dual ideal line. Neither the curve nor its divisor is replaced by its
reduction. No Hilbert polynomial, degree formula, or Hilbert-function identity
is assumed.

The original ideal cohomology or three actual sections of its dual line
compute the finite divisor's dimension. Both suppliers use the same power
induction. The first-power route needs no canonical identification or inverse
cohomology; neither route asserts a Cartier representative over the ground field.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.OverField

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

private theorem line_cartierCoefficientSequence_shortExact
    {D C : Scheme.{u}} (i : D ⟶ C) [IsClosedImmersion i]
    (hI : IsLocallyRankOne C (idealModule i)) (M : LineBundle C) :
    (cartierCoefficientSequence i hI M.val).ShortExact := by
  let L := dualLineBundle C ⟨idealModule i, hI⟩
  let N := tensorLineBundle C L M
  let : IsFiniteLocallyFree C N.val := lineBundle_isFiniteLocallyFree N
  have hS : (idealTensorQuotientSequence i N.val).ShortExact :=
    ShortComplex.shortExact_of_iso (idealTensorQuotientSequenceIso i N.val)
      (tensor_shortExact_finiteLocallyFree N.val (idealSequence i)
        (idealSequence_shortExact i))
  exact ShortComplex.shortExact_of_iso (cartierCoefficientSequenceIso i hI M.val) hS

private theorem finite_pushforward_h1
    {k : Type u} [Field k] (X : FScheme k) {D : Scheme.{u}}
    (i : D ⟶ X.left) [IsClosedImmersion i] [IsFinite (i ≫ X.hom)]
    (M : D.Modules) :
    Subsingleton (moduleCohomology k X ((pushforward i).obj M) 1) :=
  CanonicalEnlargement.finiteSupport_positive
    (CanonicalEnlargement.finiteClosedSupport_pushforward_finite k i X.hom M) 0

/-- The literal ideal row computes the full finite divisor's H0 dimension
from the actual ideal cohomology. In particular nilpotents contribute to the
dimension. No projective embedding or reducedness hypothesis is needed. -/
theorem finiteCartier_h0_finrank_of_ideal_cohomology
    {k : Type u} [Field k] (X : FScheme k) {D : Scheme.{u}}
    (i : D ⟶ X.left) [IsClosedImmersion i] [IsFinite (i ≫ X.hom)]
    [Subsingleton (moduleCohomology k X (SheafOfModules.unit X.left.ringCatSheaf) 1)]
    [Subsingleton (moduleCohomology k X (idealModule i) 0)]
    (hO : Module.finrank k
      (moduleCohomology k X (SheafOfModules.unit X.left.ringCatSheaf) 0) = 1)
    (hI : Module.finrank k (moduleCohomology k X (idealModule i) 1) = 1) :
    Module.finrank k (moduleCohomology k X
      ((pushforward i).obj (SheafOfModules.unit D.ringCatSheaf)) 0) = 2 := by
  let S := idealSequence i
  have hS := idealSequence_shortExact i
  let : Module.Finite k
      (moduleCohomology k X (SheafOfModules.unit X.left.ringCatSheaf) 0) :=
    Module.finite_of_finrank_pos (by rw [hO]; decide)
  let : Module.Free k (moduleCohomology k X (idealModule i) 1) :=
    Module.Free.of_divisionRing k (moduleCohomology k X (idealModule i) 1)
  let : Module.Finite k (moduleCohomology k X (idealModule i) 1) :=
    Module.finite_of_finrank_pos (by rw [hI]; decide)
  let : Subsingleton (moduleCohomology k X S.X₁ 0) :=
    inferInstanceAs (Subsingleton (moduleCohomology k X (idealModule i) 0))
  let : Subsingleton (moduleCohomology k X S.X₂ 1) :=
    inferInstanceAs (Subsingleton
      (moduleCohomology k X (SheafOfModules.unit X.left.ringCatSheaf) 1))
  let : Module.Finite k (moduleCohomology k X S.X₂ 0) :=
    inferInstanceAs (Module.Finite k
      (moduleCohomology k X (SheafOfModules.unit X.left.ringCatSheaf) 0))
  let : Module.Finite k (moduleCohomology k X S.X₁ 1) :=
    inferInstanceAs (Module.Finite k (moduleCohomology k X (idealModule i) 1))
  let : Module.Finite k (moduleCohomology k X S.X₃ 0) :=
    finite_middle_of_exact (moduleCohomologyMap X S.g 0)
      (moduleCohomologyConnecting X S hS 0)
      (moduleCohomologyConnecting_exact_left X S hS 0)
  let : Subsingleton (moduleCohomology k X S.X₃ 1) :=
    finite_pushforward_h1 X i (SheafOfModules.unit D.ringCatSheaf)
  have h := QuotientEuler.moduleEulerQuotient_dim X S hS
  have h₀ : Module.finrank k (moduleCohomology k X S.X₁ 0) = 0 :=
    Module.finrank_zero_of_subsingleton
  have h₁ : Module.finrank k (moduleCohomology k X S.X₂ 1) = 0 :=
    Module.finrank_zero_of_subsingleton
  change (Module.finrank k (moduleCohomology k X S.X₃ 0) : ℤ) =
    (Module.finrank k
      (moduleCohomology k X (SheafOfModules.unit X.left.ringCatSheaf) 0) : ℤ) -
    (Module.finrank k (moduleCohomology k X S.X₁ 0) : ℤ) +
    (Module.finrank k (moduleCohomology k X (idealModule i) 1) : ℤ) -
    (Module.finrank k (moduleCohomology k X S.X₂ 1) : ℤ) at h
  rw [hO, hI, h₀, h₁] at h
  change Module.finrank k (moduleCohomology k X S.X₃ 0) = 2
  omega

private theorem finiteCartier_line_step
    {k : Type u} [Field k] (X : FScheme k) {D : Scheme.{u}}
    (i : D ⟶ X.left) [IsClosedImmersion i] [IsFinite (i ≫ X.hom)]
    (hI : IsLocallyRankOne X.left (idealModule i)) (M : LineBundle X.left)
    [Module.Finite k (moduleCohomology k X M.val 0)]
    [Subsingleton (moduleCohomology k X M.val 1)]
    (hD : Module.finrank k (moduleCohomology k X
      ((pushforward i).obj (SheafOfModules.unit D.ringCatSheaf)) 0) = 2) :
    let N := tensorLineBundle X.left (dualLineBundle X.left ⟨idealModule i, hI⟩) M
    Subsingleton (moduleCohomology k X N.val 1) ∧
      Module.finrank k (moduleCohomology k X N.val 0) =
        Module.finrank k (moduleCohomology k X M.val 0) + 2 := by
  let L := dualLineBundle X.left ⟨idealModule i, hI⟩
  let N := tensorLineBundle X.left L M
  let S := cartierCoefficientSequence i hI M.val
  have hS : S.ShortExact := line_cartierCoefficientSequence_shortExact i hI M
  let : Subsingleton (moduleCohomology k X S.X₁ 1) :=
    inferInstanceAs (Subsingleton (moduleCohomology k X M.val 1))
  let : Module.Finite k (moduleCohomology k X S.X₁ 0) :=
    inferInstanceAs (Module.Finite k (moduleCohomology k X M.val 0))
  have hQ : Module.finrank k (moduleCohomology k X S.X₃ 0) = 2 :=
    (finiteSchemeLine_pushforward_h0_finrank X i (pullbackLineBundle i N)).trans hD
  let : Module.Finite k (moduleCohomology k X S.X₃ 0) :=
    Module.finite_of_finrank_pos (by omega)
  let : Subsingleton (moduleCohomology k X S.X₃ 1) :=
    finite_pushforward_h1 X i ((Modules.pullback i).obj N.val)
  let : Subsingleton (moduleCohomology k X S.X₂ 1) :=
    (QuotientEuler.moduleH1Map_surjective X S hS).subsingleton
  let : Module.Finite k (moduleCohomology k X S.X₂ 0) :=
    moduleCohomology_finite_middle X S hS 0
  have h := QuotientEuler.moduleEulerQuotient_dim X S hS
  have h₁ : Module.finrank k (moduleCohomology k X S.X₁ 1) = 0 :=
    Module.finrank_zero_of_subsingleton
  have h₂ : Module.finrank k (moduleCohomology k X S.X₂ 1) = 0 :=
    Module.finrank_zero_of_subsingleton
  rw [hQ, h₁, h₂] at h
  refine ⟨inferInstanceAs (Subsingleton (moduleCohomology k X S.X₂ 1)), ?_⟩
  change Module.finrank k (moduleCohomology k X S.X₂ 0) =
    Module.finrank k (moduleCohomology k X S.X₁ 0) + 2
  omega

/-- The original positive Cartier rows compute every dual-ideal power from
actual rank-two finite-divisor sections and the original unit cohomology. -/
theorem finiteCartier_dualIdealPower_cohomology_of_divisor_rank
    {k : Type u} [Field k] (X : FScheme k) {D : Scheme.{u}}
    (i : D ⟶ X.left) [IsClosedImmersion i] [IsFinite (i ≫ X.hom)]
    (hI : IsLocallyRankOne X.left (idealModule i))
    [Subsingleton (moduleCohomology k X (SheafOfModules.unit X.left.ringCatSheaf) 1)]
    (hO : Module.finrank k
      (moduleCohomology k X (SheafOfModules.unit X.left.ringCatSheaf) 0) = 1)
    (hD : Module.finrank k (moduleCohomology k X
      ((pushforward i).obj (SheafOfModules.unit D.ringCatSheaf)) 0) = 2) (r : ℕ) :
    let L := dualLineBundle X.left ⟨idealModule i, hI⟩
    Subsingleton (moduleCohomology k X (tensorPowerLineBundle X.left L r).val 1) ∧
      Module.finrank k (moduleCohomology k X (tensorPowerLineBundle X.left L r).val 0) =
        2 * r + 1 := by
  let L := dualLineBundle X.left ⟨idealModule i, hI⟩
  induction r with
  | zero =>
    let E := PowerPullback.freeUnitIso X.left
    refine ⟨(moduleCohomologyIso X E 1).injective.subsingleton, ?_⟩
    exact (moduleCohomologyIso X E 0).finrank_eq.trans hO
  | succ r ih =>
    let M := tensorPowerLineBundle X.left L r
    have hi : Module.finrank k (moduleCohomology k X M.val 0) = 2 * r + 1 := ih.2
    let : Subsingleton (moduleCohomology k X M.val 1) := ih.1
    let : Module.Finite k (moduleCohomology k X M.val 0) :=
      Module.finite_of_finrank_pos (by rw [hi]; omega)
    have hs := finiteCartier_line_step X i hI M hD
    refine ⟨hs.1, ?_⟩
    change Module.finrank k
      (moduleCohomology k X (tensorLineBundle X.left L M).val 0) = 2 * (r + 1) + 1
    rw [hs.2, hi]
    omega

/-- The genuine Hilbert function of the dual ideal of a finite anticanonical
Cartier divisor. The hypotheses concern actual H0 and H1 of the structure and
ideal sheaves, not their Hilbert functions. Exactness proves the positive-power
H1 vanishing as well as the entire formula `2 * r + 1`. -/
theorem finiteCartier_dualIdealPower_cohomology
    {k : Type u} [Field k] (X : FScheme k) {D : Scheme.{u}}
    (i : D ⟶ X.left) [IsClosedImmersion i] [IsFinite (i ≫ X.hom)]
    (hI : IsLocallyRankOne X.left (idealModule i))
    [Subsingleton (moduleCohomology k X (SheafOfModules.unit X.left.ringCatSheaf) 1)]
    [Subsingleton (moduleCohomology k X (idealModule i) 0)]
    (hO : Module.finrank k
      (moduleCohomology k X (SheafOfModules.unit X.left.ringCatSheaf) 0) = 1)
    (hJ : Module.finrank k (moduleCohomology k X (idealModule i) 1) = 1) (r : ℕ) :
    let L := dualLineBundle X.left ⟨idealModule i, hI⟩
    Subsingleton (moduleCohomology k X (tensorPowerLineBundle X.left L r).val 1) ∧
      Module.finrank k (moduleCohomology k X (tensorPowerLineBundle X.left L r).val 0) =
        2 * r + 1 := by
  exact finiteCartier_dualIdealPower_cohomology_of_divisor_rank X i hI hO
    (finiteCartier_h0_finrank_of_ideal_cohomology X i hO hJ) r

/-- Three original dual-ideal sections and the original unit cohomology
compute the full finite Cartier divisor's section rank. -/
theorem finiteCartier_h0_finrank_of_dualIdeal_h0
    {k : Type u} [Field k] (X : FScheme k) {D : Scheme.{u}}
    (i : D ⟶ X.left) [IsClosedImmersion i] [IsFinite (i ≫ X.hom)]
    (hI : IsLocallyRankOne X.left (idealModule i))
    [Subsingleton (moduleCohomology k X (SheafOfModules.unit X.left.ringCatSheaf) 1)]
    (hO : Module.finrank k
      (moduleCohomology k X (SheafOfModules.unit X.left.ringCatSheaf) 0) = 1)
    (hL : Module.finrank k (moduleCohomology k X
      (dualLineBundle X.left ⟨idealModule i, hI⟩).val 0) = 3) :
    Module.finrank k (moduleCohomology k X
      ((pushforward i).obj (SheafOfModules.unit D.ringCatSheaf)) 0) = 2 := by
  let U := trivialLineBundle X.left
  let L := dualLineBundle X.left ⟨idealModule i, hI⟩
  let N := tensorLineBundle X.left L U
  let S := cartierCoefficientSequence i hI U.val
  have hS : S.ShortExact := line_cartierCoefficientSequence_shortExact i hI U
  let eU : U.val ≅ SheafOfModules.unit X.left.ringCatSheaf :=
    PowerPullback.freeUnitIso X.left
  let eN : N.val ≅ L.val :=
    tensorSheafIso X.left (Iso.refl L.val) eU ≪≫
      (SheafOfModulesOfCommRing.tensorRightUnitIso X.left.sheaf).app L.val
  let : Subsingleton (moduleCohomology k X S.X₁ 1) :=
    (moduleCohomologyIso X eU 1).injective.subsingleton
  have hU : Module.finrank k (moduleCohomology k X S.X₁ 0) = 1 :=
    (moduleCohomologyIso X eU 0).finrank_eq.trans hO
  have hN : Module.finrank k (moduleCohomology k X S.X₂ 0) = 3 :=
    (moduleCohomologyIso X eN 0).finrank_eq.trans hL
  let : Module.Finite k (moduleCohomology k X S.X₂ 0) :=
    Module.finite_of_finrank_pos (by rw [hN]; decide)
  have hsurj : Function.Surjective (moduleCohomologyMap X S.g 0) := by
    intro x
    exact (moduleCohomologyConnecting_exact_left X S hS 0 x).mp
      (Subsingleton.elim _ _)
  let : Module.Finite k (moduleCohomology k X S.X₃ 0) :=
    Module.Finite.of_surjective (moduleCohomologyMap X S.g 0) hsurj
  let : Subsingleton (moduleCohomology k X S.X₃ 1) :=
    finite_pushforward_h1 X i ((Modules.pullback i).obj N.val)
  let : Subsingleton (moduleCohomology k X S.X₂ 1) :=
    (QuotientEuler.moduleH1Map_surjective X S hS).subsingleton
  have h := QuotientEuler.moduleEulerQuotient_dim X S hS
  have h₁ : Module.finrank k (moduleCohomology k X S.X₁ 1) = 0 :=
    Module.finrank_zero_of_subsingleton
  have h₂ : Module.finrank k (moduleCohomology k X S.X₂ 1) = 0 :=
    Module.finrank_zero_of_subsingleton
  rw [hU, hN, h₁, h₂] at h
  have hQ : Module.finrank k (moduleCohomology k X S.X₃ 0) = 2 := by omega
  exact (finiteSchemeLine_pushforward_h0_finrank X i (pullbackLineBundle i N)).symm.trans hQ

/-- The positive Cartier recurrence derives every original dual-ideal
power from three first-power sections, without inverse-line cohomology. -/
theorem finiteCartier_dualIdealPower_cohomology_of_firstPower
    {k : Type u} [Field k] (X : FScheme k) {D : Scheme.{u}}
    (i : D ⟶ X.left) [IsClosedImmersion i] [IsFinite (i ≫ X.hom)]
    (hI : IsLocallyRankOne X.left (idealModule i))
    [Subsingleton (moduleCohomology k X (SheafOfModules.unit X.left.ringCatSheaf) 1)]
    (hO : Module.finrank k
      (moduleCohomology k X (SheafOfModules.unit X.left.ringCatSheaf) 0) = 1)
    (hL : Module.finrank k (moduleCohomology k X
      (dualLineBundle X.left ⟨idealModule i, hI⟩).val 0) = 3) (r : ℕ) :
    let L := dualLineBundle X.left ⟨idealModule i, hI⟩
    Subsingleton (moduleCohomology k X (tensorPowerLineBundle X.left L r).val 1) ∧
      Module.finrank k (moduleCohomology k X (tensorPowerLineBundle X.left L r).val 0) =
        2 * r + 1 := by
  exact finiteCartier_dualIdealPower_cohomology_of_divisor_rank X i hI hO
    (finiteCartier_h0_finrank_of_dualIdeal_h0 X i hI hO hL) r

end AlgebraicGeometry.Scheme.Cohomology
