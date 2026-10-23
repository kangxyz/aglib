/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.HenselianResidue
public import Aglib.AlgebraicGeometry.Group.RootsFiniteEtale
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.Coefficients
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Actual roots over a strictly henselian local spectrum

The original finite-etale section-lifting theorem makes restriction of actual
root sections a multiplicative equivalence. Separably closed residue fields
then supply cyclic coordinates without an arithmetic marking premise.
This is the section-level supplier, not yet the constant-sheaf comparison.
-/

@[expose] public section
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Group
open scoped CategoryTheory.MonObj
open GroupCohomology.Kummer.Coefficients

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.HenselianConstant

universe u
variable (R : Type u) [CommRing R] [HenselianLocalRing R]

attribute [local instance] Over.cartesianMonoidalCategory

/-- The actual residue point regarded as an arrow to the terminal cover. -/
def residueToTerminal :
    Over.mk (Scheme.LocalRing.residueSpecMap R) ⟶ Over.mk (𝟙 (Spec (.of R))) :=
  Over.homMk (Scheme.LocalRing.residueSpecMap R) (by simp)

variable (n : ℕ)
/-- The native commutative group structure on the actual scheme of n-th roots. -/
local instance : CommGrpObj (MultiplicativeGroup.rootsScheme (Spec (.of R)) n) :=
  MultiplicativeGroup.rootsCommGroup (Spec (.of R)) n

/-- Restriction of original root sections to the residue point. -/
def rootSectionRestriction :
    (Over.mk (𝟙 (Spec (.of R))) ⟶ MultiplicativeGroup.rootsScheme (Spec (.of R)) n) →*
      (Over.mk (Scheme.LocalRing.residueSpecMap R) ⟶
        MultiplicativeGroup.rootsScheme (Spec (.of R)) n) where
  toFun s := residueToTerminal R ≫ s
  map_one' := MonObj.comp_one _
  map_mul' a b := MonObj.comp_mul _ a b

/-- The actual root restriction is bijective by finite-etale henselian section lifting. -/
theorem rootSectionRestriction_bijective (hn : 0 < n)
    (hinv : IsUnit (n : Γ(Spec (.of R), ⊤))) :
    Function.Bijective (rootSectionRestriction R n) := by
  let Y := MultiplicativeGroup.rootsScheme (Spec (.of R)) n
  let : IsFinite Y.hom := RootsFiniteEtale.rootsScheme_finite _ n hn
  let : Etale Y.hom := RootsFiniteEtale.rootsScheme_etale _ n hn hinv
  constructor
  · intro a b hab
    obtain ⟨s, _, hs⟩ := Scheme.FiniteEtale.HenselianResidue.existsUnique_section_lift
      R Y.hom ((residueToTerminal R ≫ a).left) (Over.w (residueToTerminal R ≫ a))
    apply Over.OverMorphism.ext
    exact (hs a.left ⟨a.w, rfl⟩).trans
      (hs b.left ⟨b.w, (congrArg (fun k => k.left) hab).symm⟩).symm
  · intro t
    obtain ⟨s, ⟨hs, hst⟩, _⟩ :=
      Scheme.FiniteEtale.HenselianResidue.existsUnique_section_lift R Y.hom t.left t.w
    refine ⟨Over.homMk s hs, ?_⟩
    apply Over.OverMorphism.ext
    exact hst

/-- Original global root sections are multiplicatively equivalent to residue root points. -/
def rootSectionResidueEquiv (hn : 0 < n)
    (hinv : IsUnit (n : Γ(Spec (.of R), ⊤))) :
    (Over.mk (𝟙 (Spec (.of R))) ⟶ MultiplicativeGroup.rootsScheme (Spec (.of R)) n) ≃*
      (Over.mk (Scheme.LocalRing.residueSpecMap R) ⟶
        MultiplicativeGroup.rootsScheme (Spec (.of R)) n) :=
  MulEquiv.ofBijective (rootSectionRestriction R n)
    (rootSectionRestriction_bijective R n hn hinv)

/-- Root points use the original representability coordinates and the native Gamma/Spec iso. -/
def residueRootCoordinates :
    (Over.mk (Scheme.LocalRing.residueSpecMap R) ⟶
      MultiplicativeGroup.rootsScheme (Spec (.of R)) n) ≃*
      rootsOfUnity n (IsLocalRing.ResidueField R) := by
  let e := (Scheme.ΓSpecIso (.of (IsLocalRing.ResidueField R))).commRingCatIsoToRingEquiv
  exact (rootsMulEquiv (Spec (.of R)) n
    (Over.mk (Scheme.LocalRing.residueSpecMap R))).trans (e.toMulEquiv.restrictRootsOfUnity n)

/-- Invertibility in global sections implies nonzero level in the residue field. -/
theorem residueLevel_ne_zero (hinv : IsUnit (n : Γ(Spec (.of R), ⊤))) :
    (n : IsLocalRing.ResidueField R) ≠ 0 := by
  have h := (hinv.map (Scheme.LocalRing.residueSpecMap R).appTop.hom).map
    (Scheme.ΓSpecIso (.of (IsLocalRing.ResidueField R))).hom.hom
  simpa only [map_natCast] using h.ne_zero

/-- Cyclic coordinates on roots over a separably closed field. -/
def fieldCyclicCoordinates (k : Type u) [Field k] [IsSepClosed k]
    (n : ℕ) [NeZero n] [NeZero (n : k)] : ZMod n ≃+ Additive (rootsOfUnity n k) := by
  let ζ := Classical.choose (HasEnoughRootsOfUnity.exists_primitiveRoot k n)
  have hζ : IsPrimitiveRoot ζ n :=
    Classical.choose_spec (HasEnoughRootsOfUnity.exists_primitiveRoot k n)
  let u := (hζ.isUnit (NeZero.ne n)).unit
  have hu : IsPrimitiveRoot u n := hζ.isUnit_unit (NeZero.ne n)
  exact hu.zmodEquivZPowers.trans (MulEquiv.subgroupCongr hu.zpowers_eq).toAdditive

variable [IsSepClosed (IsLocalRing.ResidueField R)]

/-- Chosen cyclic coordinates on actual global root sections, with no marking input. -/
def globalRootCoordinates (hn : 0 < n)
    (hinv : IsUnit (n : Γ(Spec (.of R), ⊤))) :
    ZMod n ≃+ Additive
      (Over.mk (𝟙 (Spec (.of R))) ⟶ MultiplicativeGroup.rootsScheme (Spec (.of R)) n) := by
  letI : NeZero n := ⟨hn.ne'⟩
  letI : NeZero (n : IsLocalRing.ResidueField R) := ⟨residueLevel_ne_zero R n hinv⟩
  exact (fieldCyclicCoordinates (IsLocalRing.ResidueField R) n).trans
    ((rootSectionResidueEquiv R n hn hinv).trans (residueRootCoordinates R n)).symm.toAdditive

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.HenselianConstant
