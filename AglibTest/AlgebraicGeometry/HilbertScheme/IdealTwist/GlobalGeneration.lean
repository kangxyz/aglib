/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.HilbertScheme.IdealTwist.Untwist

/-! Focused consumer of the direct image and the relative global generation of the twisted ideal
sheaf of a Hilbert family over a locally Noetherian base (Nitsure, arXiv:math/0504590v1, §5,
pp. 26–27), with axiom guards. -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open scoped Polynomial

universe u

/-- **Relative global generation**: the counit `π^* π_* I_Z(r) ⟶ I_Z(r)` is an epimorphism. -/
example {A : Type u} [CommRing A] (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1)) {Φ : ℚ[X]}
    {T : Scheme.{u}} [IsLocallyNoetherian T] {g : T ⟶ Spec (CommRingCat.of A)}
    {Z : (pullback (toSpec A ι) g).IdealSheafData} (hZ : IsHilbertFamily ι Φ g Z) (r : ℤ)
    (hr : hilbertRegularityBound n Φ ≤ r) :
    Epi ((Scheme.Modules.pullbackPushforwardAdjunction (pullback.snd (toSpec A ι) g)).counit.app
      (familyIdealTwist ι g Z r)) :=
  hZ.epi_counit_familyIdealTwist ι n e r hr

/-- **The direct image** `π_* I_Z(r)` has rank `(n + r).choose r - ⌊Φ(r)⌋₊` and commutes with
every base change. -/
example {A : Type u} [CommRing A] (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1)) {Φ : ℚ[X]}
    {T : Scheme.{u}} [IsLocallyNoetherian T] {g : T ⟶ Spec (CommRingCat.of A)}
    {Z : (pullback (toSpec A ι) g).IdealSheafData} (hZ : IsHilbertFamily ι Φ g Z) (r : ℕ)
    (hr : hilbertRegularityBound n Φ ≤ r) {T' : Scheme.{u}} (f : T' ⟶ T) :
    Scheme.Modules.SheafHasRank
        ((Scheme.Modules.pushforward (pullback.snd (toSpec A ι) g)).obj
          (familyIdealTwist ι g Z r)) ((n + r).choose r - ⌊Φ.eval (r : ℚ)⌋₊) ∧
      IsIso (Scheme.Modules.moduleBaseChangeMap (pullback.snd (toSpec A ι) g) f
        (familyIdealTwist ι g Z r)) :=
  ⟨hZ.sheafHasRank_pushforward_familyIdealTwist ι n e r hr,
    hZ.isIso_moduleBaseChangeMap_familyIdealTwist ι n e r hr f⟩

/-- **The ideal of `Z` from the sections of `I_Z(r)`**, for an untwisting isomorphism. -/
example {A : Type u} [CommRing A] (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1)) {Φ : ℚ[X]}
    {T : Scheme.{u}} [IsLocallyNoetherian T] {g : T ⟶ Spec (CommRingCat.of A)}
    {Z : (pullback (toSpec A ι) g).IdealSheafData} (hZ : IsHilbertFamily ι Φ g Z) (r : ℕ)
    (hr : hilbertRegularityBound n Φ ≤ r) (L : (pullback (toSpec A ι) g).Modules)
    [Scheme.Modules.IsFiniteLocallyFree _ L]
    (u : (Scheme.Modules.moduleTensorLeftFunctor _ L).obj (familyIdealTwist ι g Z r) ≅
      Scheme.Hom.idealModule Z.subschemeι) :
    Scheme.Modules.Hom.imageIdealData
      ((Scheme.Modules.moduleTensorLeftFunctor _ L).map
          ((Scheme.Modules.pullbackPushforwardAdjunction (pullback.snd (toSpec A ι) g)).counit.app
            (familyIdealTwist ι g Z r)) ≫ u.hom ≫ Scheme.Hom.idealInclusion Z.subschemeι) = Z :=
  hZ.imageIdealData_tensor_counit ι n e r hr L u

/-- **`I_Z` is the image of `π^* π_* I_Z(r) ⊗ 𝒪(-r) ⟶ 𝒪`.** -/
example {A : Type u} [CommRing A] (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1)) {Φ : ℚ[X]}
    {T : Scheme.{u}} [IsLocallyNoetherian T] {g : T ⟶ Spec (CommRingCat.of A)}
    {Z : (pullback (toSpec A ι) g).IdealSheafData} (hZ : IsHilbertFamily ι Φ g Z) (r : ℕ)
    (hr : hilbertRegularityBound n Φ ≤ r) :
    Scheme.Modules.Hom.imageIdealData
      ((((Scheme.Modules.pullbackPushforwardAdjunction (pullback.snd (toSpec A ι) g)).counit.app
          (familyIdealTwist ι g Z r) ≫ familyIdealTwistInclusion ι Z r) ▷
            familyTwistingSheaf ι g (-r)) ≫ (familyTwistPairingIso ι g r).hom) = Z :=
  hZ.imageIdealData_twistPairing_counit ι n e r hr

/--
info: 'AlgebraicGeometry.Scheme.Modules.epi_of_restrict_openCover' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.epi_of_restrict_openCover

/--
info: 'AlgebraicGeometry.Scheme.Modules.epi_counit_of_epi_globalSectionsEval' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.epi_counit_of_epi_globalSectionsEval

/--
info: 'AlgebraicGeometry.Scheme.Modules.epi_pullback_counit_of_isPullback' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.epi_pullback_counit_of_isPullback

/--
info: 'AlgebraicGeometry.Scheme.Modules.relativeFlat_of_forall_isPullback' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.relativeFlat_of_forall_isPullback

/--
info: 'AlgebraicGeometry.ProjectiveSpace.pointMapIdealTwistIso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.pointMapIdealTwistIso

/--
info: 'AlgebraicGeometry.ProjectiveSpace.projectiveCohomologyDim_idealTwist_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.projectiveCohomologyDim_idealTwist_zero

/--
info: 'AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.fibreCohomologyConcentrated_familyIdealTwist' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.fibreCohomologyConcentrated_familyIdealTwist

/--
info: 'AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.relativeFlat_familyIdealTwist' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.relativeFlat_familyIdealTwist

/--
info: 'AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.sheafHasRank_pushforward_familyIdealTwist' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.sheafHasRank_pushforward_familyIdealTwist

/--
info: 'AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.isIso_moduleBaseChangeMap_familyIdealTwist' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.isIso_moduleBaseChangeMap_familyIdealTwist

/--
info: 'AlgebraicGeometry.ProjectiveSpace.isLimitPushforwardFamilyTwistedKernelFork' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.isLimitPushforwardFamilyTwistedKernelFork

/--
info: 'AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.epi_counit_familyIdealTwist' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.epi_counit_familyIdealTwist

/--
info: 'AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.imageIdealData_tensor_counit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.imageIdealData_tensor_counit

/--
info: 'CategoryTheory.MonoidalCategory.untwistIso_hom_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.MonoidalCategory.untwistIso_hom_comp

/--
info: 'CategoryTheory.Abelian.epi_of_isKernel_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Abelian.epi_of_isKernel_comp

/--
info: 'AlgebraicGeometry.ProjectiveSpace.epi_of_isKernel_pushforward_familyTwistedShortComplex' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.epi_of_isKernel_pushforward_familyTwistedShortComplex

/--
info: 'AlgebraicGeometry.ProjectiveSpace.familyIdealTwistLift_inclusion' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.familyIdealTwistLift_inclusion

/--
info: 'AlgebraicGeometry.ProjectiveSpace.imageIdealData_twistPairing_of_epi' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.imageIdealData_twistPairing_of_epi

/--
info: 'AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.epi_of_epi_homEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.epi_of_epi_homEquiv

/--
info: 'AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.imageIdealData_twistPairing_counit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.imageIdealData_twistPairing_counit

/--
info: 'AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.relativeFlat_idealModule' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.relativeFlat_idealModule
