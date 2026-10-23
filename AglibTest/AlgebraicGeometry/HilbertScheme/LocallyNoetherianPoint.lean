/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.HilbertScheme.LocallyNoetherianFunctor

/-! Focused consumer of the sheaf-level Grassmannian point of a Hilbert family over a locally
Noetherian base (Nitsure, arXiv:math/0504590v1, §5, pp. 25–26): the direct image `π_* 𝒪_Z(r)`,
the evaluation epimorphism, the point, its naturality and the natural transformation on locally
Noetherian test schemes, with axiom guards. -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open scoped Polynomial

universe u

/-- **(*) for `𝒪_Z(r)`**: `π_* 𝒪_Z(r)` is finite locally free of rank `⌊Φ(r)⌋₊`, and its formation
commutes with every base change. -/
example {A : Type u} [CommRing A] (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1)) {Φ : ℚ[X]}
    {T : Scheme.{u}} [IsLocallyNoetherian T] {g : T ⟶ Spec (CommRingCat.of A)}
    {Z : (pullback (toSpec A ι) g).IdealSheafData} (hZ : IsHilbertFamily ι Φ g Z) (r : ℕ)
    (hr : hilbertRegularityBound n Φ ≤ r) {T' : Scheme.{u}} (t : T' ⟶ T) :
    Scheme.Modules.SheafHasRank (directImageSheaf ι g Z r) ⌊Φ.eval (r : ℚ)⌋₊ ∧
      IsIso (Scheme.Modules.moduleBaseChangeMap (pullback.snd (toSpec A ι) g) t
        (familyQuotientTwist ι g Z r)) :=
  ⟨hZ.sheafHasRank_directImageSheaf ι n e r hr,
    hZ.isIso_moduleBaseChangeMap_directImageSheaf ι n e r hr t⟩

/-- **The evaluation map `𝒪_T^{monomials} ⟶ π_* 𝒪_Z(r)` is an epimorphism.** -/
example {A : Type u} [CommRing A] (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1)) {Φ : ℚ[X]}
    {T : Scheme.{u}} [IsLocallyNoetherian T] {g : T ⟶ Spec (CommRingCat.of A)}
    {Z : (pullback (toSpec A ι) g).IdealSheafData} (hZ : IsHilbertFamily ι Φ g Z) (r : ℕ)
    (hr : hilbertRegularityBound n Φ ≤ r) : Epi (directImageQuotientMap ι g Z r) :=
  hZ.epi_directImageQuotientMap ι n e r hr

/-- **The Grassmannian point is natural** in locally Noetherian test schemes over `Spec A`. -/
example {A : Type u} [CommRing A] (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1)) {Φ : ℚ[X]}
    {T : Scheme.{u}} [IsLocallyNoetherian T] {g : T ⟶ Spec (CommRingCat.of A)}
    {Z : (pullback (toSpec A ι) g).IdealSheafData} (hZ : IsHilbertFamily ι Φ g Z) (r : ℕ)
    (hr : hilbertRegularityBound n Φ ≤ r) {T' : Scheme.{u}} [IsLocallyNoetherian T']
    (g' : T' ⟶ Spec (CommRingCat.of A)) (f : T' ⟶ T) (h : f ≫ g = g') :
    Over.homMk f h ≫ hZ.grassmannianMap ι n e r hr =
      (hZ.comap ι f h).grassmannianMap ι n e r hr :=
  hZ.grassmannianMap_comp ι n e g' f h r hr

/-- **The map to the Grassmannian on locally Noetherian test schemes**: a natural transformation
from the restricted Hilbert functor to the restricted functor of points of the Grassmannian (its
injectivity is tested in `AglibTest/AlgebraicGeometry/HilbertScheme/Representability`). -/
example {A : Type u} [CommRing A] (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1)) (Φ : ℚ[X]) (r : ℕ)
    (hr : hilbertRegularityBound n Φ ≤ r) :
    (Scheme.locallyNoetherianOverInclusion (Spec (CommRingCat.of A))).op ⋙ hilbertFunctor ι Φ ⟶
      (Scheme.locallyNoetherianOverInclusion (Spec (CommRingCat.of A))).op ⋙
        yoneda.obj (Grassmannian.schemeOver (CommRingCat.of A) ⌊Φ.eval (r : ℚ)⌋₊
          ((n + r).choose r)) :=
  locallyNoetherianGrassmannianNatTrans ι n e A Φ r hr

/-- Every locally Noetherian test scheme is locally Noetherian, by instance. -/
example {S : Scheme.{u}} (T : Scheme.LocallyNoetherianOver S) : IsLocallyNoetherian T.obj.left :=
  inferInstance

/--
info: 'AlgebraicGeometry.Scheme.IdealSheafData.pullback_map_twistedRestriction' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Scheme.IdealSheafData.pullback_map_twistedRestriction

/--
info: 'AlgebraicGeometry.Scheme.Modules.pushforwardFreeMap_baseChange' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Scheme.Modules.pushforwardFreeMap_baseChange

/--
info: 'AlgebraicGeometry.Scheme.Modules.isIso_cartesianBaseChangeMap_of_isIso_moduleBaseChangeMap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Scheme.Modules.isIso_cartesianBaseChangeMap_of_isIso_moduleBaseChangeMap

/--
info: 'AlgebraicGeometry.ProjectiveSpace.projectiveCohomologyDim_quotientTwist_zero_cast' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms projectiveCohomologyDim_quotientTwist_zero_cast

/--
info: 'AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.fibreCohomologyConcentrated' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms IsHilbertFamily.fibreCohomologyConcentrated

/--
info: 'AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.sheafHasRank_directImageSheaf' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms IsHilbertFamily.sheafHasRank_directImageSheaf

/--
info: 'AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.isIso_moduleBaseChangeMap_directImageSheaf' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms IsHilbertFamily.isIso_moduleBaseChangeMap_directImageSheaf

/--
info: 'AlgebraicGeometry.ProjectiveSpace.directImageQuotientMap_baseChange' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms directImageQuotientMap_baseChange

/--
info: 'AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.isIso_cartesianBaseChangeMap_baseChangeMap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms IsHilbertFamily.isIso_cartesianBaseChangeMap_baseChangeMap

/--
info: 'AlgebraicGeometry.ProjectiveSpace.pullbackFreeMap_monomialMap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms pullbackFreeMap_monomialMap

/--
info: 'AlgebraicGeometry.ProjectiveSpace.epi_pushforwardFreeMap_monomialMap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms epi_pushforwardFreeMap_monomialMap

/--
info: 'AlgebraicGeometry.ProjectiveSpace.epi_pushforward_twistedRestriction' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms epi_pushforward_twistedRestriction

/--
info: 'AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.epi_directImageQuotientMap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms IsHilbertFamily.epi_directImageQuotientMap

/--
info: 'AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.grassmannianQuotient' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms IsHilbertFamily.grassmannianQuotient

/--
info: 'AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.grassmannianMap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms IsHilbertFamily.grassmannianMap

/--
info: 'AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.nonempty_isoUnder_pullback_grassmannianQuotient' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms IsHilbertFamily.nonempty_isoUnder_pullback_grassmannianQuotient

/--
info: 'AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.grassmannianMap_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms IsHilbertFamily.grassmannianMap_comp

/--
info: 'AlgebraicGeometry.ProjectiveSpace.locallyNoetherianGrassmannianNatTransApp_naturality' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms locallyNoetherianGrassmannianNatTransApp_naturality

/--
info: 'AlgebraicGeometry.ProjectiveSpace.locallyNoetherianGrassmannianNatTrans' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms locallyNoetherianGrassmannianNatTrans
