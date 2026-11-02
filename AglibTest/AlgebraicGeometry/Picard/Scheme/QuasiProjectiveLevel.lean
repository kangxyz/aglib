/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Scheme.QuasiProjectiveLevel

/-!
# Consumer checks for quasi-projective levels on a supplied Picard representative

The level and compact-image immersion results use the original `P,R`, with no additional
fine-stratum or rank-finiteness premise. The representing comparison is an equality of opens.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.RelativePicard AlgebraicGeometry.Scheme.RelativePicard.Strata

namespace AglibTest.PicardSchemeQuasiProjectiveLevel

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {ι : Type u} {X : Scheme.{u}}
  (i : X ⟶ ProjectiveSpace A ι) [IsClosedImmersion i] [Flat (i ≫ toSpec A ι)]
  [GeometricallyIntegral (i ≫ toSpec A ι)] {N : ℕ} (e : ι ≃ Fin (N + 1))
  (P : LocallyNoetherianOver (Spec (.of A)))
  (R : ((locallyNoetherianOverInclusion (Spec (.of A))).op ⋙
    (fppfPicardSheaf (i ≫ toSpec A ι)).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

example (φ : Polynomial ℚ) (m : ℤ) :
    IsHQuasiProjective
      (((coarseCondition i N e φ m).opens (T := P.obj) (R.homEquiv (𝟙 P))).ι ≫ P.obj.hom) :=
  isHQuasiProjective_opens_coarseCondition i e P R φ m

example {Y : Scheme.{u}} [CompactSpace Y] (j : Y ⟶ P.obj.left) [IsImmersion j]
    (φ : Polynomial ℚ)
    (hstratum : Set.range j ⊆
      (eulerCondition i N e φ).opens (T := P.obj) (R.homEquiv (𝟙 P))) :
    IsHQuasiProjective (j ≫ P.obj.hom) :=
  isHQuasiProjective_comp_of_isCompact_range_of_range_subset_eulerCondition i e P R j
    (isCompact_range j.continuous) φ hstratum

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.FiberCondition.preimage_opens_uniqueUpToIso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.FiberCondition.preimage_opens_uniqueUpToIso

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.isHQuasiProjective_opens_coarseCondition' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.isHQuasiProjective_opens_coarseCondition

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.isHQuasiProjective_comp_of_isCompact_range_of_range_subset_eulerCondition' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.isHQuasiProjective_comp_of_isCompact_range_of_range_subset_eulerCondition

end AglibTest.PicardSchemeQuasiProjectiveLevel
