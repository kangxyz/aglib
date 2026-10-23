/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Formal.Algebraization
public import Aglib.AlgebraicGeometry.Modules.Invertible.Formal.System.Realization
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.Proper

/-!
# Actual line bundles realizing compatible formal line bundles

Native proper coherent effectivity first supplies the module and a full
isomorphism of its completion with the original formal system. The positive
geometric comparison and the rank-one algebraization theorem then make that
same module an actual line bundle.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open AlgebraicGeometry.Scheme.Modules.Coherent

namespace AlgebraicGeometry.Scheme.Modules.Invertible.CompatibleLineBundleSystem

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  {I : Ideal R} [IsAdicComplete I R] {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of R)} [IsProper f]
  (S : CompatibleLineBundleSystem f I)

/-- Any actual coherent realization of the original formal system is locally
rank one, using its original geometric reduction isomorphisms. -/
theorem isLocallyRankOne_of_completionIso [IsLocallyNoetherian X]
    (M : X.CoherentSheaf)
    (β : (completionFunctor X (idealThickeningIdealSheaf f I)).obj M ≅ S.toAdicSystem) :
    IsLocallyRankOne X M.obj := by
  apply isLocallyRankOne_of_proper_positiveThickening I f M.obj M.property
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  exact isLocallyRankOne_of_iso _ (S.geometricReductionIso M β k).symm (S.bundle k).property

/-- The actual coherent module chosen by the native proper completion equivalence. -/
def algebraizedModule :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    X.CoherentSheaf := by
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  exact (Scheme.Cohomology.properCompletionEquivalence I f).inverse.obj S.toAdicSystem

/-- The full original formal comparison supplied by proper coherent effectivity. -/
def algebraizedCompletionIso :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    (completionFunctor X (idealThickeningIdealSheaf f I)).obj S.algebraizedModule ≅
      S.toAdicSystem := by
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  exact (Scheme.Cohomology.properCompletionEquivalence I f).counitIso.app S.toAdicSystem

/-- The coherent algebraization is an actual line bundle on the original proper scheme. -/
def algebraizedLineBundle : LineBundle X := by
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  exact ⟨S.algebraizedModule.obj,
    S.isLocallyRankOne_of_completionIso S.algebraizedModule S.algebraizedCompletionIso⟩

/-- Every original positive geometric reduction of the algebraized line bundle
is the given line bundle, through the native full formal comparison. -/
def algebraizedLineBundleReductionIso (n : ℕ) :
    (pullback (idealThickeningι f (I ^ (n + 1)))).obj S.algebraizedLineBundle.val ≅
      (S.bundle n).val := by
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  exact S.geometricReductionIso S.algebraizedModule S.algebraizedCompletionIso n

end AlgebraicGeometry.Scheme.Modules.Invertible.CompatibleLineBundleSystem
