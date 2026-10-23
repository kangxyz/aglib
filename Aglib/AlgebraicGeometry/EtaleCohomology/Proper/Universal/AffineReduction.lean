/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Universal.ModelTransport

/-! # Original proper exchange from universal projective-line exchange

The geometric criterion and its universal bounded-exchange property now apply
directly to the original higher maps and derived singles in independently
supplied derived-category models. Universal projective-line exchange remains
an explicit input; this file does not assert the general proper-base-change
theorem.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper

universe u dX dS dX' dS'

attribute [local instance] hasSheafifyLarge

variable {X S X' S' : Scheme.{u}}
  [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{dX'} (AbelianSheaf.{u, u + 1} X')]
  [HasDerivedCategory.{dS'} (AbelianSheaf.{u, u + 1} S')]
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : IsPullback g' f' f g) (n : ℕ)

/-- The universal bounded-exchange property supplies the actual higher map
on every bounded-torsion coefficient in independently supplied models. -/
theorem higherBaseChangeMap_isIso_of_universallyBoundedBaseChange
    (hf : universallyBoundedBaseChange n f)
    (F : AbelianSheaf.{u, u + 1} X) (hF : n • 𝟙 F = 0) (q : ℕ) :
    IsIso ((higherBaseChangeMap f f' g g' h.w.symm q).app F) :=
  higherBaseChangeMap_isIso_of_boundedExchange f f' g g' h.w.symm n
    (((boundedBaseChange n).universally_le f hf) f' g g' h) F hF q

/-- The same property supplies the original derived exchange on the literal
source single, with no relation required between the four model universes. -/
theorem derivedBaseChangeMap_single_isIso_of_universallyBoundedBaseChange
    (hf : universallyBoundedBaseChange n f)
    (F : AbelianSheaf.{u, u + 1} X) (hF : n • 𝟙 F = 0) :
    IsIso ((derivedBaseChangeMap f f' g g' h.w.symm).app
      ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F)) :=
  (Reduction.derivedBaseChangeMap_single_isIso_iff_higher f f' g g' h.w.symm F).mpr
    (higherBaseChangeMap_isIso_of_universallyBoundedBaseChange f f' g g' h n hf F hF)

section Affine

variable (R : Type u) [CommRing R]
  [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} (Spec (.of R)))]
  (p : X ⟶ Spec (.of R)) [IsProper p]
  (p' : X' ⟶ S') (b : S' ⟶ Spec (.of R)) (b' : X' ⟶ X)
  (hp : IsPullback b' p' p b)

/-- Universal projective-line exchange over the same arbitrary ring implies
the original higher exchange for every proper morphism over its spectrum. -/
theorem properHigherBaseChange_isIso_of_projectiveLine
    (hline : universallyBoundedBaseChange n (ProjectiveLine.structureMap R))
    (F : AbelianSheaf.{u, u + 1} X) (hF : n • 𝟙 F = 0) (q : ℕ) :
    IsIso ((higherBaseChangeMap p p' b b' hp.w.symm q).app F) :=
  higherBaseChangeMap_isIso_of_universallyBoundedBaseChange p p' b b' hp n
    (universallyBoundedBaseChange_proper_affine_of_projectiveLine n R hline p) F hF q

/-- The corresponding original derived-single exchange follows through its
native all-degree homology criterion. The projective-line input is unchanged. -/
theorem properDerivedBaseChange_single_isIso_of_projectiveLine
    (hline : universallyBoundedBaseChange n (ProjectiveLine.structureMap R))
    (F : AbelianSheaf.{u, u + 1} X) (hF : n • 𝟙 F = 0) :
    IsIso ((derivedBaseChangeMap p p' b b' hp.w.symm).app
      ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F)) :=
  derivedBaseChangeMap_single_isIso_of_universallyBoundedBaseChange p p' b b' hp n
    (universallyBoundedBaseChange_proper_affine_of_projectiveLine n R hline p) F hF

end Affine

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper
