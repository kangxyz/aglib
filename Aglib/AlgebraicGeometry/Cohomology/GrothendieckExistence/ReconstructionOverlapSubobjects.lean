/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.ReconstructionOverlapAmbient

/-! # Whole comparisons of original subobjects in overlap coordinates -/

@[expose] public noncomputable section
open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u
variable {X U V : Scheme.{u}}
  (p : U ⟶ X) (q : V ⟶ X) [IsOpenImmersion p] [IsOpenImmersion q]
  {G₁ : U.Modules} {G₂ : V.Modules} {M : X.Modules}
  (s₁ : G₁ ⟶ (pullback p).obj M) (s₂ : G₂ ⟶ (pullback q).obj M)

/-- The original pulled ambient inclusion is preserved. -/
def ReconstructionOverlapAmbientComparison :=
  {e : (pullback (Limits.pullback.fst p q)).obj G₁ ≅
    (pullback (Limits.pullback.snd p q)).obj G₂ //
    (pullback (Limits.pullback.fst p q)).map s₁ ≫
      (reconstructionOverlapPullbackIso p q).hom.app M =
    e.hom ≫ (pullback (Limits.pullback.snd p q)).map s₂}

/-- The same original inclusion in the native gluer's restriction coordinates. -/
def ReconstructionOverlapRestrictionComparison :=
  {e : G₁.restrict (Limits.pullback.fst p q) ≅ G₂.restrict (Limits.pullback.snd p q) //
    (restrictFunctor (Limits.pullback.fst p q)).map
      (s₁ ≫ (restrictFunctorIsoPullback p).inv.app M) ≫
        (overlapRestrictIso p q).hom.app M =
    e.hom ≫ (restrictFunctor (Limits.pullback.snd p q)).map
      (s₂ ≫ (restrictFunctorIsoPullback q).inv.app M)}

/-- Convert the whole original ambient comparison before specializing its source. -/
def reconstructionOverlapRestrictionComparison
    (d : ReconstructionOverlapAmbientComparison p q s₁ s₂) :
    ReconstructionOverlapRestrictionComparison p q s₁ s₂ :=
  ⟨(restrictFunctorIsoPullback (Limits.pullback.fst p q)).app G₁ ≪≫ d.val ≪≫
    ((restrictFunctorIsoPullback (Limits.pullback.snd p q)).app G₂).symm,
    reconstructionOverlap_restrict_compatible p q s₁ s₂ d.val d.property⟩

end AlgebraicGeometry.Scheme.Modules.Coherent
