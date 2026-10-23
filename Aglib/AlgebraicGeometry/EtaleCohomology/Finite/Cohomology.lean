/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.HigherVanishing
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.CohomologyBaseChange

/-! # Original cohomology and its canonical square for finite direct image

The comparison uses the original `Sheaf.H`, pullback, counit, and ordinary
exchange. It does not assert that arbitrary global-cohomology pullback is an
isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite

universe u wX wS wX' wS'

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}}
  [HasExt.{wX} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{wS} (AbelianSheaf.{u, u + 1} S)]
  (f : X ⟶ S) [IsFinite f]

/-- Original cohomology of a finite direct image is original cohomology of its
source, with independently sized Ext groups. -/
def finiteCohomologyDirectImageAddEquiv (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) :
    Sheaf.H.{wS} ((directImage f).obj F) q ≃+ Sheaf.H.{wX} F q :=
  cohomologyDirectImageAddEquiv f F q

/-- The finite comparison is exactly original pullback followed by the original
adjunction counit on cohomology. -/
theorem finiteCohomologyDirectImageAddEquiv_apply
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)
    (a : Sheaf.H.{wS} ((directImage f).obj F) q) :
    finiteCohomologyDirectImageAddEquiv f F q a =
      Sheaf.H.map ((inverseImageAdjunction f).counit.app F) q
        (cohomologyPullback f ((directImage f).obj F) q a) :=
  cohomologyDirectImageAddEquiv_apply f F q a

/-- Coefficient naturality uses the original cohomology maps. -/
theorem finiteCohomologyDirectImageAddEquiv_naturality
    {F G : AbelianSheaf.{u, u + 1} X} (a : F ⟶ G) (q : ℕ)
    (x : Sheaf.H.{wS} ((directImage f).obj F) q) :
    finiteCohomologyDirectImageAddEquiv f G q (Sheaf.H.map ((directImage f).map a) q x) =
      Sheaf.H.map a q (finiteCohomologyDirectImageAddEquiv f F q x) :=
  cohomologyDirectImageAddEquiv_naturality f a q x

variable {X' S' : Scheme.{u}}
  [HasExt.{wX'} (AbelianSheaf.{u, u + 1} X')]
  [HasExt.{wS'} (AbelianSheaf.{u, u + 1} S')]
  (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X) (h : IsPullback g' f' f g)

/-- The actual finite cohomology equivalences commute with the original exchange
and pullback maps. No global-cohomology pullback is claimed to be invertible. -/
theorem finiteCohomologyDirectImageAddEquiv_baseChange
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)
    (a : Sheaf.H.{wS} ((directImage f).obj F) q) :
    let : IsFinite f' := MorphismProperty.of_isPullback h (inferInstance : IsFinite f)
    finiteCohomologyDirectImageAddEquiv f' ((inverseImage g').obj F) q
        (Sheaf.H.map ((baseChangeMap f f' g g' h.w.symm).app F) q
          (cohomologyPullback g ((directImage f).obj F) q a)) =
      cohomologyPullback g' F q (finiteCohomologyDirectImageAddEquiv f F q a) := by
  dsimp only
  let : IsFinite f' := MorphismProperty.of_isPullback h (inferInstance : IsFinite f)
  exact cohomologyDirectImageAddEquiv_baseChange f f' g g' h.w.symm F q a

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
