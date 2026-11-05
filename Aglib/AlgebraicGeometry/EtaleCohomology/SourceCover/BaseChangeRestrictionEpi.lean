/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.SourceCover.OrdinaryFaceComponent
public import Aglib.AlgebraicGeometry.EtaleCohomology.SourceCover.OrdinaryActualEpimorphism
public import Aglib.CategoryTheory.Adjunction.Mates.FaceEpimorphism
public import Aglib.AlgebraicGeometry.EtaleCohomology.PullbackEpimorphism

/-! # Original restriction epimorphism after smooth base change

The actual face equation transports an original restriction epi using only
ordinary smooth exchange. No derived open-image acyclicity or compatibility
of biproduct comparison models is assumed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X S X' S' : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (H : IsPullback g' f' f g) [Smooth g]

include H

/-- Ordinary smooth face naturality transports the literal restriction epi. -/
theorem sourceEtaleImageMap_baseChange_epi {U V : X.Etale} (a : U ⟶ V)
    (F : AbelianSheaf.{u, u + 1} X) (n : ℕ) (hn : 0 < n) (hF : n • 𝟙 F = 0)
    [Epi ((sourceEtaleImageMap f a).app F)] : type_of% (
  epi_of_commuting_face
    (sourceEtaleOrdinaryComparison_face_app f f' g g' H a F)
    (inverseImage_map_epi g ((sourceEtaleImageMap f a).app F))
    (sourceEtaleOrdinaryComparison_actual_epi f f' g g' H U n hn F hF)
    ) :=
  epi_of_commuting_face
    (sourceEtaleOrdinaryComparison_face_app f f' g g' H a F)
    (inverseImage_map_epi g ((sourceEtaleImageMap f a).app F))
    (sourceEtaleOrdinaryComparison_actual_epi f f' g g' H U n hn F hF)

end AlgebraicGeometry.Scheme.EtaleCohomology
