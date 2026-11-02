/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.BaseChangeIdentity
public import Aglib.AlgebraicGeometry.Compactification.Refinements.SourceIsoCoherence

/-! # Actual source isomorphism over an identity base -/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Hom.DenseCompactification

universe u
variable {X X' S : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S)
  (a : X' ⟶ X) (sq : IsPullback a f' f (𝟙 S))

/-- The actual source isomorphism of a Cartesian presentation over the identity base. -/
def cartesianIdentitySourceIso : X' ≅ X := sq.flip.isoPullback ≪≫ identitySourceIso f

/-- Its original underlying map is the source arrow of the given square. -/
theorem cartesianIdentitySourceIso_hom : (cartesianIdentitySourceIso f f' a sq).hom = a :=
  sq.flip.isoPullback_hom_snd

/-- The source isomorphism lies over the actual structure maps. -/
theorem cartesianIdentitySourceIso_fac :
    (cartesianIdentitySourceIso f f' a sq).hom ≫ f = f' :=
  sourceIso_comp_fac f (pullback.fst (𝟙 S) f) f'
    (identitySourceIso f) sq.flip.isoPullback
    (identitySourceIso_hom_f f) sq.flip.isoPullback_hom_fst


end AlgebraicGeometry.Scheme.EtaleCohomology
