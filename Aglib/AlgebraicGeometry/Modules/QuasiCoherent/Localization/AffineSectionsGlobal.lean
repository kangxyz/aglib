/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Localization.AffineSectionsQuasicoherent
public import Aglib.AlgebraicGeometry.Modules.BaseChange.OpenImmersion
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Noetherian
/-!
# Quasicoherent direct image along quasi-compact open immersions

Actual open base change reduces to an affine target. Compactness of the
base-changed open immersion then permits the proved finite-principal-cover
localization argument. No coherent extension or quotient equivalence is
used in this theorem.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

namespace AlgebraicGeometry.Scheme.Modules.QuasiCoherent

/-- The actual direct image of a quasicoherent module along a quasi-compact
open immersion is quasicoherent. -/
theorem quasicoherent_pushforward_open
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (M : U.Modules) [M.IsQuasicoherent] :
    ((Scheme.Modules.pushforward j).obj M).IsQuasicoherent := by
  apply quasicoherent_of_affineCharts
  intro R a _
  let p := pullback.fst j a
  let q := pullback.snd j a
  have : CompactSpace (Limits.pullback j a : Scheme) :=
    QuasiCompact.compactSpace_of_compactSpace q
  have hcompact : IsCompact (q.opensRange : Set (Spec R)) :=
    isCompact_range q.continuous
  have h : ((Scheme.Modules.pushforward q).obj (M.restrict p)).IsQuasicoherent :=
    AffineSections.isQuasicoherent_pushforward_of_isCompact q hcompact (M.restrict p)
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    ((openBaseChange j a).app M).symm h

/-- Every open immersion into a locally noetherian scheme preserves
quasicoherence under actual direct image. The quasi-compactness needed in
the proof follows from local noetherianity of the target. -/
theorem quasicoherent_pushforward_open_of_locallyNoetherian
    {U X : Scheme.{u}} [IsLocallyNoetherian X] (j : U ⟶ X) [IsOpenImmersion j]
    (M : U.Modules) [M.IsQuasicoherent] :
    ((Scheme.Modules.pushforward j).obj M).IsQuasicoherent :=
  quasicoherent_pushforward_open j M

end AlgebraicGeometry.Scheme.Modules.QuasiCoherent
