/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Map.Spec
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber

/-!
# Dimensions of original module cohomology on residue-field fibres

The fibre is the actual pullback along `Spec κ(p) → Spec R`, and its
coefficient is the ordinary geometric pullback of the original module
sheaf. The dimension uses the original additive `Sheaf.H` with the
literal structural residue-field action. This numerical definition
does not introduce a new fibre or cohomology object. Geometric finiteness
is supplied by the projective/proper theorems that consume it.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Module

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

/-- The dimension of the original cohomology of the ordinary pulled coefficient on the
actual residue-field fibre, with its structural residue-field module action. -/
def moduleFiberCohomologyDimension (f : X ⟶ Spec (CommRingCat.of R))
    (M : X.Modules) (q : ℕ) (p : PrimeSpectrum R) : ℕ :=
  let k := p.asIdeal.ResidueField
  let σ := Spec.map (CommRingCat.ofHom (algebraMap R k))
  let Y := pullback f σ
  let a := pullback.fst f σ
  let b := pullback.snd f σ
  let N := (Scheme.Modules.pullback a).obj M
  let β := b.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  letI := moduleCohomologyModuleOfHom Y β N q
  finrank k (Sheaf.H.{u + 1} (moduleAddSheaf Y N) q)

end AlgebraicGeometry.Scheme.Cohomology
