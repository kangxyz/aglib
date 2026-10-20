/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorAssociator
public import Aglib.AlgebraicGeometry.Modules.InternalHom
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Picard.LocalRing` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`bda11ea713da57688521022525841aaf204de11f9cd9b6d4c2d2c754d80ed5ca`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.Modules.Invertible
  (LineBundle isLocallyRankOne_iff_restrict_unit)
open _root_.AlgebraicGeometry.Scheme.Modules (pullbackUnitIso)

/-!
# Actual line bundles on the spectrum of a local ring

Private investigation for `K2-018#prop:k2018-arithmetic-characters`,
mathematical source revision `e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Engineering basis: `7dcde130d429905e2624079dd7a0d18e3ebc94e2`.
The encoded subset is triviality of each actual locally rank-one module sheaf
on the spectrum of an arbitrary commutative local ring. No integral,
noetherian, dimension, or discrete-valuation hypothesis is used.
-/

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible
namespace AlgebraicGeometry.Scheme.Modules.Invertible
universe u

/-- Every actual line bundle over an arbitrary local ring spectrum is trivial.
Source subset: `K2-018#prop:k2018-arithmetic-characters`, mathematical revision
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`; local Kummer prerequisite.
The proof uses a chart at the closed point and its specialization topology. -/
theorem localLineBundle_trivial (R : CommRingCat.{u}) [IsLocalRing R]
    (L : LineBundle (Spec R)) :
    Nonempty (L.val ≅ SheafOfModules.unit (Spec R).ringCatSheaf) := by
  let x : Spec R := IsLocalRing.closedPoint R
  obtain ⟨U, hx, ⟨e⟩⟩ := (isLocallyRankOne_iff_restrict_unit L.val).mp L.property x
  have hU : U = ⊤ := (IsLocalRing.closedPoint_mem_iff U).mp hx
  have : IsIso U.ι := isIso_of_isOpenImmersion_of_opensRange_eq_top U.ι
    (by simpa using hU)
  let j := inv U.ι
  let e' := ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app L.val).symm ≪≫ e
  exact ⟨((Scheme.Modules.pullbackId _).app L.val).symm ≪≫
    ((Scheme.Modules.pullbackCongr (IsIso.inv_hom_id U.ι)).app L.val).symm ≪≫
    ((Scheme.Modules.pullbackComp j U.ι).app L.val).symm ≪≫
    (Scheme.Modules.pullback j).mapIso e' ≪≫ pullbackUnitIso j⟩

end AlgebraicGeometry.Scheme.Modules.Invertible
