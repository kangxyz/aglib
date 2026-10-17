/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Line bundles on local schemes

If a scheme `X` has a point `x` whose only open neighbourhood is `X` itself, every
line bundle on `X` is trivial: a trivializing open around `x` is all of `X`
(`nonempty_iso_unit_of_forall_mem_open`). The spectrum of a local ring has this
property at its closed point, so every line bundle on `Spec R` is trivial and
`PicardGroup (Spec R)` is a subsingleton for every commutative local ring `R`.
No Noetherian, integrality, reducedness or dimension hypothesis is used.

Extraction source: `R5Lab.AlgebraicGeometry.Curves.Picard.localLineBundle_trivial`;
source names are provenance.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules.Invertible

universe u

/-- A line bundle on a scheme with a point whose only open neighbourhood is the whole
scheme is isomorphic to the structure sheaf. -/
theorem nonempty_iso_unit_of_forall_mem_open {X : Scheme.{u}} (x : X)
    (hx : ∀ U : X.Opens, x ∈ U → U = ⊤) (L : LineBundle X) :
    Nonempty (L.val ≅ SheafOfModules.unit X.ringCatSheaf) := by
  obtain ⟨U, hxU, ⟨e⟩⟩ := (isLocallyRankOne_iff_restrict_unit L.val).mp L.property x
  have : IsIso U.ι := isIso_of_isOpenImmersion_of_opensRange_eq_top U.ι
    (by simpa using hx U hxU)
  let j := inv U.ι
  let e' := ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app L.val).symm ≪≫ e
  exact ⟨((Scheme.Modules.pullbackId _).app L.val).symm ≪≫
    ((Scheme.Modules.pullbackCongr (IsIso.inv_hom_id U.ι)).app L.val).symm ≪≫
    ((Scheme.Modules.pullbackComp j U.ι).app L.val).symm ≪≫
    (Scheme.Modules.pullback j).mapIso e' ≪≫ Scheme.Modules.pullbackUnitIso j⟩

/-- Under the same hypothesis, every line-bundle class is zero. -/
theorem classOf_eq_zero_of_forall_mem_open {X : Scheme.{u}} (x : X)
    (hx : ∀ U : X.Opens, x ∈ U → U = ⊤) (L : LineBundle X) : classOf X L = 0 := by
  obtain ⟨e⟩ := nonempty_iso_unit_of_forall_mem_open x hx L
  exact Quotient.sound ⟨e ≪≫ (CategoryTheory.Limits.coproductUniqueIso
    (fun _ : PUnit.{u + 1} => SheafOfModules.unit X.ringCatSheaf)).symm⟩

theorem subsingleton_picardGroup_of_forall_mem_open {X : Scheme.{u}} (x : X)
    (hx : ∀ U : X.Opens, x ∈ U → U = ⊤) : Subsingleton (PicardGroup X) := by
  refine ⟨fun a b => ?_⟩
  induction a using Quotient.inductionOn with | h L =>
  induction b using Quotient.inductionOn with | h M =>
  exact (classOf_eq_zero_of_forall_mem_open x hx L).trans
    (classOf_eq_zero_of_forall_mem_open x hx M).symm

/-- Every line bundle on the spectrum of a commutative local ring is trivial. -/
theorem nonempty_iso_unit_of_isLocalRing (R : CommRingCat.{u}) [IsLocalRing R]
    (L : LineBundle (Spec R)) :
    Nonempty (L.val ≅ SheafOfModules.unit (Spec R).ringCatSheaf) :=
  nonempty_iso_unit_of_forall_mem_open (IsLocalRing.closedPoint R)
    (fun U hU => (IsLocalRing.closedPoint_mem_iff U).mp hU) L

/-- The Picard group of the spectrum of a commutative local ring is trivial. -/
instance subsingleton_picardGroup_of_isLocalRing (R : CommRingCat.{u}) [IsLocalRing R] :
    Subsingleton (PicardGroup (Spec R)) :=
  subsingleton_picardGroup_of_forall_mem_open (IsLocalRing.closedPoint R)
    (fun U hU => (IsLocalRing.closedPoint_mem_iff U).mp hU)

end AlgebraicGeometry.Scheme.Modules.Invertible
