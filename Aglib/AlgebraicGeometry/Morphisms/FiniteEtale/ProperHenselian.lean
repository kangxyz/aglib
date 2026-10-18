/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange
public import Mathlib.RingTheory.Henselian

/-!
# FiniteEtale / ProperHenselian

Object-based extraction of the Wangcai checkpoint-27 construction.
Existing qualified declarations and their explicit mathematical premises are retained.
-/

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (baseChange)
universe u

namespace AlgebraicGeometry.Scheme.FiniteEtale

/-- Exact universal independent proper-henselian comparison premise. Its ring
is actually henselian and local; it concerns all proper schemes and their
actual residue-field pullbacks, independently of any elliptic curve or isogeny. -/
def ProperHenselianComparison (R : Type u) [CommRing R] [HenselianLocalRing R] : Prop :=
  ∀ (Y : Scheme.{u}) (π : Y ⟶ Spec (.of R)), IsProper π →
    (baseChange (pullback.fst π
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))).IsEquivalence

end AlgebraicGeometry.Scheme.FiniteEtale

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 726bc9a6fbdccd40d47bf22c275089a137482a154436ed19e61e5d2043257c80.
Definitions, hypotheses and universes are retained modulo native names. -/
