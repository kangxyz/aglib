/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.HenselianResidue
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-! # A section of the original nonempty finite-etale cover

Over a Henselian local ring with separably closed residue, one actual residue
point lifts to a section. The proof selects no product decomposition and
requires no Noetherian, domain, or normality assumption.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.FiniteEtale

universe u

variable (R : Type u) [CommRing R] [HenselianLocalRing R]
  [IsSepClosed (IsLocalRing.ResidueField R)]

/-- Lift a section through the specified point of the original closed fibre.
Etaleness supplies the residue-field separability used for the residue point;
Henselian lifting retains that point exactly. -/
theorem exists_section_through_closedPoint
    {E : Scheme.{u}} (p : E ⟶ Spec (.of R)) [IsFinite p] [Etale p]
    (y : E) (hy : p y = IsLocalRing.closedPoint R) :
    ∃ s : Spec (.of R) ⟶ E,
      s ≫ p = 𝟙 _ ∧ s (IsLocalRing.closedPoint R) = y := by
  let t₀ := Scheme.LocalRing.residueSpecMap R
  have ht₀ : t₀ (default : Spec (.of (IsLocalRing.ResidueField R))) =
      IsLocalRing.closedPoint R := IsLocalRing.PrimeSpectrum.comap_residue R _
  obtain ⟨t, ht, hty⟩ := Scheme.exists_fac_of_etale_of_isSepClosed p t₀ y
    (hy.trans ht₀.symm)
  obtain ⟨s, hs, _⟩ := HenselianResidue.existsUnique_section_lift R p t ht
  refine ⟨s, hs.1, ?_⟩
  calc
    s (IsLocalRing.closedPoint R) = s (t₀ default) := congrArg s ht₀.symm
    _ = t default := congrArg (fun h : Spec (.of (IsLocalRing.ResidueField R)) ⟶ E =>
      h default) hs.2
    _ = y := hty

/-- Every nonempty finite-etale cover of a strictly Henselian local spectrum
has an actual section with its unchanged structural triangle. -/
theorem exists_section_of_isSepClosed_residue
    {E : Scheme.{u}} (p : E ⟶ Spec (.of R)) [IsFinite p] [Etale p] [Nonempty E] :
    ∃ s : Spec (.of R) ⟶ E, s ≫ p = 𝟙 _ := by
  let y₀ : E := Classical.choice inferInstance
  have hclosed : IsClosed (Set.range p) := p.isClosedMap.isClosed_range
  have hmem : IsLocalRing.closedPoint R ∈ Set.range p :=
    (IsLocalRing.specializes_closedPoint (p y₀)).mem_closed hclosed ⟨y₀, rfl⟩
  obtain ⟨y, hy⟩ := hmem
  obtain ⟨s, hs, _⟩ := exists_section_through_closedPoint R p y hy
  exact ⟨s, hs⟩

end AlgebraicGeometry.Scheme.FiniteEtale
