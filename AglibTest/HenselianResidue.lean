/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.HenselianResidue
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Henselian residue-section consumers

The general producer is checked on its actual residue map, including the
original Noetherian DVR specialization. No proper-comparison witness is supplied.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.FiniteEtale.HenselianResidue
universe u

example (R : Type u) [CommRing R] [HenselianLocalRing R] [IsDomain R]
    [IsNoetherianRing R] [IsDiscreteValuationRing R]
    (C : Scheme.FiniteEtale (Spec (.of R)))
    (t : Spec (.of (IsLocalRing.ResidueField R)) ⟶ C.obj.left)
    (ht : t ≫ C.obj.hom = Scheme.LocalRing.residueSpecMap R) :
    ∃! s : Spec (.of R) ⟶ C.obj.left,
      s ≫ C.obj.hom = 𝟙 _ ∧ Scheme.LocalRing.residueSpecMap R ≫ s = t :=
  existsUnique_section_lift R C.obj.hom t ht

example (R : Type u) [CommRing R] [HenselianLocalRing R] :
    liftResiduePoint R (𝟙 (Spec (.of R))) (Scheme.LocalRing.residueSpecMap R)
      (by simp) = 𝟙 _ := by
  symm
  exact liftResiduePoint_unique R (𝟙 _) (Scheme.LocalRing.residueSpecMap R)
    (by simp) (𝟙 _) (by simp) (by simp)

example (R : Type u) [CommRing R] [HenselianLocalRing R]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) [IsFinite p] [Etale p]
    (t : Spec (.of (IsLocalRing.ResidueField R)) ⟶ X)
    (ht : t ≫ p = Scheme.LocalRing.residueSpecMap R) :
    Scheme.LocalRing.residueSpecMap R ≫ liftResiduePoint R p t ht = t :=
  liftResiduePoint_restrict R p t ht
