/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.FiniteComponentPointEquiv
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.FiniteComponentPointScheme

/-! # Actual geometric morphism indices for finite components -/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

/-- The native spectrum functor identifies actual ring points over a fixed base
map with actual scheme morphisms satisfying the same base triangle. -/
def specPointOverEquiv (R A K : Type u) [CommRing R] [CommRing A] [CommRing K]
    [Algebra R A] (r : R →+* K) :
    {a : A →+* K // a.comp (algebraMap R A) = r} ≃
      {q : Spec (.of K) ⟶ Spec (.of A) //
        q ≫ Spec.algebraMap R A = Spec.map (CommRingCat.ofHom r)} := by
  let φ : {a : A →+* K // a.comp (algebraMap R A) = r} →
      {q : Spec (.of K) ⟶ Spec (.of A) //
        q ≫ Spec.algebraMap R A = Spec.map (CommRingCat.ofHom r)} := fun a =>
    ⟨Spec.map (CommRingCat.ofHom a.val), by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      exact congrArg (fun t => Spec.map (CommRingCat.ofHom t)) a.property⟩
  apply Equiv.ofBijective φ
  constructor
  · intro a b h
    apply Subtype.ext
    have hh : CommRingCat.ofHom a.val = CommRingCat.ofHom b.val :=
      Spec.map_injective (congrArg Subtype.val h)
    exact congrArg (fun t => t.hom) hh
  · intro q
    obtain ⟨a, ha⟩ := Spec.map_surjective q.val
    have hb : CommRingCat.ofHom (algebraMap R A) ≫ a = CommRingCat.ofHom r := by
      apply Spec.map_injective
      rw [Spec.map_comp, ha]
      exact q.property
    refine ⟨⟨a.hom, congrArg (fun t => t.hom) hb⟩, ?_⟩
    exact Subtype.ext ha

/-- The actual maximal components are indexed by scheme points over the one
chosen common geometric field, retaining the original structural morphism. -/
def finiteComponentGeometricIndex (R A Ω : Type u) [CommRing R] [HenselianLocalRing R]
    [IsSepClosed (ResidueField R)] [CommRing A] [Algebra R A] [Module.Finite R A]
    [Field Ω] [IsAlgClosed Ω] [Algebra (ResidueField R) Ω] :
    MaximalSpectrum A ≃
      {q : Spec (.of Ω) ⟶ Spec (.of A) //
        q ≫ Spec.algebraMap R A = Spec.map (CommRingCat.ofHom
          ((algebraMap (ResidueField R) Ω).comp (IsLocalRing.residue R)))} :=
  (finiteComponentPointEquiv R A Ω).trans
    (specPointOverEquiv R A Ω ((algebraMap (ResidueField R) Ω).comp (IsLocalRing.residue R)))

end AlgebraicGeometry.Scheme.EtaleCohomology
