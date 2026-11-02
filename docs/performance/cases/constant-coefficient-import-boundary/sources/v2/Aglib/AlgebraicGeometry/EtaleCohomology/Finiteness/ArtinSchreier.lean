/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.CharacteristicPrimaryGeometry
public import Aglib.CategoryTheory.Sites.SheafCohomology.ConstantCyclic
public import Aglib.LinearAlgebra.FrobeniusFixed

/-!
# Proper Artin--Schreier cohomology is finite

For every proper scheme over a separably closed characteristic-`p` field, the
original prime-field cohomology is finite in every degree. The original
prime-field inclusion identifies it with the fixed vectors of the original
Frobenius on structure cohomology. The structural field action and the
independent Ext universe are retained. There is no dimension, smoothness,
reducedness, connectedness, perfectness or Frobenius-invertibility hypothesis.
-/

@[expose] public noncomputable section

universe u w

open CategoryTheory CategoryTheory.Abelian
open AlgebraicGeometry.Scheme.OverField

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Curves

attribute [local instance] hasSheafifyLarge Curves.structureCohomologyModule

variable {k : Type u} [Field k] [IsSepClosed k] (Y : FScheme k) [IsProper Y.hom]
  [HasExt.{w} (AbelianSheaf.{u, u + 1} Y.left)]
  (p : ℕ) [Fact p.Prime] [CharP k p]

/-- The original prime-field inclusion is injective on every cohomology group of a proper scheme. -/
theorem primeFieldToStructure_cohomology_injective (q : ℕ) :
    Function.Injective (Sheaf.H.map
      (primeFieldToStructure Y.left p (primeCast_global_eq_zero Y p)) q) := by
  have hS := artinSchreierComplex_shortExact Y.left p (Fact.out)
    (primeCast_global_eq_zero Y p)
  cases q with
  | zero =>
      let := primeFieldToStructure_mono Y.left p (Fact.out) (primeCast_global_eq_zero Y p)
      exact Ext.postcomp_mk₀_injective_of_mono _ _
  | succ q =>
      let : Module k (Sheaf.H.{w} (additiveStructureSheaf Y.left) q) :=
        Curves.structureCohomologyModule Y q
      let : FiniteDimensional k (Sheaf.H.{w} (additiveStructureSheaf Y.left) q) :=
        etaleStructureCohomology_finite Y q
      have hsurj := artinSchreier_cohomology_surjective Y p q
      apply (injective_iff_map_eq_zero _).mpr
      intro x hx
      obtain ⟨z, hz⟩ := Sheaf.H.longSequence_exact₁ hS x hx rfl
      have he := (ShortComplex.ab_exact_iff_function_exact _).mp
        (Sheaf.H.longSequence_exact₃' hS q (q + 1) rfl)
      exact hz.symm.trans ((he z).mpr (hsurj z))

/-- The original cohomological inclusion takes values in the literal Frobenius-fixed set. -/
def primeFieldCohomologyToFrobeniusFixed (q : ℕ) :
    Sheaf.H.{w} (primeFieldSheaf Y.left p) q →
      {x : Sheaf.H.{w} (additiveStructureSheaf Y.left) q //
        structureCohomologyFrobenius Y p q x = x} := fun x => by
  let y := Sheaf.H.map (primeFieldToStructure Y.left p (primeCast_global_eq_zero Y p)) q x
  refine ⟨y, sub_eq_zero.mp ?_⟩
  rw [← artinSchreier_cohomology_apply]
  have he := (ShortComplex.ab_exact_iff_function_exact _).mp
    (Sheaf.H.longSequence_exact₂'
      (artinSchreierComplex_shortExact Y.left p (Fact.out) (primeCast_global_eq_zero Y p)) q)
  exact (he y).mpr ⟨x, rfl⟩

/-- Exactness and actual Frobenius-difference surjectivity identify the original
inclusion's range. -/
theorem primeFieldCohomologyToFrobeniusFixed_bijective (q : ℕ) :
    Function.Bijective (primeFieldCohomologyToFrobeniusFixed Y p q) := by
  constructor
  · intro x y h
    exact primeFieldToStructure_cohomology_injective Y p q (congrArg Subtype.val h)
  · intro y
    have hy : Sheaf.H.map
        (artinSchreierMap Y.left p (Fact.out) (primeCast_global_eq_zero Y p)) q y.val = 0 := by
      rw [artinSchreier_cohomology_apply, y.property, sub_self]
    obtain ⟨x, hx⟩ := Sheaf.H.longSequence_exact₂
      (artinSchreierComplex_shortExact Y.left p (Fact.out) (primeCast_global_eq_zero Y p))
      y.val hy
    exact ⟨x, Subtype.ext hx⟩

/-- The original prime-field cohomology is the actual finite-dimensional Frobenius-fixed kernel. -/
def primeFieldCohomologyFrobeniusFixedEquiv (q : ℕ) :
    Sheaf.H.{w} (primeFieldSheaf Y.left p) q ≃
      {x : Sheaf.H.{w} (additiveStructureSheaf Y.left) q //
        structureCohomologyFrobenius Y p q x = x} :=
  Equiv.ofBijective (primeFieldCohomologyToFrobeniusFixed Y p q)
    (primeFieldCohomologyToFrobeniusFixed_bijective Y p q)

/-- The fixed-kernel equivalence has the literal original prime-field inclusion
as its forward map. -/
@[simp]
theorem primeFieldCohomologyFrobeniusFixedEquiv_val (q : ℕ)
    (x : Sheaf.H.{w} (primeFieldSheaf Y.left p) q) :
    (primeFieldCohomologyFrobeniusFixedEquiv Y p q x).val =
      Sheaf.H.map (primeFieldToStructure Y.left p (primeCast_global_eq_zero Y p)) q x := rfl

/-- Every original prime-field cohomology group of a proper scheme over a separably closed
field of characteristic `p` is finite. -/
theorem primeField_cohomology_finite_of_proper (q : ℕ) :
    Finite (Sheaf.H.{w} (primeFieldSheaf Y.left p) q) := by
  let : Module k (Sheaf.H.{w} (additiveStructureSheaf Y.left) q) :=
    Curves.structureCohomologyModule Y q
  let : FiniteDimensional k (Sheaf.H.{w} (additiveStructureSheaf Y.left) q) :=
    etaleStructureCohomology_finite Y q
  let : Finite {x : Sheaf.H.{w} (additiveStructureSheaf Y.left) q //
      structureCohomologyFrobenius Y p q x = x} :=
    LinearMap.finite_fixedPoints_of_frobenius (k := k) p (structureCohomologyFrobenius Y p q)
  exact Finite.of_injective (primeFieldCohomologyFrobeniusFixedEquiv Y p q)
    (primeFieldCohomologyFrobeniusFixedEquiv Y p q).injective

/-- The actual cyclic prime-power coefficients have finite cohomology in every degree on a
proper scheme over a separably closed characteristic-`p` field. -/
theorem cyclicPrimePower_cohomology_finite_of_proper (q r : ℕ) :
    Finite (Sheaf.H.{w}
      (ConstantFinite.coefficient (ULift.{u} (ZMod (p ^ r))) Y.left) q) := by
  let : Finite (Sheaf.H.{w} (primeFieldSheaf Y.left p) q) :=
    primeField_cohomology_finite_of_proper Y p q
  let e : Sheaf.H.{w} (ConstantFinite.coefficient (ULift.{u} (ZMod p)) Y.left) q ≃+
      Sheaf.H.{w} (primeFieldSheaf Y.left p) q :=
    ((Sheaf.functorH (Scheme.smallEtaleTopology Y.left) q).mapIso
      (cyclicPrimeFieldIso Y.left p)).addCommGroupIsoToAddEquiv
  have hp : Finite (Sheaf.H.{w}
      (ConstantFinite.coefficient (ULift.{u} (ZMod p)) Y.left) q) :=
    Finite.of_injective e e.injective
  let : Finite (Sheaf.H.{w}
      (ConstantFinite.coefficient (ULift.{u} (ZMod p)) Y.left) q) := hp
  exact Sheaf.cyclicPrimePower_cohomology_finite (cyclicCoefficientFunctor Y.left)
    p (Fact.out : p.Prime).pos q r

end AlgebraicGeometry.Scheme.EtaleCohomology
