/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.StructureScalars
public import Aglib.LinearAlgebra.FrobeniusDifference

/-!
# Frobenius semilinearity on original étale structure cohomology

The semilinear operator is the induced map of the principal's actual Frobenius.
The base field may be imperfect and the operator need not be invertible.
Finite dimensionality is the remaining geometric input to the difference theorem.
-/

@[expose] public noncomputable section

universe u w

open CategoryTheory
open AlgebraicGeometry.Scheme.OverField

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

variable {k : Type u} [Field k] (Y : FScheme k)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} Y.left)]

attribute [local instance] structureCohomologyModule

omit [HasExt.{w} (AbelianSheaf.{u, u + 1} Y.left)] in
/-- Characteristic of the actual field scheme's global sections, including the empty scheme. -/
theorem primeCast_global_eq_zero (p : ℕ) [CharP k p] :
    (p : Γ(Y.left, ⊤)) = 0 := by
  have h := congrArg (Scheme.constants Y) (CharP.cast_eq_zero k p)
  simpa only [map_natCast, map_zero] using h

/-- Frobenius on original cohomology is semilinear for the constructed scalar action. -/
def structureCohomologyFrobenius (p : ℕ) [Fact p.Prime] [CharP k p] (q : ℕ) :
    Sheaf.H.{w} (additiveStructureSheaf Y.left) q →ₛₗ[_root_.frobenius k p]
      Sheaf.H.{w} (additiveStructureSheaf Y.left) q where
  toAddHom := Sheaf.H.map (structureFrobenius Y.left p (Fact.out)
    (primeCast_global_eq_zero Y p)) q
  map_smul' a x := by
    change Sheaf.H.map _ q (Sheaf.H.map (structureScalar Y.left (Scheme.constants Y a)) q x) =
      Sheaf.H.map (structureScalar Y.left (Scheme.constants Y (_root_.frobenius k p a))) q
        (Sheaf.H.map _ q x)
    rw [← Sheaf.H.map_comp_apply, structureScalar_frobenius,
      Sheaf.H.map_comp_apply]
    simp only [_root_.frobenius_def, map_pow]

/-- Original AS cohomology is exactly Frobenius minus the identity, not a replacement map. -/
theorem artinSchreier_cohomology_apply (p : ℕ) [Fact p.Prime] [CharP k p]
    (q : ℕ) (x : Sheaf.H.{w} (additiveStructureSheaf Y.left) q) :
    Sheaf.H.map (artinSchreierMap Y.left p (Fact.out) (primeCast_global_eq_zero Y p)) q x =
      structureCohomologyFrobenius Y p q x - x := by
  change (Sheaf.functorH _ q).map (_ - 𝟙 _) x = _
  rw [CategoryTheory.Functor.map_sub, CategoryTheory.Functor.map_id]
  rfl

/-- Finite dimensionality over a separably closed field gives the actual AS surjectivity. -/
theorem artinSchreier_cohomology_surjective (p : ℕ) [Fact p.Prime] [CharP k p]
    [IsSepClosed k] (q : ℕ)
    [FiniteDimensional k (Sheaf.H.{w} (additiveStructureSheaf Y.left) q)] :
    Function.Surjective (Sheaf.H.map
      (artinSchreierMap Y.left p (Fact.out) (primeCast_global_eq_zero Y p)) q) := by
  intro x
  obtain ⟨y, hy⟩ := LinearMap.surjective_sub_id_of_frobenius p
    (structureCohomologyFrobenius Y p q) x
  exact ⟨y, (artinSchreier_cohomology_apply Y p q y).trans hy⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
