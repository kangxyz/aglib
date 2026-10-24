/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.Trace.Coordinates
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.GlobalSections
public import Aglib.AlgebraicGeometry.Cohomology.Modules.ScalarFactorization
public import Aglib.AlgebraicGeometry.Cohomology.Proper.StructureSheaf.Coefficient
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Limits

/-!
# Original finite trace coordinates on cohomology

The actual trace-coordinate and adjugate sheaf maps induce their original
scalar factorization on cohomology. The affine comparison and the original
structural square identify the source action. Length restriction retains the
actual residue degree; the trace-coordinate map need only be base-linear.

The resulting inequality holds in every degree, without finite-length or
splitting hypotheses. Its current consumer is the separable surface H1
bound. This module does not construct a dominating model or prove a uniform
bound over all models.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

private theorem scalarFactorization_conjugate
    {R M P N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    [AddCommGroup N] [Module R N]
    (d : R) (e : P ≃ₗ[R] M) (f : P →ₗ[R] N) (g : N →ₗ[R] P)
    (h : g.comp f = d • LinearMap.id) :
    (e.toLinearMap.comp g).comp (f.comp e.symm.toLinearMap) =
      d • LinearMap.id := by
  apply LinearMap.ext
  intro x
  have hx := DFunLike.congr_fun h (e.symm x)
  change g (f (e.symm x)) = d • e.symm x at hx
  change e (g (f (e.symm x))) = d • x
  rw [hx, e.map_smul, e.apply_symm_apply]

/-- The actual finite diagram bounds original cohomology by its fixed
trace-discriminant torsion and the original base cohomology. -/
theorem finiteTraceCohomology_length_le
    (A B : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    [CommRing B] [IsDomain B] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    [Module.Finite A B] [FaithfulSMul A B] [IsIntegrallyClosed A]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (π : Y ⟶ X) [IsDominant π] [IsFinite π] (hX : NormalStalks X)
    (a : X ⟶ Spec (.of A)) (b : Y ⟶ Spec (.of B))
    [IsDominant a] [IsDominant b]
    (ha : IsIso (CommRingCat.ofHom (functionFieldMap a)))
    (hb : IsIso (CommRingCat.ofHom (functionFieldMap b)))
    (hsq : π ≫ a = b ≫ FiniteTraceCoordinates.baseMap A B) (n : ℕ) :
    letI := moduleCohomologyModuleOfHom Y (FiniteTraceCoordinates.structureScalar b)
      (FiniteTraceCoordinates.structureModule Y) n
    letI := moduleCohomologyModuleOfHom X (FiniteTraceCoordinates.structureScalar a)
      (FiniteTraceCoordinates.structureModule X) n
    Module.length B
        (Sheaf.H.{u + 1} (moduleAddSheaf Y (FiniteTraceCoordinates.structureModule Y)) n) ≤
      Module.length B
          (Submodule.torsionBy B
            (Sheaf.H.{u + 1} (moduleAddSheaf Y (FiniteTraceCoordinates.structureModule Y)) n)
            (algebraMap A B (FiniteTraceCoordinates.fixedDiscriminant A B))) *
        Module.length (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) +
      (FiniteTraceCoordinates.degree A B : ℕ∞) * Module.length A
        (Sheaf.H.{u + 1} (moduleAddSheaf X (FiniteTraceCoordinates.structureModule X)) n) := by
  let α := FiniteTraceCoordinates.structureScalar a
  let β := FiniteTraceCoordinates.structureScalar b
  let ε := π.appTop.hom.comp α
  let OX := FiniteTraceCoordinates.structureModule X
  let OY := FiniteTraceCoordinates.structureModule Y
  let P := FiniteTraceCoordinates.directImageStructure π
  let N := FiniteTraceCoordinates.target A B (X := X)
  let d := FiniteTraceCoordinates.fixedDiscriminant A B
  let := moduleCohomologyModuleOfHom X α P n
  let := moduleCohomologyModuleOfHom X α N n
  let := moduleCohomologyModuleOfHom X α OX n
  let := moduleCohomologyModuleOfHom Y ε OY n
  let := moduleCohomologyModuleOfHom Y β OY n
  let : IsScalarTower A B (Sheaf.H.{u + 1} (moduleAddSheaf Y OY) n) :=
    moduleCohomologyScalarTowerOfEq Y A B ε β
      (FiniteTraceCoordinates.scalar_square A B π a b hsq) OY n
  let : OY.IsQuasicoherent := quasicoherent_of_affineCharts OY
    (fun R j _ => ((affineLocallyFiniteType_unit Y) R j).1)
  let e : Sheaf.H.{u + 1} (moduleAddSheaf X P) n ≃ₗ[A]
      Sheaf.H.{u + 1} (moduleAddSheaf Y OY) n :=
    moduleAffinePushforwardCohomologyLinearEquiv π α OY n
  let φ := FiniteTraceCoordinates.coordinates A B π hX b
  let ψ := FiniteTraceCoordinates.adjugateExpansion A B π b
  let f := moduleCohomologyMapOfHom X α φ n
  let g := moduleCohomologyMapOfHom X α ψ n
  have hfg : g.comp f = d • LinearMap.id :=
    moduleCohomologyMap_scalarFactorization X α d φ ψ
      (FiniteTraceCoordinates.coordinates_comp_adjugateExpansion A B π hX a b ha hb hsq) n
  have hconj := scalarFactorization_conjugate d e f g hfg
  have hbound := Module.length_le_torsionBy_mul_residue_add_of_comp_smul_id (B := B) d
    (f.comp e.symm.toLinearMap) (e.toLinearMap.comp g) hconj
  have hN : Module.length A (Sheaf.H.{u + 1} (moduleAddSheaf X N) n) =
      (FiniteTraceCoordinates.degree A B : ℕ∞) *
        Module.length A (Sheaf.H.{u + 1} (moduleAddSheaf X OX) n) :=
    moduleCohomologyFiniteCopies_length X α n OX (FiniteTraceCoordinates.degree A B)
  exact hbound.trans_eq (congrArg
    (fun z => Module.length B
      (Submodule.torsionBy B (Sheaf.H.{u + 1} (moduleAddSheaf Y OY) n)
        (algebraMap A B d)) *
      Module.length (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) + z) hN)

end AlgebraicGeometry.Scheme.Cohomology
