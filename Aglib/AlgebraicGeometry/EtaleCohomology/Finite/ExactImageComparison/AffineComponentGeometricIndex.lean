/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.AffineExtendedPoint
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.FiniteComponentGeometricIndex
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.PointOverEquiv

/-! # Indexing the actual affine finite stalk by original geometric fibre points -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood

universe u

variable (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω] [IsAlgClosed Ω]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsFinite f]

/-- The actual maximal-component index of the strict-local finite source is
canonically in bijection with the original `Ω`-valued geometric fibre of `f`. -/
def finiteAffineComponentGeometricIndex :
    MaximalSpectrum Γ(finiteAffineSource R Ω f, ⊤) ≃
      {x : Spec (.of Ω) ⟶ X // x ≫ f = Spec.algebraMap R Ω} := by
  let B := GeometricEtaleColimit R Ω
  let Y := finiteAffineSource R Ω f
  let p : Y ⟶ Spec (.of B) := finiteAffineProjection R Ω f
  let : IsFinite p := inferInstanceAs (IsFinite
    (pullback.fst (Spec.algebraMap R (GeometricEtaleColimit R Ω)) f))
  let : IsAffine Y := isAffine_of_isAffineHom p
  let := finiteSourceAlgebra B p
  let := finiteSource_moduleFinite B p
  let : Algebra (ResidueField B) Ω := (GeometricEtaleColimit.residueFieldEmbedding R Ω).toAlgebra
  let b : Spec (.of Ω) ⟶ Spec (.of B) := Spec.map (CommRingCat.ofHom
    ((algebraMap (ResidueField B) Ω).comp (IsLocalRing.residue B)))
  have hb : b = point R Ω := by
    change Spec.map (CommRingCat.ofHom
      ((GeometricEtaleColimit.residueFieldEmbedding R Ω).comp (IsLocalRing.residue B))) = _
    rw [GeometricEtaleColimit.residueFieldEmbedding_comp_residue]
    rfl
  have ht : b ≫ Spec.algebraMap R B = Spec.algebraMap R Ω :=
    (congrArg (fun t => t ≫ Spec.algebraMap R B) hb).trans (point_structure R Ω)
  exact (finiteComponentGeometricIndex B Γ(Y, ⊤) Ω).trans
    ((pointOverEquivOfIso Y.isoSpec.symm (Spec.algebraMap B Γ(Y, ⊤)) p
      (finiteSource_spec_algebraMap B p).symm b).trans
      ((pullbackPointOverEquiv (Spec.algebraMap R B) f b).trans
        (pointOverEquivOfBaseEq f ht)))

/-- The index equivalence sends each component to the original residue point
extended to `Ω`, retaining the previously proved literal point map. -/
theorem finiteAffineComponentGeometricIndex_apply
    (m : MaximalSpectrum Γ(finiteAffineSource R Ω f, ⊤)) :
    (finiteAffineComponentGeometricIndex R Ω f m).val = finiteAffineExtendedPoint R Ω f m := by
  let B := GeometricEtaleColimit R Ω
  let Y := finiteAffineSource R Ω f
  let p : Y ⟶ Spec (.of B) := finiteAffineProjection R Ω f
  let : IsFinite p := inferInstanceAs (IsFinite
    (pullback.fst (Spec.algebraMap R (GeometricEtaleColimit R Ω)) f))
  let : IsAffine Y := isAffine_of_isAffineHom p
  let := finiteSourceAlgebra B p
  let := finiteSource_moduleFinite B p
  let : Algebra (ResidueField B) Ω := (GeometricEtaleColimit.residueFieldEmbedding R Ω).toAlgebra
  change (Spec.map (CommRingCat.ofHom (finiteComponentPoint B Γ(Y, ⊤) Ω m)) ≫
    Y.isoSpec.inv) ≫ (baseChangedEtaleCone R Ω f).pt.hom =
      extendedFiniteComponentPoint B Γ(Y, ⊤) Ω
        (Y.isoSpec.inv ≫ (baseChangedEtaleCone R Ω f).pt.hom) m
  rw [extendedFiniteComponentPoint_eq, Category.assoc]

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood
