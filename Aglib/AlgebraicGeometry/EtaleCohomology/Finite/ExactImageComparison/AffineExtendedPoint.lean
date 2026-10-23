/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.FiniteComponentStalkExtension
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.AffineDirectImageStalk

/-! # Actual common-field component points of the original affine finite source -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood

universe u

variable (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω] [IsAlgClosed Ω]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsFinite f]

/-- The actual common-field point of the original finite source selected by a
maximal component of its strict-local base change. -/
def finiteAffineExtendedPoint (m : MaximalSpectrum Γ(finiteAffineSource R Ω f, ⊤)) :
    Spec (.of Ω) ⟶ X := by
  let B := GeometricEtaleColimit R Ω
  let Y := finiteAffineSource R Ω f
  let p : Y ⟶ Spec (.of B) := finiteAffineProjection R Ω f
  let : IsFinite p := inferInstanceAs (IsFinite
    (pullback.fst (Spec.algebraMap R (GeometricEtaleColimit R Ω)) f))
  let : IsAffine Y := isAffine_of_isAffineHom p
  let := finiteSourceAlgebra B p
  let := finiteSource_moduleFinite B p
  let : Algebra (ResidueField B) Ω := (GeometricEtaleColimit.residueFieldEmbedding R Ω).toAlgebra
  exact extendedFiniteComponentPoint B Γ(Y, ⊤) Ω
    (Y.isoSpec.inv ≫ (baseChangedEtaleCone R Ω f).pt.hom) m

/-- The chosen component point lies over the original fixed geometric point,
with equality of actual scheme maps rather than equality of supports. -/
theorem finiteAffineExtendedPoint_comp
    (m : MaximalSpectrum Γ(finiteAffineSource R Ω f, ⊤)) :
    finiteAffineExtendedPoint R Ω f m ≫ f = Spec.algebraMap R Ω := by
  let B := GeometricEtaleColimit R Ω
  let Y := finiteAffineSource R Ω f
  let p : Y ⟶ Spec (.of B) := finiteAffineProjection R Ω f
  let : IsFinite p := inferInstanceAs (IsFinite
    (pullback.fst (Spec.algebraMap R (GeometricEtaleColimit R Ω)) f))
  let : IsAffine Y := isAffine_of_isAffineHom p
  let := finiteSourceAlgebra B p
  let := finiteSource_moduleFinite B p
  let : Algebra (ResidueField B) Ω := (GeometricEtaleColimit.residueFieldEmbedding R Ω).toAlgebra
  let q : Spec (.of Γ(Y, ⊤)) ⟶ X := Y.isoSpec.inv ≫ (baseChangedEtaleCone R Ω f).pt.hom
  have hpb : (baseChangedEtaleCone R Ω f).pt.hom ≫ f =
      p ≫ Spec.algebraMap R B :=
    (pullback.condition (f := Spec.algebraMap R B) (g := f)).symm
  have hq : q ≫ f = Spec.algebraMap B Γ(Y, ⊤) ≫ Spec.algebraMap R B := by
    calc
      q ≫ f = Y.isoSpec.inv ≫ ((baseChangedEtaleCone R Ω f).pt.hom ≫ f) :=
        Category.assoc Y.isoSpec.inv (baseChangedEtaleCone R Ω f).pt.hom f
      _ = Y.isoSpec.inv ≫ (p ≫ Spec.algebraMap R B) :=
        congrArg (fun t : Y ⟶ Spec (.of R) => Y.isoSpec.inv ≫ t) hpb
      _ = (Y.isoSpec.inv ≫ p) ≫ Spec.algebraMap R B :=
        (Category.assoc Y.isoSpec.inv p (Spec.algebraMap R B)).symm
      _ = Spec.algebraMap B Γ(Y, ⊤) ≫ Spec.algebraMap R B :=
        congrArg (fun t => t ≫ Spec.algebraMap R B)
          (finiteSource_spec_algebraMap B p).symm
  have hb : Spec.map (CommRingCat.ofHom
      ((algebraMap (ResidueField B) Ω).comp (IsLocalRing.residue B))) = point R Ω := by
    change Spec.map (CommRingCat.ofHom
      ((GeometricEtaleColimit.residueFieldEmbedding R Ω).comp (IsLocalRing.residue B))) = _
    rw [GeometricEtaleColimit.residueFieldEmbedding_comp_residue]
    rfl
  change extendedFiniteComponentPoint B Γ(Y, ⊤) Ω q m ≫ f = _
  rw [extendedFiniteComponentPoint_eq, Category.assoc, hq, ← Category.assoc,
    finiteComponentPoint_spec_comp, hb]
  exact point_structure R Ω

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood
