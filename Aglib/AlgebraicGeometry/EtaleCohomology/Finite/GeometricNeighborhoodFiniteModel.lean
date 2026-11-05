/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.GeometricNeighborhoodLimit
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.GeometricNeighborhoodBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.FiniteAffineModel

/-! # The actual finite Henselian model of the original pointed limit

For an original finite source, the actual geometric-neighborhood base change
is finite over the constructed Henselian neighborhood ring. Its own global
sections and native affine isomorphism supply the model required by finite
pointed stage lifting. No model existence or reconstruction iso is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood
universe u
variable (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsFinite f]

/-- The original finite projection from the actual limit base change. -/
def limitFiniteProjection : (baseChangedCone R Ω f).pt.left ⟶
    Spec (.of (GeometricEtaleColimit R Ω)) :=
  pullback.fst (Spec.algebraMap R (GeometricEtaleColimit R Ω)) f

instance limitFiniteProjection_isFinite : IsFinite (limitFiniteProjection R Ω f) :=
  inferInstanceAs (IsFinite
    (pullback.fst (Spec.algebraMap R (GeometricEtaleColimit R Ω)) f))

instance limitSource_isAffine : IsAffine (baseChangedCone R Ω f).pt.left :=
  isAffine_of_isAffineHom (limitFiniteProjection R Ω f)

/-- The model ring is the original limit source's global-section ring. -/
abbrev limitSourceRing := Γ((baseChangedCone R Ω f).pt.left, ⊤)

/-- The original structural map defines the algebra, without replacing the ring. -/
@[instance_reducible]
def limitSourceAlgebra : Algebra (GeometricEtaleColimit R Ω) (limitSourceRing R Ω f) :=
  finiteSourceAlgebra (GeometricEtaleColimit R Ω) (limitFiniteProjection R Ω f)

/-- Actual finiteness over the constructed Henselian ring. -/
theorem limitSource_moduleFinite :
    let := limitSourceAlgebra R Ω f
    Module.Finite (GeometricEtaleColimit R Ω) (limitSourceRing R Ω f) :=
  finiteSource_moduleFinite (GeometricEtaleColimit R Ω) (limitFiniteProjection R Ω f)

/-- The required E is the original source's native affine isomorphism. -/
def limitSourceIso : Spec (.of (limitSourceRing R Ω f)) ≅
    (baseChangedCone R Ω f).pt.left :=
  ((baseChangedCone R Ω f).pt.left).isoSpec.symm

/-- The reconstruction keeps the actual map to the Henselian base. -/
theorem limitSourceIso_projection :
    let := limitSourceAlgebra R Ω f
    (limitSourceIso R Ω f).hom ≫ limitFiniteProjection R Ω f =
      Spec.algebraMap (GeometricEtaleColimit R Ω) (limitSourceRing R Ω f) :=
  (finiteSource_spec_algebraMap (GeometricEtaleColimit R Ω)
    (limitFiniteProjection R Ω f)).symm

/-- The original target-X map is retained under reconstruction. -/
def limitSourceTargetMap : Spec (.of (limitSourceRing R Ω f)) ⟶ X :=
  (limitSourceIso R Ω f).hom ≫ (baseChangedCone R Ω f).pt.hom

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood
