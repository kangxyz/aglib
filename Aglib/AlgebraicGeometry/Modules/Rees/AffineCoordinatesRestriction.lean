/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Rees.AffineCoordinatesImage

/-! # Restriction naturality of the canonical affine Rees coordinates -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory Limits Opposite
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules.Rees

open Scheme.Cohomology

variable {A : Type u} [CommRing A] (I : Ideal A)
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
  (F : X.Modules) [F.IsQuasicoherent]
  {U V : X.Opens}

/-- The original structural-linear restriction of the coefficient. -/
abbrev originalRestriction (hUV : U ≤ V) :
    originalSections f F V →ₗ[A] originalSections f F U :=
  ((moduleSectionsPresheaf X
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) F).map
      (homOfLE hUV).op).hom

/-- Restriction on the pulled coefficient at the actual inverse-image opens. -/
abbrev pulledRestriction (hUV : U ≤ V) :
    pulledSections I f F V →ₗ[reesAlgebra I] pulledSections I f F U :=
  ((moduleSectionsPresheaf (space I f)
    ((structureMap I f).appTop.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of (reesAlgebra I))).inv.hom)
    (pulledCoefficient I f F)).map
      ((TopologicalSpace.Opens.map (projection I f).base).map (homOfLE hUV)).op).hom

/-- Restriction on the actual image coefficient. -/
abbrev coefficientRestriction (hUV : U ≤ V) :
    coefficientSections I f F V →ₗ[reesAlgebra I] coefficientSections I f F U :=
  ((moduleSectionsPresheaf (space I f)
    ((structureMap I f).appTop.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of (reesAlgebra I))).inv.hom)
    (coefficient I f F)).map
      ((TopologicalSpace.Opens.map (projection I f).base).map (homOfLE hUV)).op).hom

/-- Scalar-extension coordinates commute with the original section restrictions. -/
theorem pulledSectionsEquiv_restriction (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hUV : U ≤ V) (x : reesAlgebra I ⊗[A] originalSections f F V) :
    pulledSectionsEquiv I f F U hU ((originalRestriction f F hUV).baseChange (reesAlgebra I) x) =
      pulledRestriction I f F hUV (pulledSectionsEquiv I f F V hV x) := by
  induction x using TensorProduct.inductionOn with
  | tmul b m =>
    change pulledSectionsEquiv I f F U hU
        (b ⊗ₜ[A] originalRestriction f F hUV m) = _
    rw [pulledSectionsEquiv_tmul, pulledSectionsEquiv_tmul]
    exact congrArg (fun k => k (b ⊗ₜ[A,algebraMap A (reesAlgebra I)] m))
      ((moduleSectionsBaseChangeMap f (algebraMap A (reesAlgebra I)) F).naturality
        (homOfLE hUV).op)
  | add x y hx hy => simp only [map_add, hx, hy]

omit [F.IsQuasicoherent] in
/-- The actual coefficient quotient commutes with restriction. -/
theorem toCoefficient_restriction (hUV : U ≤ V) (m : pulledSections I f F V) :
    coefficientRestriction I f F hUV
        ((toCoefficient I f F).app (projection I f ⁻¹ᵁ V) m) =
      (toCoefficient I f F).app (projection I f ⁻¹ᵁ U)
        (pulledRestriction I f F hUV m) := by
  exact (PresheafOfModules.naturality_apply (toCoefficient I f F).val
    ((TopologicalSpace.Opens.map (projection I f).base).map (homOfLE hUV)).op m).symm

omit [F.IsQuasicoherent] in
/-- Polynomial restriction commutes with the original Rees tensor image map. -/
theorem moduleImageMap_restriction (hUV : U ≤ V)
    (x : reesAlgebra I ⊗[A] originalSections f F V) :
    PolynomialModule.map A (originalRestriction f F hUV)
        (reesAlgebra.moduleImageMap I (originalSections f F V) x) =
      reesAlgebra.moduleImageMap I (originalSections f F U)
        ((originalRestriction f F hUV).baseChange (reesAlgebra I) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul b m =>
    change PolynomialModule.map A (originalRestriction f F hUV)
        (b.val • PolynomialModule.single A 0 m) =
      b.val • PolynomialModule.single A 0 (originalRestriction f F hUV m)
    simp [PolynomialModule.map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Polynomial coordinates of actual image sections commute with restriction. -/
theorem coefficientSectionsToPolynomial_restriction
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ≤ V)
    (m : coefficientSections I f F V) :
    coefficientSectionsToPolynomial I f F U hU (coefficientRestriction I f F hUV m) =
      PolynomialModule.map A (originalRestriction f F hUV)
        (coefficientSectionsToPolynomial I f F V hV m) := by
  obtain ⟨n, rfl⟩ := toCoefficient_sections_surjective I f F V hV m
  obtain ⟨x, rfl⟩ := (pulledSectionsEquiv I f F V hV).surjective n
  rw [toCoefficient_restriction, ← pulledSectionsEquiv_restriction I f F hU hV hUV x,
    coefficientSectionsToPolynomial_toCoefficient,
    coefficientSectionsToPolynomial_toCoefficient]
  exact (moduleImageMap_restriction I f F hUV x).symm

/-- The equivalence retains restriction in the ambient polynomial module. -/
theorem coefficientSectionsEquiv_restriction
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ≤ V)
    (m : coefficientSections I f F V) :
    (coefficientSectionsEquiv I f F U hU (coefficientRestriction I f F hUV m)).val =
      PolynomialModule.map A (originalRestriction f F hUV)
        (coefficientSectionsEquiv I f F V hV m).val :=
  coefficientSectionsToPolynomial_restriction I f F hU hV hUV m

end AlgebraicGeometry.Scheme.Modules.Rees
