/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Geometrically.Integral.GlobalSections
public import Aglib.AlgebraicGeometry.ResidueField.Constants
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Aglib.AlgebraicGeometry.Cohomology.Modules.StructureSheaf

/-!
# Fields and finite-dimensional global sections of proper integral schemes

Native proper coherent cohomology finiteness supplies H0 finiteness. Source additionally
constructs the actual global-section FIELD structure and injective residue-evaluation maps for
integral proper schemes.

Source: `R5Lab.Aglib.AlgebraicGeometry.Morphisms.Proper.GlobalSections`, frozen R5
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`b2d5dec292692420ec507336fea4c038526d4771aabcab1ea5750aaf0ef24dee`. Selected lines: [[55, 132]].
The actual objects, canonical maps, universes and stated premises are retained.
-/

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.OverField (FScheme)

namespace AlgebraicGeometry.Scheme
universe u
attribute [local instance] globalSectionsModule
variable {F : Type u} [Field F]

/-- Properness and integrality derive a field structure on actual global sections. -/
theorem globalSections_isField (X : FScheme F) [IsProper X.hom] [IsIntegral X.left] :
    IsField Γ(X.left, ⊤) := by
  let : Algebra F Γ(X.left, ⊤) := (constants X).toAlgebra
  let : Algebra.IsIntegral F Γ(X.left, ⊤) := ⟨constants_isIntegral_of_proper X⟩
  exact isField_of_isIntegral_of_isField' (Field.toIsField F)

/-- Native global residue evaluation is the ring map of the residue-field point
followed by actual scheme affinization. -/
theorem fromSpecResidueField_toSpecΓ (X : Scheme.{u}) (x : X) :
    X.fromSpecResidueField x ≫ X.toSpecΓ = Spec.map (X.Γevaluation x) := by
  rw [Scheme.fromSpecResidueField, Category.assoc, Scheme.fromSpecStalk_toSpecΓ,
    ← Spec.map_comp]
  rfl

/-- The exact native global evaluation map sends structural constants to the
existing structural residueConstants map. -/
theorem evaluation_comp_constants (X : FScheme F) (x : X.left) :
    (X.left.Γevaluation x).hom.comp (constants X) = residueConstants X.left X.hom x := by
  change (CommRingCat.ofHom (constants X) ≫ X.left.Γevaluation x).hom =
    (Spec.preimage (X.left.fromSpecResidueField x ≫ X.hom)).hom
  congr 1
  apply Spec.map_injective
  rw [Spec.map_comp, Spec.map_preimage, ← fromSpecResidueField_toSpecΓ,
    Category.assoc, _root_.AlgebraicGeometry.Scheme.structureMap_factorsThroughAffinization]

/-- Native global residue evaluation, linear for the exact existing residueAlgebra. -/
def residueEvaluationLinearMap (X : FScheme F) (x : X.left) :
    letI := residueAlgebra X.left X.hom x
    Γ(X.left, ⊤) →ₗ[F] X.left.residueField x := by
  letI := residueAlgebra X.left X.hom x
  exact {
    __ := (X.left.Γevaluation x).hom.toAddMonoidHom
    map_smul' a b := by
      change (X.left.Γevaluation x).hom (constants X a * b) =
        residueConstants X.left X.hom x a * (X.left.Γevaluation x).hom b
      rw [map_mul]
      have h := congrArg (fun f : F →+* X.left.residueField x => f a)
        (evaluation_comp_constants X x)
      exact congrArg (fun z => z * (X.left.Γevaluation x).hom b) h }

/-- The native global evaluation map at any point is injective because the
global-section field structure is derived from properness and integrality. -/
theorem residueEvaluation_injective (X : FScheme F) [IsProper X.hom] [IsIntegral X.left]
    (x : X.left) : Function.Injective (X.left.Γevaluation x).hom := by
  let : Field Γ(X.left, ⊤) := (globalSections_isField X).toField
  exact RingHom.injective _

/-- Every nonempty locally finite type field scheme has an actual closed point;
no rational-point assumption is needed. -/
theorem exists_closedPoint (X : FScheme F) [LocallyOfFiniteType X.hom] [Nonempty X.left] :
    Nonempty (ClosedPoint X.left) := by
  let : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  obtain ⟨x, _, hx⟩ := nonempty_inter_closedPoints (X := X.left)
    (Z := Set.univ) Set.univ_nonempty isClosed_univ.isLocallyClosed
  exact ⟨⟨x, hx⟩⟩

/-- Evaluation at a closed point injects the actual global sections into the
existing finite residue extension, with its original structural scalar action. -/
theorem globalSections_finite_of_closedPoint (X : FScheme F) [IsProper X.hom] [IsIntegral X.left]
    (x : ClosedPoint X.left) :
    Module.Finite F Γ(X.left, ⊤) := by
  let := residueAlgebra X.left X.hom x.val
  let : Module.Finite F (X.left.residueField x.val) := residue_finite X.left X.hom x
  exact Module.Finite.of_injective (residueEvaluationLinearMap X x.val)
    (residueEvaluation_injective X x.val)

/-- Every proper integral field scheme has finite actual global sections,
in arbitrary dimension and without geometric-integrality or finiteness-family inputs. -/
theorem globalSections_finite (X : FScheme F) [IsProper X.hom] [IsIntegral X.left] :
    Module.Finite F Γ(X.left, ⊤) := by
  obtain ⟨x⟩ := exists_closedPoint X
  exact globalSections_finite_of_closedPoint X x

/-- The actual Ext-defined structure-sheaf H⁰ of every proper integral field
scheme is finite, via the already constructed scalar-compatible H⁰ comparison. -/
theorem structureH0_finite (X : FScheme F) [IsProper X.hom] [IsIntegral X.left] :
    Module.Finite F (structureCohomology F X 0) := by
  let := globalSections_finite X
  exact Module.Finite.of_surjective (structureH0Equiv X).symm.toLinearMap
    (structureH0Equiv X).symm.surjective

end AlgebraicGeometry.Scheme
