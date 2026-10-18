/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.Conormal.Frames

/-!
# The original affine conormal arrows under change of the base algebra

The native differential map preserves every original d value. The two
original cotangent equivalences identify the same ideal tensor class.
These actual maps commute with the original positive conormal arrow and
quotient differential arrow. No smoothness or regular-list premise is used.
-/

@[expose] public section
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Differentials
open scoped TensorProduct ChangeOfRings

universe u
namespace AlgebraicGeometry.Scheme.Modules

variable {R S A B : CommRingCat.{u}} (ρ : R ⟶ S) (β : S ⟶ A)

/-- The original native differential map for the base square with identity on the target. -/
def canonicalBaseDifferentialMap :
    CommRingCat.KaehlerDifferential (ρ ≫ β) ⟶ CommRingCat.KaehlerDifferential β :=
  CommRingCat.KaehlerDifferential.map (f := ρ ≫ β) (f' := β) (g := ρ) (g' := 𝟙 A)
    (by simp)

/-- The original base map carries each original d(a) to that same d(a). -/
theorem canonicalBaseDifferentialMap_d (a : A) :
    canonicalBaseDifferentialMap ρ β (CommRingCat.KaehlerDifferential.d (f := ρ ≫ β) a) =
      CommRingCat.KaehlerDifferential.d (f := β) a :=
  CommRingCat.KaehlerDifferential.map_d (by simp) a

variable (σ : A ⟶ B) (hσ : Function.Surjective σ)

/-- The same original tensor-ideal presentation identifies the two native cotangent modules. -/
def canonicalBaseConormalIso :
    relativeConormalAffineModule (ρ ≫ β) σ hσ ≅ relativeConormalAffineModule β σ hσ := by
  letI := (ρ ≫ β).hom.toAlgebra
  letI := ((ρ ≫ β) ≫ σ).hom.toAlgebra
  letI := β.hom.toAlgebra
  letI := (β ≫ σ).hom.toAlgebra
  letI := σ.hom.toAlgebra
  let E := relativeConormalAffineExtension (ρ ≫ β) σ hσ
  let E' := relativeConormalAffineExtension β σ hσ
  exact E.cotangentEquiv.toModuleIso.symm ≪≫ E'.cotangentEquiv.toModuleIso

/-- The actual cotangent comparison retains each original ideal class. -/
theorem canonicalBaseConormalIso_class (x : RingHom.ker σ.hom) :
    (canonicalBaseConormalIso ρ β σ hσ).hom (relativeConormalAffineClass (ρ ≫ β) σ hσ x) =
      relativeConormalAffineClass β σ hσ x := by
  let := (ρ ≫ β).hom.toAlgebra
  let := ((ρ ≫ β) ≫ σ).hom.toAlgebra
  let := β.hom.toAlgebra
  let := (β ≫ σ).hom.toAlgebra
  let := σ.hom.toAlgebra
  let E := relativeConormalAffineExtension (ρ ≫ β) σ hσ
  let E' := relativeConormalAffineExtension β σ hσ
  have hE : E.cotangentEquiv ((1 : B) ⊗ₜ[A] x) =
      relativeConormalAffineClass (ρ ≫ β) σ hσ x :=
    (Algebra.Extension.contangentEquiv_tmul (P := E) (1 : B) x).trans (one_smul B _)
  have hE' : E'.cotangentEquiv ((1 : B) ⊗ₜ[A] x) =
      relativeConormalAffineClass β σ hσ x :=
    (Algebra.Extension.contangentEquiv_tmul (P := E') (1 : B) x).trans (one_smul B _)
  have hi : E.cotangentEquiv.symm (relativeConormalAffineClass (ρ ≫ β) σ hσ x) =
      ((1 : B) ⊗ₜ[A] x) := by
    apply E.cotangentEquiv.injective
    rw [LinearEquiv.apply_symm_apply]
    exact hE.symm
  change E'.cotangentEquiv (E.cotangentEquiv.symm
    (relativeConormalAffineClass (ρ ≫ β) σ hσ x)) = _
  exact (congrArg E'.cotangentEquiv hi).trans hE'

/-- The original positive kernel-class-to-differential arrow commutes with base change. -/
theorem canonicalBaseConormal_f :
    relativeConormalAffineLinearF (ρ ≫ β) σ hσ ≫
        (ModuleCat.extendScalars σ.hom).map (canonicalBaseDifferentialMap ρ β) =
      (canonicalBaseConormalIso ρ β σ hσ).hom ≫ relativeConormalAffineLinearF β σ hσ := by
  let := (ρ ≫ β).hom.toAlgebra
  let := ((ρ ≫ β) ≫ σ).hom.toAlgebra
  let := σ.hom.toAlgebra
  let E := relativeConormalAffineExtension (ρ ≫ β) σ hσ
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨a, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective (P := E) x
  change (ModuleCat.extendScalars σ.hom).map (canonicalBaseDifferentialMap ρ β)
      (relativeConormalAffineLinearF (ρ ≫ β) σ hσ
        (relativeConormalAffineClass (ρ ≫ β) σ hσ a)) =
    relativeConormalAffineLinearF β σ hσ
      ((canonicalBaseConormalIso ρ β σ hσ).hom
        (relativeConormalAffineClass (ρ ≫ β) σ hσ a))
  rw [relativeConormalAffineLinearF_class (ρ ≫ β) σ hσ a,
    canonicalBaseConormalIso_class ρ β σ hσ a,
    relativeConormalAffineLinearF_class β σ hσ a,
    ModuleCat.ExtendScalars.map_tmul, canonicalBaseDifferentialMap_d]

/-- The original quotient differential arrow commutes with the same native base maps. -/
theorem canonicalBaseConormal_g :
    relativeConormalAffineLinearG (ρ ≫ β) σ hσ ≫ canonicalBaseDifferentialMap ρ (β ≫ σ) =
      (ModuleCat.extendScalars σ.hom).map (canonicalBaseDifferentialMap ρ β) ≫
        relativeConormalAffineLinearG β σ hσ := by
  let := σ.hom.toAlgebra
  apply ((ModuleCat.extendRestrictScalarsAdj σ.hom).homEquiv _ _).injective
  apply CommRingCat.KaehlerDifferential.ext
  intro a
  change canonicalBaseDifferentialMap ρ (β ≫ σ)
      (relativeConormalAffineLinearG (ρ ≫ β) σ hσ
        ((1 : B) ⊗ₜ[A] CommRingCat.KaehlerDifferential.d (f := ρ ≫ β) a)) =
    relativeConormalAffineLinearG β σ hσ
      ((ModuleCat.extendScalars σ.hom).map (canonicalBaseDifferentialMap ρ β)
        ((1 : B) ⊗ₜ[A] CommRingCat.KaehlerDifferential.d (f := ρ ≫ β) a))
  rw [relativeConormalAffineLinearG_tmul, one_smul, canonicalBaseDifferentialMap_d,
    ModuleCat.ExtendScalars.map_tmul, canonicalBaseDifferentialMap_d,
    relativeConormalAffineLinearG_tmul, one_smul]

/-- The actual original affine conormal short-complex morphism under base change. -/
def canonicalBaseConormalComplexMap :
    relativeConormalAffineLinearComplex (ρ ≫ β) σ hσ ⟶
      relativeConormalAffineLinearComplex β σ hσ :=
  CategoryTheory.ShortComplex.homMk (canonicalBaseConormalIso ρ β σ hσ).hom
    ((ModuleCat.extendScalars σ.hom).map (canonicalBaseDifferentialMap ρ β))
    (canonicalBaseDifferentialMap ρ (β ≫ σ))
    (canonicalBaseConormal_f ρ β σ hσ).symm (canonicalBaseConormal_g ρ β σ hσ).symm

end AlgebraicGeometry.Scheme.Modules
