/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.PullbackUnit
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.PullbackSections
public import Aglib.Algebra.Category.ModuleCat.BaseChange
public import Mathlib.AlgebraicGeometry.Group.Affine

/-!
# Algebra coordinates of sections over spectra

The original algebra action is compared through the actual `GammaSpec` inverse.
These coordinates therefore apply directly to the native algebraic Amitsur
conerve, without replacing a global-section ring by a definitionally equal ring.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

/-- The spectrum scalar action is induced by the original `GammaSpec` inverse. -/
theorem specSections_smul (A : CommRingCat.{u}) (M : (Spec A).Modules)
    (a : A) (s : moduleSpecΓFunctor.obj M) :
    (a • s : moduleSpecΓFunctor.obj M) =
      SMul.smul (M := Γ(Spec A, ⊤)) (α := Γ(M, ⊤)) ((Scheme.ΓSpecIso A).inv.hom a) s := by
  change SMul.smul (M := Γ(Spec A, ⊤)) (α := Γ(M, ⊤))
    ((Spec A).presheaf.map (𝟙 (op ⊤)) ((Scheme.ΓSpecIso A).inv.hom a)) s = _
  rw [CategoryTheory.Functor.map_id]
  rfl

variable (R : Type u) [CommRing R] (F : (Spec (CommRingCat.of R)).Modules)
  [F.IsQuasicoherent]

/-- Native tensor coordinates over an actual `R`-algebra. -/
def specTensorSectionsIso (A : CommAlgCat.{u} R) :
    ModuleCat.of A (A ⊗[R] moduleSpecΓFunctor.obj F) ≅
      moduleSpecΓFunctor.obj
        ((pullback (Spec.map (CommRingCat.ofHom (algebraMap R A)))).obj F) :=
  (ModuleCat.extendScalarsAlgebraIso R A (moduleSpecΓFunctor.obj F)).symm ≪≫
    affinePullbackGlobalSectionsIso (CommRingCat.ofHom (algebraMap R A)) F

/-- The original unit tensor is the original geometric unit section. -/
theorem specTensorSectionsIso_one_tmul (A : CommAlgCat.{u} R)
    (s : moduleSpecΓFunctor.obj F) :
    (specTensorSectionsIso R F A).hom ((1 : A) ⊗ₜ[R] s) =
      (((pullbackPushforwardAdjunction
        (Spec.map (CommRingCat.ofHom (algebraMap R A)))).unit.app F).app ⊤) s := by
  have h := congrArg (fun q => q s)
    (affinePullbackGlobalSectionsIso_unit (CommRingCat.ofHom (algebraMap R A)) F)
  change (affinePullbackGlobalSectionsIso (CommRingCat.ofHom (algebraMap R A)) F).hom
      ((1 : A) ⊗ₜ[R,algebraMap R A] s) = _ at h
  change (affinePullbackGlobalSectionsIso (CommRingCat.ofHom (algebraMap R A)) F).hom
      ((ModuleCat.extendScalarsAlgebraIso R A (moduleSpecΓFunctor.obj F)).inv
        ((1 : A) ⊗ₜ[R] s)) = _
  rw [ModuleCat.extendScalarsAlgebraIso_inv_tmul]
  exact h

/-- The scalar action in tensor coordinates uses the original `GammaSpec` ring isomorphism. -/
theorem specTensorSectionsIso_tmul (A : CommAlgCat.{u} R)
    (a : A) (s : moduleSpecΓFunctor.obj F) :
    (specTensorSectionsIso R F A).hom (a ⊗ₜ[R] s) =
      SMul.smul (M := Γ(Spec (CommRingCat.of A), ⊤))
        (α := Γ((pullback (Spec.map (CommRingCat.ofHom (algebraMap R A)))).obj F, ⊤))
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)
        ((((pullbackPushforwardAdjunction
          (Spec.map (CommRingCat.ofHom (algebraMap R A)))).unit.app F).app ⊤) s) := by
  have h : a ⊗ₜ[R] s = a • ((1 : A) ⊗ₜ[R] s) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h, _root_.map_smul]
  exact (congrArg (fun z : moduleSpecΓFunctor.obj
      ((pullback (Spec.map (CommRingCat.ofHom (algebraMap R A)))).obj F) => a • z)
    (specTensorSectionsIso_one_tmul R F A s)).trans
      (specSections_smul (CommRingCat.of A) _ a _)

/-- Pure tensor coordinates preserve every actual algebra morphism on the over-site. -/
theorem sectionsPresheaf_map_specTensor_tmul {A B : CommAlgCat.{u} R} (f : A ⟶ B)
    (a : A) (s : moduleSpecΓFunctor.obj F) :
    (sectionsPresheaf (Spec (CommRingCat.of R)) F).map
        ((algSpec (CommRingCat.of R)).map f.op).op
        ((specTensorSectionsIso R F A).hom (a ⊗ₜ[R] s)) =
      (specTensorSectionsIso R F B).hom (f.hom a ⊗ₜ[R] s) := by
  let k := (algSpec (CommRingCat.of R)).map f.op
  have hR : k.left.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) =
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (f.hom a) :=
    (congrArg (fun q => q.hom a)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f.hom.toRingHom))).symm
  exact (congrArg ((sectionsPresheaf (Spec (CommRingCat.of R)) F).map k.op)
    (specTensorSectionsIso_tmul R F A a s)).trans
    ((sectionsPresheaf_map_smul (Spec (CommRingCat.of R)) F k
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)
      ((((pullbackPushforwardAdjunction
        (Spec.map (CommRingCat.ofHom (algebraMap R A)))).unit.app F).app ⊤) s)).trans
      ((congrArg₂ (fun (r : Γ(Spec (CommRingCat.of B), ⊤))
          (z : Γ((pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))).obj F, ⊤)) => r • z)
        hR (sectionsPresheaf_map_unit (Spec (CommRingCat.of R)) F k s)).trans
          (specTensorSectionsIso_tmul R F B (f.hom a) s).symm))

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
