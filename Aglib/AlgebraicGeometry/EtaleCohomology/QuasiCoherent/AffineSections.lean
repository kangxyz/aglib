/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.SectionsDescent
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Affine.PullbackSections

/-!
# Affine coordinates of actual quasi-coherent descent sections

On affine test schemes the section comparison is the native extension-of-scalars
comparison, with no flatness or finite-generation condition on the coefficient.
No such tensor formula is used on a nonaffine test scheme.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

variable (X : Scheme.{u}) [IsAffine X] (F : X.Modules) [F.IsQuasicoherent]

/-- On an affine test scheme the genuine Hom-descent value has native tensor coordinates. -/
def affineSectionsEquiv (T : Over X) [IsAffine T.left] :
    (homPresheaf X F).obj (op T) ≃
      (ModuleCat.extendScalars T.hom.appTop.hom).obj ((affineΓFunctor X).obj F) :=
  (sectionsEquiv X F T).trans (affinePullbackSectionsIso T.hom F).toLinearEquiv.toEquiv.symm

/-- Returning from affine coordinates gives the original pullback sections. -/
theorem sectionsEquiv_affineSectionsEquiv_symm (T : Over X) [IsAffine T.left]
    (s : (ModuleCat.extendScalars T.hom.appTop.hom).obj ((affineΓFunctor X).obj F)) :
    sectionsEquiv X F T ((affineSectionsEquiv X F T).symm s) =
      (affinePullbackSectionsIso T.hom F).hom s := by
  exact (sectionsEquiv X F T).apply_symm_apply _

/-- The tensor unit is precisely the original geometric pullback unit. -/
theorem sectionsEquiv_affineSectionsEquiv_symm_one_tmul
    (T : Over X) [IsAffine T.left] (s : (affineΓFunctor X).obj F) :
    sectionsEquiv X F T ((affineSectionsEquiv X F T).symm
      ((1 : Γ(T.left, ⊤)) ⊗ₜ[Γ(X, ⊤),T.hom.appTop.hom] s)) =
      (((pullbackPushforwardAdjunction T.hom).unit.app F).app ⊤) s := by
  exact (sectionsEquiv_affineSectionsEquiv_symm X F T _).trans
    (affinePullbackSectionsIso_one_tmul T.hom F s)

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
