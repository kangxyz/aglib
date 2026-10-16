/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Affine.Vanishing
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Injective
public import Aglib.CategoryTheory.Abelian.Injective.MapAugmentation

/-!
# Original affine injective resolutions after sections

For a quasicoherent coefficient on an affine scheme, sections of any supplied
native injective resolution form a genuine injective module resolution.
Exactness in positive degrees is the proved affine acyclicity theorem;
degree zero uses preservation of kernels. Exact tilde makes sections preserve
injectives, without quasicoherence of any resolution term. The complex and
augmentation keep the original sections functor and resolution maps.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.AffineDerived

variable {R : CommRingCat.{u}} {M : (Spec R).Modules} (I : InjectiveResolution M)

/-- The augmentation is the original sections of the degree-zero resolution
map, extended by the native single-zero universal property. -/
def globalSectionsAugmentation :
    (CochainComplex.single₀ (ModuleCat R)).obj (moduleSpecΓFunctor.obj M) ⟶
      ((moduleSpecΓFunctor (R := R)).mapHomologicalComplex (.up ℕ)).obj I.cocomplex :=
  I.mapAugmentation moduleSpecΓFunctor

/-- Its original degree-zero component is literally the mapped resolution map. -/
@[simp]
theorem globalSectionsAugmentation_f_zero :
    (globalSectionsAugmentation I).f 0 = moduleSpecΓFunctor.map (I.ι.f 0) :=
  I.mapAugmentation_f_zero moduleSpecΓFunctor

/-- Native kernel preservation proves degree-zero exactness, even for a
coefficient that is not quasicoherent. -/
theorem globalSectionsAugmentation_quasiIsoAt_zero :
    QuasiIsoAt (globalSectionsAugmentation I) 0 :=
  I.mapAugmentation_quasiIsoAt_zero moduleSpecΓFunctor

variable [M.IsQuasicoherent]

/-- Affine acyclicity proves that this original sections augmentation is a
quasi-isomorphism; no resolution term is assumed quasicoherent. -/
instance globalSectionsAugmentation_quasiIso : QuasiIso (globalSectionsAugmentation I) :=
  I.mapAugmentation_quasiIso_of_isZero_rightDerived_succ moduleSpecΓFunctor
    (isZero_rightDerived_globalSections_succ M)

/-- Sections of the supplied original sheaf resolution give an actual module
injective resolution of the original coefficient's sections. -/
def globalSectionsInjectiveResolution : InjectiveResolution (moduleSpecΓFunctor.obj M) where
  cocomplex := ((moduleSpecΓFunctor (R := R)).mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  injective n := by
    change Injective (moduleSpecΓFunctor.obj (I.cocomplex.X n))
    infer_instance
  ι := globalSectionsAugmentation I

/-- The module resolution retains the same original mapped complex. -/
@[simp]
theorem globalSectionsInjectiveResolution_cocomplex :
    (globalSectionsInjectiveResolution I).cocomplex =
      ((moduleSpecΓFunctor (R := R)).mapHomologicalComplex (.up ℕ)).obj I.cocomplex := rfl

/-- Its augmentation retains the original sections augmentation. -/
@[simp]
theorem globalSectionsInjectiveResolution_ι :
    (globalSectionsInjectiveResolution I).ι = globalSectionsAugmentation I := rfl

end AlgebraicGeometry.Scheme.Modules.AffineDerived
