/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.ChartPullbackCoordinates

/-! # Original unit sections in affine-chart coordinates

Evaluation of the original categorical chart unit retains the actual geometric
coefficient on the original target chart. The module-sheaf and coordinate
objects remain abstract while the comparison is evaluated.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules

/-- Evaluation of the native affine pushforward section comparison is the
original coefficient evaluated on the whole affine source. -/
theorem moduleSpecΓFunctor_map_pushforwardGlobalSectionsIso_apply
    {R S : CommRingCat.{u}} (φ : R ⟶ S)
    {M : (Spec R).Modules} {N : (Spec S).Modules}
    (q : M ⟶ (pushforward (Spec.map φ)).obj N)
    (m : moduleSpecΓFunctor.obj M) :
    (moduleSpecΓFunctor.map q ≫ (pushforwardGlobalSectionsIso φ).hom.app N) m =
      q.app ⊤ m := rfl

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  {X Z : Scheme.{u}} (p : Z ⟶ X)
  (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
  (c : Spec (CommRingCat.of S) ⟶ Z) [IsOpenImmersion c]
  (H : c ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ j)
  (M : X.Modules) [M.IsQuasicoherent]

local notation "φ" => CommRingCat.ofHom (algebraMap R S)

/-- A scalar-extension unit tensor is the original restricted pullback-unit
section on the actual target chart. -/
theorem chartPullbackSectionsIso_one_tmul
    (m : moduleSpecΓFunctor.obj (M.restrict j)) :
    (chartPullbackSectionsIso p j c H M).hom ((1 : S) ⊗ₜ[R,(φ).hom] m) =
      (Nonflat.chartCoefficient p j c (Spec.map φ) H.symm
        ((pullbackPushforwardAdjunction p).unit.app M)).app ⊤ m := by
  have h := congrArg (fun k => k m) (chartPullbackSectionsIso_unit p j c H M)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.extendRestrictScalarsAdj_unit_app_apply] at h
  change (chartPullbackSectionsIso p j c H M).hom ((1 : S) ⊗ₜ[R,(φ).hom] m) =
    (Nonflat.chartCoefficient p j c (Spec.map φ) H.symm
      ((pullbackPushforwardAdjunction p).unit.app M)).app ⊤ m at h
  exact h

/-- A coordinate unit tensor is the original restricted pullback-unit section,
with no replacement of either chart or the ambient coefficient. -/
theorem chartPullbackCoordinatesIso_inv_one_tmul {N : ModuleCat.{u} R}
    (e : moduleSpecΓFunctor.obj (M.restrict j) ≅ N) (n : N) :
    (chartPullbackCoordinatesIso p j c H M e).inv ((1 : S) ⊗ₜ[R] n) =
      (Nonflat.chartCoefficient p j c (Spec.map φ) H.symm
        ((pullbackPushforwardAdjunction p).unit.app M)).app ⊤ (e.inv n) := by
  exact (ModuleCat.scalarExtensionCoordinatesIso_inv_tmul
    (chartPullbackSectionsIso p j c H M) e 1 n).trans
      (chartPullbackSectionsIso_one_tmul p j c H M (e.inv n))

end AlgebraicGeometry.Scheme.Modules
