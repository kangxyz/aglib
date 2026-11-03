/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.Cohomology.Restriction
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Trace.SectionsCore

/-! # Original affine trace sections: native qcqs adapter -/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
universe u
namespace AlgebraicGeometry.Scheme.Cohomology.RelativeProjectiveTrace

/-- The native affine higher-image comparison evaluated on the original open unit.
The target morphism is qcqs by the supplied Cartesian square. -/
theorem affineHigherOpenSections_unit
    {R A : Type u} [CommRing R] [CommRing A] {X W : Scheme.{u}}
    (i : W ⟶ X) (q : W ⟶ Spec (.of A)) (p : X ⟶ Spec (.of R))
    [QuasiCompact p] [QuasiSeparated p] (σ : R →+* A)
    [IsOpenImmersion i] [IsOpenImmersion (Spec.map (CommRingCat.ofHom σ))]
    (H : IsPullback i q p (Spec.map (CommRingCat.ofHom σ)))
    (M : X.Modules) [M.IsQuasicoherent] (I : InjectiveResolution M)
    (J : InjectiveResolution ((Modules.restrictFunctor i).obj M)) (n : ℕ)
    (x : (moduleSpecΓFunctor (R := .of R)).obj
      (((Scheme.Modules.pushforward p).rightDerived n).obj M)) :
    let : QuasiCompact q := MorphismProperty.of_isPullback H inferInstance
    let : QuasiSeparated q := MorphismProperty.of_isPullback H inferInstance
    moduleHigherDirectImageAffineSectionsLinearEquiv (R := A) q
        ((Modules.restrictFunctor i).obj M) J n
        (ModuleCat.Hom.hom ((moduleSpecΓFunctor (R := .of A)).map
          (X := (Modules.restrictFunctor (Spec.map (CommRingCat.ofHom σ))).obj
            (((Scheme.Modules.pushforward p).rightDerived n).obj M))
          (Y := ((Scheme.Modules.pushforward q).rightDerived n).obj
            ((Modules.restrictFunctor i).obj M))
          ((Scheme.Modules.higherDirectImageOpenRestrictionIso i q p
            (Spec.map (CommRingCat.ofHom σ)) H n).hom.app M))
          (affineUnitSections (Spec.map (CommRingCat.ofHom σ))
            (((Scheme.Modules.pushforward p).rightDerived n).obj M) x)) =
      moduleCohomologyMapAlong i ((restrictAdjunction i).unit.app M) n
        (moduleHigherDirectImageAffineSectionsLinearEquiv (R := R) p M I n x) := by
  let : QuasiCompact q := MorphismProperty.of_isPullback H inferInstance
  let : QuasiSeparated q := MorphismProperty.of_isPullback H inferInstance
  let := moduleResolutionPushforwardTildeCounit_quasiIso p M I
  let := moduleResolutionPushforwardTildeCounit_quasiIso q
    ((Modules.restrictFunctor i).obj M) J
  exact affineHigherOpenSections_unit_of_counit_quasiIso i q p σ H M I J n x

end AlgebraicGeometry.Scheme.Cohomology.RelativeProjectiveTrace
