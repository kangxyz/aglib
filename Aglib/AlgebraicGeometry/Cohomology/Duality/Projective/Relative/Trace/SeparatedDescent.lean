/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Trace.SeparatedSections
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.SeparatedNaturality
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Trace.DescentCore

/-!
# Affine descent of cohomologically normalized trace arrows

The entire ordinary trace square is proved before choosing a projective
model or a coefficient functor. The only trace inputs are their original
affine section formulas and the original open cohomology equation. The
coefficient map remains the supplied native restriction adjunct.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u
namespace AlgebraicGeometry.Scheme.Cohomology.RelativeProjectiveTrace

section
variable {R A : Type u} [CommRing R] [CommRing A]
  {X W : Scheme.{u}} (i : W ⟶ X) (q : W ⟶ Spec (.of A)) (p : X ⟶ Spec (.of R))
  (σ : R →+* A) [QuasiCompact p] [IsSeparated p]
  [QuasiCompact q] [IsSeparated q]
  [IsOpenImmersion i] [IsOpenImmersion (Spec.map (CommRingCat.ofHom σ))]
  (H : IsPullback i q p (Spec.map (CommRingCat.ofHom σ)))

/-- Original section normalizations and the original cohomological open
trace imply the full native sheaf trace square. No particular coefficient
functor or projective model occurs in the proof. -/
theorem affineTraceRestriction_of_sections_of_isSeparated
    (M : X.Modules) [M.IsQuasicoherent] (M' : W.Modules) [M'.IsQuasicoherent]
    (N : (Spec (.of R)).Modules) (n : ℕ)
    (C : (Modules.restrictFunctor i).obj M ⟶ M')
    (β : M ⟶ (Scheme.Modules.pushforward i).obj M')
    (hβ : β = (restrictAdjunction i).homEquiv M M' C)
    (tR : ((Scheme.Modules.pushforward p).rightDerived n).obj M ⟶ N)
    (tA : ((Scheme.Modules.pushforward q).rightDerived n).obj M' ⟶
      (Modules.restrictFunctor (Spec.map (CommRingCat.ofHom σ))).obj N)
    (τR : Sheaf.H.{u + 1} (moduleAddSheaf X M) n → moduleSpecΓFunctor.obj N)
    (τA : Sheaf.H.{u + 1} (moduleAddSheaf W M') n →
      moduleSpecΓFunctor.obj
        ((Modules.restrictFunctor (Spec.map (CommRingCat.ofHom σ))).obj N))
    (htR : ∀ x,
      moduleSpecΓFunctor.map tR x =
        τR (moduleHigherDirectImageAffineSectionsLinearEquiv_of_isSeparated
          p M (injectiveResolution M) n x))
    (htA : ∀ y,
      moduleSpecΓFunctor.map tA y =
        τA (moduleHigherDirectImageAffineSectionsLinearEquiv_of_isSeparated
          q M' (injectiveResolution M') n y))
    (hopen : ∀ c,
      τA (moduleCohomologyMapAlong i β n c) =
        affineUnitSections (Spec.map (CommRingCat.ofHom σ)) N (τR c)) :
    (Scheme.Modules.higherDirectImageOpenRestrictionIso i q p
        (Spec.map (CommRingCat.ofHom σ)) H n).hom.app M ≫
      ((Scheme.Modules.pushforward q).rightDerived n).map C ≫ tA =
      (Modules.restrictFunctor (Spec.map (CommRingCat.ofHom σ))).map tR := by
  let := moduleResolutionPushforwardTildeCounit_quasiIso_of_isSeparated p M (injectiveResolution M)
  let := moduleResolutionPushforwardTildeCounit_quasiIso_of_isSeparated
    q M' (injectiveResolution M')
  let := moduleResolutionPushforwardTildeCounit_quasiIso_of_isSeparated q
    ((Modules.restrictFunctor i).obj M) (injectiveResolution _)
  exact affineTraceRestriction_of_sections_of_counit_quasiIso i q p σ H M M' N n C β hβ
    tR tA τR τA htR htA hopen

end
end AlgebraicGeometry.Scheme.Cohomology.RelativeProjectiveTrace
