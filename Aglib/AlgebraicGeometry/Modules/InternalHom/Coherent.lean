/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.InternalHom.AffineIterated
public import Aglib.AlgebraicGeometry.Modules.Coherent.FinitePresentation
public import Aglib.RingTheory.Localization.HomEvaluation

/-!
# Coherence of the actual internal Hom

On an affine chart, original Hom sections are linear maps between the original
section modules. Their restriction map is localization when the source is
finitely presented. This proves quasicoherence, not merely finite generation
of individual stalks. Over a locally Noetherian scheme, coherent source and
target therefore give a coherent actual internal-Hom sheaf.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite AlgebraicGeometry
open scoped ModuleCat.Algebra
universe u
namespace AlgebraicGeometry.Scheme.Modules.InternalHom
open QuasiCoherent

/-- Finite presentation of source sections on an affine chart makes the
actual restricted internal Hom quasicoherent there. No Noetherian hypothesis
is needed for this localization statement. -/
theorem quasicoherent_affineRestriction {X : Scheme.{u}} {R : CommRingCat.{u}}
    (j : Spec R ⟶ X) [IsOpenImmersion j] (M N : X.Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent]
    [Module.FinitePresentation R (moduleSpecΓFunctor.obj (M.restrict j))] :
    ((show X.Modules from sheaf X M N).restrict j).IsQuasicoherent := by
  let H : (Spec R).Modules := (show X.Modules from sheaf X M N).restrict j
  rw [isQuasicoherent_iff_isIso_fromTildeΓ, isIso_fromTildeΓ_iff_isLocalizing]
  intro r
  let := toPrincipalGlobalSections_isLocalized R r (M.restrict j)
  let := toPrincipalGlobalSections_isLocalized R r (N.restrict j)
  have hlocal : IsLocalizedModule (.powers r) (toPrincipalGlobalSections R r H) :=
    IsLocalizedModule.of_homEvaluation (.powers r)
      (toPrincipalGlobalSections R r (M.restrict j))
      (toPrincipalGlobalSections R r (N.restrict j)) (Localization.Away r)
      (toPrincipalGlobalSections R r H) (affineRestrictionSectionsEquiv j M N)
      (iteratedAffineRestrictionSectionsEquiv j (principalOpen R r) M N)
      (affineRestrictionSectionsEquiv_principal j r M N)
  have hres : IsLocalizedModule (.powers r)
      ((modulesSpecToSheaf.obj H).presheaf.map
        (principalOpen R r ''ᵁ ⊤).leTop.op).hom :=
    (IsLocalizedModule.comp_iff_of_bijective_left (.powers r)
      (principalGlobalSectionsEquiv R r H).symm.toLinearMap
      (principalGlobalSectionsEquiv R r H).symm.bijective).mp hlocal
  have he : principalOpen R r ''ᵁ ⊤ = PrimeSpectrum.basicOpen r := by
    rw [Scheme.Hom.image_top_eq_opensRange]
    exact Scheme.Hom.opensRange_localizationAway r
  rw [he] at hres
  exact hres

/-- The actual internal Hom of coherent modules is coherent on a locally
Noetherian scheme. The conclusion is the original affine-chart predicate,
not a substituted Hom model or an assumed coherence certificate. -/
theorem affineLocallyFiniteType_internalHom {X : Scheme.{u}} [IsLocallyNoetherian X]
    (M N : X.Modules) (hM : affineLocallyFiniteType X M)
    (hN : affineLocallyFiniteType X N) : affineLocallyFiniteType X (sheaf X M N) := by
  let : M.IsFinitePresentation := affineLocallyFiniteType_finitePresentation hM
  let : N.IsFinitePresentation := affineLocallyFiniteType_finitePresentation hN
  intro R j _
  let : IsNoetherianRing R := Coherent.noetherian_affineChart R j
  let : Module.Finite R (moduleSpecΓFunctor.obj (M.restrict j)) := (hM R j).2
  let : Module.Finite R (moduleSpecΓFunctor.obj (N.restrict j)) := (hN R j).2
  let : Module.FinitePresentation R (moduleSpecΓFunctor.obj (M.restrict j)) :=
    Module.finitePresentation_of_finite R _
  refine ⟨quasicoherent_affineRestriction j M N, ?_⟩
  exact Module.Finite.of_surjective (affineRestrictionSectionsEquiv j M N).symm.toLinearMap
    (affineRestrictionSectionsEquiv j M N).symm.surjective

end AlgebraicGeometry.Scheme.Modules.InternalHom
