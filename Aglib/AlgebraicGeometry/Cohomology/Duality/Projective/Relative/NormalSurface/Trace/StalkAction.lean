/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.NormalSurface.CanonicalStalk
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Coinduction.SourceAction

/-!
# Original canonical stalks and the actual quotient action

The original ambient-linear stalk map is quotient-linear for the native
Yoneda/coinduction action. Surjectivity of the actual closed-immersion stalk
map proves this without changing its additive map. Original global stalks
are transported through the original open-restriction stalk isomorphism.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

local instance canonicalStalkActionDerived (B : Type u) [CommRing B] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} B) := HasDerivedCategory.standard _

variable (R : Type u) [CommRing R] [IsNoetherianRing R] (ι : Type u)
    {X : Scheme.{u}} (i : X ⟶ ProjectiveSpace R ι) [IsClosedImmersion i]
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    (A : CommRingCat.{u}) [IsNoetherianRing A]
    (j : Spec A ⟶ ProjectiveSpace R ι) [IsOpenImmersion j]
    (C : ClosedImmersionAffineQuotientChart i A j)
    (z : PrimeSpectrum (A ⧸ C.ideal))

/-- The unchanged quotient-chart canonical stalk equivalence is linear over
the actual source stalk ring for the original source action on Ext. -/
def normalSurfaceCanonicalQuotientStalkSourceLinearEquiv :
    let q := (FiniteSourceStalk.stalkMap C.ideal z).hom
    let N := (moduleStalk (Spec A) (FiniteSourceStalk.imagePoint C.ideal z)).obj
      ((Scheme.Modules.restrictFunctor j).obj (normalSurfaceAmbientCoefficient R ι n))
    letI := ModuleCat.coinducedExtSourceModule q N n
    (moduleStalk (Spec (.of (A ⧸ C.ideal))) z).obj
        ((Scheme.Modules.restrictFunctor C.sourceMap).obj
          (normalSurfaceCanonicalModule R ι i n)) ≃ₗ[FiniteSourceStalk.sourceRing C.ideal z]
      Ext.{u} ((ModuleCat.restrictScalars q).obj
        (ModuleCat.of (FiniteSourceStalk.sourceRing C.ideal z)
          (FiniteSourceStalk.sourceRing C.ideal z))) N n := by
  let q := (FiniteSourceStalk.stalkMap C.ideal z).hom
  let N := (moduleStalk (Spec A) (FiniteSourceStalk.imagePoint C.ideal z)).obj
    ((Scheme.Modules.restrictFunctor j).obj (normalSurfaceAmbientCoefficient R ι n))
  letI := ModuleCat.coinducedExtSourceModule q N n
  let E := normalSurfaceCanonicalQuotientStalkExtLinearEquiv R ι i n e A j C z
  have hq : Function.Surjective q :=
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk C.ideal))).stalkMap_surjective z
  refine { __ := E.toAddEquiv, map_smul' := ?_ }
  intro b x
  obtain ⟨r, rfl⟩ := hq b
  change E (q r • x) = q r • E x
  erw [ModuleCat.coinducedExtSourceModule_map_smul]
  exact E.map_smul r x

/-- The source-linear upgrade retains the original ambient-linear map as an
additive equivalence, rather than selecting a different stalk identification. -/
theorem normalSurfaceCanonicalQuotientStalkSourceLinearEquiv_toAddEquiv :
    let q := (FiniteSourceStalk.stalkMap C.ideal z).hom
    let N := (moduleStalk (Spec A) (FiniteSourceStalk.imagePoint C.ideal z)).obj
      ((Scheme.Modules.restrictFunctor j).obj (normalSurfaceAmbientCoefficient R ι n))
    letI := ModuleCat.coinducedExtSourceModule q N n
    (normalSurfaceCanonicalQuotientStalkSourceLinearEquiv R ι i n e A j C z).toAddEquiv =
      (normalSurfaceCanonicalQuotientStalkExtLinearEquiv R ι i n e A j C z).toAddEquiv := rfl

/-- The original global canonical stalk is linear over its own original local
ring. The target action is restricted along the actual open-stalk ring map. -/
def normalSurfaceCanonicalOriginalStalkSourceLinearEquiv :
    let q := (FiniteSourceStalk.stalkMap C.ideal z).hom
    let N := (moduleStalk (Spec A) (FiniteSourceStalk.imagePoint C.ideal z)).obj
      ((Scheme.Modules.restrictFunctor j).obj (normalSurfaceAmbientCoefficient R ι n))
    letI := ModuleCat.coinducedExtSourceModule q N n
    (moduleStalk X (C.sourceMap z)).obj (normalSurfaceCanonicalModule R ι i n) ≃ₗ[
      X.presheaf.stalk (C.sourceMap z)]
      (ModuleCat.restrictScalars (C.sourceMap.stalkMap z).hom).obj
        (ModuleCat.of (FiniteSourceStalk.sourceRing C.ideal z)
          (Ext.{u} ((ModuleCat.restrictScalars q).obj
            (ModuleCat.of (FiniteSourceStalk.sourceRing C.ideal z)
              (FiniteSourceStalk.sourceRing C.ideal z))) N n)) := by
  let : IsOpenImmersion C.sourceMap := C.isOpenImmersion
  let q := (FiniteSourceStalk.stalkMap C.ideal z).hom
  let N := (moduleStalk (Spec A) (FiniteSourceStalk.imagePoint C.ideal z)).obj
    ((Scheme.Modules.restrictFunctor j).obj (normalSurfaceAmbientCoefficient R ι n))
  letI := ModuleCat.coinducedExtSourceModule q N n
  let E := normalSurfaceCanonicalQuotientStalkSourceLinearEquiv R ι i n e A j C z
  let U := (restrictModuleStalkIso C.sourceMap z).app (normalSurfaceCanonicalModule R ι i n)
  exact U.symm.toLinearEquiv.trans
    ((ModuleCat.restrictScalars (C.sourceMap.stalkMap z).hom).mapIso E.toModuleIso).toLinearEquiv

/-- The original canonical stalk is the actual derived-coinduction homology,
with its original local source action transported only by the open-stalk map.
This is derived coinduction, not an ordinary-coextension exactness assertion. -/
def normalSurfaceCanonicalOriginalStalkCoinductionLinearEquiv :
    let q := (FiniteSourceStalk.stalkMap C.ideal z).hom
    let N := (moduleStalk (Spec A) (FiniteSourceStalk.imagePoint C.ideal z)).obj
      ((Scheme.Modules.restrictFunctor j).obj (normalSurfaceAmbientCoefficient R ι n))
    (moduleStalk X (C.sourceMap z)).obj (normalSurfaceCanonicalModule R ι i n) ≃ₗ[
      X.presheaf.stalk (C.sourceMap z)]
      (ModuleCat.restrictScalars (C.sourceMap.stalkMap z).hom).obj
        ((DerivedCategory.Plus.homologyFunctor
          (ModuleCat.{u} (FiniteSourceStalk.sourceRing C.ideal z)) (n : ℤ)).obj
          ((ModuleCat.coextendScalars q).rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.singleFunctor
              (ModuleCat.{u} (FiniteSourceStalk.ambientRing C.ideal z)) 0).obj N))) := by
  let q := (FiniteSourceStalk.stalkMap C.ideal z).hom
  let N := (moduleStalk (Spec A) (FiniteSourceStalk.imagePoint C.ideal z)).obj
    ((Scheme.Modules.restrictFunctor j).obj (normalSurfaceAmbientCoefficient R ι n))
  letI := ModuleCat.coinducedExtSourceModule q N n
  let E := normalSurfaceCanonicalOriginalStalkSourceLinearEquiv R ι i n e A j C z
  let D := ModuleCat.derivedCoextendScalarsPlusHomologyExtSourceLinearEquiv q N n
    (injectiveResolution N)
  exact E.trans
    ((ModuleCat.restrictScalars (C.sourceMap.stalkMap z).hom).mapIso
      D.symm.toModuleIso).toLinearEquiv

end AlgebraicGeometry.Scheme.Cohomology
