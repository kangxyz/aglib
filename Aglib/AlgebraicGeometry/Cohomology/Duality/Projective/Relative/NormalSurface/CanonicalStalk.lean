/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.NormalSurface
public import Aglib.AlgebraicGeometry.Modules.Flat.Locality

/-!
# Original canonical stalks and ambient Ext

The original open and quotient stalk maps identify the own-homology canonical
stalk with ambient Ext in the actual embedding degree. These comparisons are
independent of ordinary direct-image localization. Dimension normalization
uses the varying local source dimension, not a uniform surface dimension.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent Opposite

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] ClosedImmersionAffineQuotientChart.isOpenImmersion

/-- On an actual affine quotient chart, the localized global canonical object is
ambient-stalk Ext in the embedding degree. The original ambient coefficient is
retained. The finite map here is the quotient chart, not the initial base map. -/
def normalSurfaceCanonicalQuotientStalkExtLinearEquiv
    (R : Type u) [CommRing R] [IsNoetherianRing R] (ι : Type u)
    {X : Scheme.{u}} (i : X ⟶ ProjectiveSpace R ι) [IsClosedImmersion i]
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    (A : CommRingCat.{u}) [IsNoetherianRing A]
    (j : Spec A ⟶ ProjectiveSpace R ι) [IsOpenImmersion j]
    (C : ClosedImmersionAffineQuotientChart i A j)
    (z : PrimeSpectrum (A ⧸ C.ideal)) :
    (ModuleCat.restrictScalars (FiniteSourceStalk.stalkMap C.ideal z).hom).obj
      ((moduleStalk (Spec (.of (A ⧸ C.ideal))) z).obj
        ((Scheme.Modules.restrictFunctor C.sourceMap).obj
          (normalSurfaceCanonicalModule R ι i n))) ≃ₗ[
      FiniteSourceStalk.ambientRing C.ideal z]
      Ext.{u}
        ((ModuleCat.restrictScalars (FiniteSourceStalk.stalkMap C.ideal z).hom).obj
          (ModuleCat.of (FiniteSourceStalk.sourceRing C.ideal z)
            (FiniteSourceStalk.sourceRing C.ideal z)))
        ((moduleStalk (Spec A) (FiniteSourceStalk.imagePoint C.ideal z)).obj
          ((Scheme.Modules.restrictFunctor j).obj (normalSurfaceAmbientCoefficient R ι n))) n := by
  let : Finite ι := Finite.of_equiv _ e.symm
  have := normalSurfaceAmbientCoefficient_finitePresentation R ι n e
  let L := (normalSurfaceAmbientCoefficient R ι n).restrict j
  have : L.IsFinitePresentation := finitePresentation_restrict j _
  let J := injectiveResolution L
  let E := (moduleStalk (Spec (.of (A ⧸ C.ideal))) z).mapIso
    (derivedClosedImmersionRightAdjointOpenHomologyIso C.sourceMap
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk C.ideal))) i j C.square
      (normalSurfaceAmbientCoefficient R ι n) (n : ℤ))
  let eR := (ModuleCat.restrictScalars (FiniteSourceStalk.stalkMap C.ideal z).hom).mapIso E
  exact eR.toLinearEquiv.trans
    (derivedClosedImmersionRightAdjointQuotientStalkExtLinearEquiv C.ideal J z n)

/-- The original global canonical stalk itself, with its ambient action transported
only through the actual open-stalk ring isomorphism, is the same ambient Ext.
No finiteness of the original regular base map to this stalk is assumed. -/
def normalSurfaceCanonicalOriginalStalkExtLinearEquiv
    (R : Type u) [CommRing R] [IsNoetherianRing R] (ι : Type u)
    {X : Scheme.{u}} (i : X ⟶ ProjectiveSpace R ι) [IsClosedImmersion i]
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    (A : CommRingCat.{u}) [IsNoetherianRing A]
    (j : Spec A ⟶ ProjectiveSpace R ι) [IsOpenImmersion j]
    (C : ClosedImmersionAffineQuotientChart i A j)
    (z : PrimeSpectrum (A ⧸ C.ideal)) :
    letI : IsOpenImmersion C.sourceMap := C.isOpenImmersion
    letI : IsIso (C.sourceMap.stalkMap z) :=
      (IsOpenImmersion.iff_isIso_stalkMap.mp C.isOpenImmersion).2 z
    let σ := (asIso (C.sourceMap.stalkMap z)).inv.hom.comp
      (FiniteSourceStalk.stalkMap C.ideal z).hom
    (ModuleCat.restrictScalars σ).obj
      ((moduleStalk X (C.sourceMap z)).obj (normalSurfaceCanonicalModule R ι i n)) ≃ₗ[
      FiniteSourceStalk.ambientRing C.ideal z]
      Ext.{u}
        ((ModuleCat.restrictScalars (FiniteSourceStalk.stalkMap C.ideal z).hom).obj
          (ModuleCat.of (FiniteSourceStalk.sourceRing C.ideal z)
            (FiniteSourceStalk.sourceRing C.ideal z)))
        ((moduleStalk (Spec A) (FiniteSourceStalk.imagePoint C.ideal z)).obj
          ((Scheme.Modules.restrictFunctor j).obj (normalSurfaceAmbientCoefficient R ι n))) n := by
  let : IsOpenImmersion C.sourceMap := C.isOpenImmersion
  let : IsIso (C.sourceMap.stalkMap z) :=
    (IsOpenImmersion.iff_isIso_stalkMap.mp C.isOpenImmersion).2 z
  let q := (FiniteSourceStalk.stalkMap C.ideal z).hom
  let eB := asIso (C.sourceMap.stalkMap z)
  let σ := eB.inv.hom.comp q
  let ω := normalSurfaceCanonicalModule R ι i n
  let T := (moduleStalk (Spec (.of (A ⧸ C.ideal))) z).obj
    ((Scheme.Modules.restrictFunctor C.sourceMap).obj ω)
  let E := (restrictModuleStalkIso C.sourceMap z).app ω
  have hσ : q = (C.sourceMap.stalkMap z).hom.comp σ := by
    ext r
    exact (eB.commRingCatIsoToRingEquiv.apply_symm_apply (q r)).symm
  let eR := (ModuleCat.restrictScalars σ).mapIso E.symm ≪≫
    ((ModuleCat.restrictScalarsComp' σ (C.sourceMap.stalkMap z).hom q hσ).app T).symm
  exact eR.toLinearEquiv.trans
    (normalSurfaceCanonicalQuotientStalkExtLinearEquiv R ι i n e A j C z)

/-- The actual quotient-chart ambient dimension is the embedding Ext degree
plus the actual local source dimension. Thus normalization uses the varying
local source dimension, not the constant surface dimension at every point. -/
theorem normalSurfaceCanonicalQuotientStalk_dimension
    (R : Type u) [CommRing R] [IsDomain R] [IsRegularLocalRing R] (ι : Type u)
    {X : Scheme.{u}} [IsIntegral X]
    (i : X ⟶ ProjectiveSpace R ι) [IsClosedImmersion i]
    [IsDominant (i ≫ toSpec R ι)]
    (hX : NormalStalks X) (hXdim : topologicalKrullDim X ≤ 2)
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    (hfin : (genericImageBaseMap R ι i).Finite)
    (A : CommRingCat.{u}) (j : Spec A ⟶ ProjectiveSpace R ι) [IsOpenImmersion j]
    (C : ClosedImmersionAffineQuotientChart i A j)
    (z : PrimeSpectrum (A ⧸ C.ideal)) :
    ringKrullDim (FiniteSourceStalk.ambientRing C.ideal z) =
      (n : ℕ) + ringKrullDim (FiniteSourceStalk.sourceRing C.ideal z) := by
  let : IsOpenImmersion C.sourceMap := C.isOpenImmersion
  let : IsIso (C.sourceMap.stalkMap z) :=
    (IsOpenImmersion.iff_isIso_stalkMap.mp C.isOpenImmersion).2 z
  let y := FiniteSourceStalk.imagePoint C.ideal z
  let eS := (asIso (j.stalkMap y)).commRingCatIsoToRingEquiv
  let eB := (asIso (C.sourceMap.stalkMap z)).commRingCatIsoToRingEquiv
  have he : j y = i (C.sourceMap z) :=
    congrArg (fun k : Spec (.of (A ⧸ C.ideal)) ⟶ ProjectiveSpace R ι => k z) C.square.w.symm
  calc
    _ = ringKrullDim ((ProjectiveSpace R ι).presheaf.stalk (j y)) :=
      (ringKrullDim_eq_of_ringEquiv eS).symm
    _ = (n : ℕ) + ringKrullDim (X.presheaf.stalk (C.sourceMap z)) := by
      rw [he]
      exact normalSurface_stalk_dimension R ι i hX hXdim n e hfin (C.sourceMap z)
    _ = _ := congrArg (fun d : WithBot ℕ∞ => (n : WithBot ℕ∞) + d) (ringKrullDim_eq_of_ringEquiv eB)

end AlgebraicGeometry.Scheme.Cohomology
