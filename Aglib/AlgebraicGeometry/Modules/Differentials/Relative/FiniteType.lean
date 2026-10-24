/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.Affine
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.Restriction
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Actual relative differentials over an affine base are locally finite

The affine coefficient map is literally Spec.preimage of the original
composite. The native relative differential
comparison preserves original d values. Finite type of that composite gives
finite algebraic Kähler differentials and hence the actual affine-local
finite quasicoherent property. This is coherence when the source scheme
is locally Noetherian. No smoothness or perfectness is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme.Modules.Differentials

/-- The original spectrum structure-section algebra, at the scheme section type. -/
local instance relativeFiniteTypeSectionAlgebra (R : CommRingCat.{u}) (U : (Spec R).Opens) :
    Algebra R Γ(Spec R, U) :=
  inferInstanceAs (Algebra R ((AlgebraicGeometry.Spec.structureSheaf R).obj.obj (op U)))

variable {Λ R : CommRingCat.{u}} {X : Scheme.{u}}
  (f : X ⟶ Spec Λ) (j : Spec R ⟶ X) [IsOpenImmersion j]

/-- The actual affine restriction is the Kähler module of the original
coefficient map obtained from the specified composite to the affine base. -/
def relativeDifferentialAffineChartIso :
    (relativeDifferentialSheaf f).restrict j ≅
      tilde (CommRingCat.KaehlerDifferential (Spec.preimage (j ≫ f))) :=
  relativeDifferentialRestrictIso f j ≪≫
    relativeDifferentialCongrIso (j ≫ f) (Spec.map_preimage (j ≫ f)).symm ≪≫
      relativeDifferentialAffineIso (Spec.preimage (j ≫ f))

/-- The original chart comparison retains the original localized differential. -/
theorem relativeDifferentialAffineChartIso_hom_d (r b : R) :
    (relativeDifferentialAffineChartIso f j).hom.val.app (op (PrimeSpectrum.basicOpen r))
        ((relativeDifferentialDerivation f).d
          ((j.appIso (PrimeSpectrum.basicOpen r)).inv
            (@algebraMap R Γ(Spec R, PrimeSpectrum.basicOpen r) _ _
              (relativeFiniteTypeSectionAlgebra R (PrimeSpectrum.basicOpen r)) b))) =
      tilde.toOpen (CommRingCat.KaehlerDifferential (Spec.preimage (j ≫ f)))
        (PrimeSpectrum.basicOpen r) (CommRingCat.KaehlerDifferential.d b) := by
  let σ := Spec.preimage (j ≫ f)
  let U : (Spec R).Opens := PrimeSpectrum.basicOpen r
  let a : Γ(Spec R, U) := algebraMap R Γ(Spec R, U) b
  have hrestrict := (relativeDifferentialRestrictIso_hom_d f j U
    ((j.appIso U).inv a)).trans
      (congrArg (relativeDifferentialDerivation (j ≫ f)).d
        (Iso.inv_hom_id_apply (j.appIso U) a))
  have hcongr := relativeDifferentialCongrIso_hom_d (j ≫ f)
    (Spec.map_preimage (j ≫ f)).symm (op U) a
  exact (congrArg (fun z => (relativeDifferentialAffineIso σ).hom.val.app (op U)
    ((relativeDifferentialCongrIso (j ≫ f)
      (Spec.map_preimage (j ≫ f)).symm).hom.val.app (op U) z)) hrestrict).trans
        ((congrArg ((relativeDifferentialAffineIso σ).hom.val.app (op U)) hcongr).trans
          (relativeDifferentialAffineIso_hom_d σ r b))

/-- Finite type on the original affine scheme map gives finiteness of the
actual ring-theoretic Kähler module with its original coefficient action. -/
theorem finite_kaehler_of_locallyOfFiniteType [LocallyOfFiniteType f] :
    Module.Finite R (CommRingCat.KaehlerDifferential (Spec.preimage (j ≫ f))) := by
  let σ := Spec.preimage (j ≫ f)
  have hσ : LocallyOfFiniteType (Spec.map σ) :=
    (Spec.map_preimage (j ≫ f)).symm ▸
      (inferInstance : LocallyOfFiniteType (j ≫ f))
  have hfinite : RingHom.FiniteType σ.hom :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hσ
  let : Algebra Λ R := σ.hom.toAlgebra
  let : Algebra.FiniteType Λ R := hfinite
  change Module.Finite R (_root_.KaehlerDifferential Λ R)
  infer_instance

/-- The actual relative differential sheaf is affine-locally quasicoherent of
finite type when the original map to the affine base is locally of finite type. -/
theorem relativeDifferentialSheaf_affineLocallyFiniteType [LocallyOfFiniteType f] :
    affineLocallyFiniteType X (relativeDifferentialSheaf f) := by
  intro R j _
  let σ := Spec.preimage (j ≫ f)
  let K : ModuleCat.{u} R := CommRingCat.KaehlerDifferential σ
  let : Module.Finite R K := finite_kaehler_of_locallyOfFiniteType f j
  have htilde : affineFiniteSheaf R (tilde K) := by
    refine ⟨inferInstance, ?_⟩
    let e : K ≃ₗ[R] moduleSpecΓFunctor.obj (tilde K) :=
      (tilde.toTildeΓNatIso.app K).toLinearEquiv
    exact Module.Finite.of_surjective (M := K) e.toLinearMap e.surjective
  exact (affineFiniteSheaf R).prop_of_iso
    (relativeDifferentialAffineChartIso f j).symm htilde

end AlgebraicGeometry.Scheme.Modules.Differentials
