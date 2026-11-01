/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.Semilinear.KernelRepresentation.Restricted
public import Aglib.RingTheory.Etale.FrobeniusKernel.GenericFinite
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.CoefficientRepresentation
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.FiniteTrivialization
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.GaloisInstances

/-!
# Generic finite local constancy of the original semilinear kernel

The algebraic generic-freeness construction supplies a genuine principal
localization and a finite etale algebra. Its natural Hom equivalence represents
the restriction of the original categorical kernel. The additive structure is
transported onto that same finite etale scheme; no second representative or
localized semilinear module is selected.
-/

@[expose] public noncomputable section

universe u

open scoped TensorProduct

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

/-- A finite quasicoherent module over a Noetherian domain has a semilinear
fixed kernel represented by an actual finite etale scheme after a nonzero
principal localization. The literal restriction of the original additive
kernel is finite locally constant. -/
theorem exists_finite_etale_restrictedKernel_and_free
    (A : CommRingCat.{u}) [IsDomain A] [IsNoetherianRing A]
    (F : (Spec A).Modules) [F.IsQuasicoherent]
    [Module.Finite A (moduleSpecΓFunctor.obj F)]
    (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0)
    (Φ : moduleSpecΓFunctor.obj F →ₛₗ[RingHom.frobeniusOfPrimeCastEqZero p hp hA]
      moduleSpecΓFunctor.obj F) :
    ∃ (r : A), r ≠ 0 ∧
      ∃ (R : Type u) (_ : CommRing R) (_ : Algebra A R) (_ : IsLocalization.Away r R)
        (_ : Etale (Spec.map (CommRingCat.ofHom (algebraMap A R))))
        (C : Type u) (_ : CommRing C) (_ : Algebra R C)
        (_ : Module.Finite R C) (_ : Algebra.Etale R C),
        Module.Free R (R ⊗[A] moduleSpecΓFunctor.obj F) ∧
        Nonempty (finiteRepresentedSetSheaf (Scheme.FiniteEtale.AffineDescent.specCover R C) ≅
          underlyingSetSheaf
            ((etaleRestriction (Spec.map (CommRingCat.ofHom (algebraMap A R)))).obj
              (kernel (affineFrobenius A F p hp hA Φ -
                𝟙 (additiveCoefficient (Spec A) F))))) ∧
        IsFiniteLocallyConstant
          ((etaleRestriction (Spec.map (CommRingCat.ofHom (algebraMap A R)))).obj
            (kernel (affineFrobenius A F p hp hA Φ -
              𝟙 (additiveCoefficient (Spec A) F)))) := by
  obtain ⟨r, hr, R, hR, hAR, hloc, C, hC, hRC, hfree, hfinite, hetale, e, he⟩ :=
    Algebra.FrobeniusKernel.exists_finite_etale_fixedRepresentative_and_free.{u, u, u} p hp hA Φ
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A R))) :=
    IsOpenImmersion.of_isLocalization r
  let : IsDomain R := IsLocalization.Away.isDomain (S := R) hr
  let : ConnectedSpace (Spec (CommRingCat.of R)) :=
    inferInstanceAs (ConnectedSpace (PrimeSpectrum R))
  let L := (etaleRestriction (Spec.map (CommRingCat.ofHom (algebraMap A R)))).obj
    (kernel (affineFrobenius A F p hp hA Φ - 𝟙 (additiveCoefficient (Spec A) F)))
  let Y := Scheme.FiniteEtale.AffineDescent.specCover R C
  let ei := restrictedKernelSheafIso A F p hp hA Φ R C e he
  let H := CoefficientRepresentation.groupScheme L Y ei
  let s := Scheme.FiniteEtale.algebraicClosureResiduePoint (Spec (CommRingCat.of R))
    (Classical.choice (inferInstance : Nonempty (Spec (CommRingCat.of R))))
  refine ⟨r, hr, R, hR, hAR, hloc, inferInstance, C, hC, hRC, hfinite, hetale,
    hfree, ⟨ei⟩, ?_⟩
  exact (isFiniteLocallyConstant_iff_of_iso
    (CoefficientRepresentation.sheafIso L Y ei)).mp
      (representedSheaf_isFiniteLocallyConstant (s := s) H)

/-- The original generic kernel endpoint forgets only the retained freeness
witness, without changing its localization or finite etale representative. -/
theorem exists_finite_etale_restrictedKernel
    (A : CommRingCat.{u}) [IsDomain A] [IsNoetherianRing A]
    (F : (Spec A).Modules) [F.IsQuasicoherent]
    [Module.Finite A (moduleSpecΓFunctor.obj F)]
    (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0)
    (Φ : moduleSpecΓFunctor.obj F →ₛₗ[RingHom.frobeniusOfPrimeCastEqZero p hp hA]
      moduleSpecΓFunctor.obj F) :
    ∃ (r : A), r ≠ 0 ∧
      ∃ (R : Type u) (_ : CommRing R) (_ : Algebra A R) (_ : IsLocalization.Away r R)
        (_ : Etale (Spec.map (CommRingCat.ofHom (algebraMap A R))))
        (C : Type u) (_ : CommRing C) (_ : Algebra R C)
        (_ : Module.Finite R C) (_ : Algebra.Etale R C),
        Nonempty (finiteRepresentedSetSheaf (Scheme.FiniteEtale.AffineDescent.specCover R C) ≅
          underlyingSetSheaf
            ((etaleRestriction (Spec.map (CommRingCat.ofHom (algebraMap A R)))).obj
              (kernel (affineFrobenius A F p hp hA Φ -
                𝟙 (additiveCoefficient (Spec A) F))))) ∧
        IsFiniteLocallyConstant
          ((etaleRestriction (Spec.map (CommRingCat.ofHom (algebraMap A R)))).obj
            (kernel (affineFrobenius A F p hp hA Φ -
              𝟙 (additiveCoefficient (Spec A) F)))) := by
  obtain ⟨r, hr, R, hR, hAR, hloc, hEt, C, hC, hRC, hfinite, hetale, _, ei, hL⟩ :=
    exists_finite_etale_restrictedKernel_and_free A F p hp hA Φ
  exact ⟨r, hr, R, hR, hAR, hloc, hEt, C, hC, hRC, hfinite, hetale, ei, hL⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
