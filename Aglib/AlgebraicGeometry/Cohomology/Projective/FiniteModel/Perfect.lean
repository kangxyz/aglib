/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.FiniteModel.Sheaf
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.Resolution

/-!
# Actual strict perfect direct images for projective embeddings

The actual qcqs affine counit theorem discharges the original counit condition.
The same constructed strict sheaf complex therefore represents the installed
native derived direct image. Over a Noetherian base the coherent relatively
flat coefficient supplies the finite-projective model, so the strict direct-
image representative is constructed without a comparison-family premise.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules.QuasiCoherent

namespace AlgebraicGeometry.Scheme.Cohomology

namespace ProjectiveCohomologyModel

theorem embeddingCounit_quasiIso {R : CommRingCat.{u}} {ι : Type u} {X : Scheme.{u}}
    (i : X ⟶ ProjectiveSpace R ι) [IsClosedImmersion i] (f : X ⟶ Spec R)
    {n : ℕ} (e : ι ≃ Fin (n + 1)) (M : X.Modules) [M.IsQuasicoherent]
    (I : InjectiveResolution M) :
    QuasiIso (Scheme.Modules.Complex.tildeGlobalSectionsCounit R (.up ℤ)
      (((Scheme.Modules.pushforward f).mapCochainComplexPlus.obj I.cochainComplexPlus).obj)) := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (i ≫ toSpec R ι)
  let : QuasiCompact f := (quasiCompact_iff_compactSpace f).mpr inferInstance
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from i]; infer_instance⟩
  let : QuasiSeparated f := inferInstance
  exact moduleResolutionPushforwardTildeCounit_quasiIso f M I

variable {R : CommRingCat.{u}} {ι : Type u} {X : Scheme.{u}}
  {i : X ⟶ ProjectiveSpace R ι} [IsClosedImmersion i]
  {f : X ⟶ Spec R} {M : X.Modules} [M.IsQuasicoherent] {n : ℕ}
  (D : ProjectiveCohomologyModel R ι i f M n) (e : ι ≃ Fin (n + 1))
  (I : InjectiveResolution M)

/-- The original actual strict-model arrow to the pushed injective
resolution is a quasi-isomorphism, with its geometric counit condition proved. -/
theorem sheafComparison_quasiIso : QuasiIso (D.sheafComparison e I) :=
  D.sheafComparison_quasiIso_of_counit e I (embeddingCounit_quasiIso i f e M I)

include D e in
/-- The original pushed resolution has an actual global strict-perfect
representative, with no supplied quasi-isomorphism condition. -/
theorem hasStrictSheafModel : Scheme.Modules.Complex.HasStrictModel
    (((Scheme.Modules.pushforward f).mapCochainComplexPlus.obj I.cochainComplexPlus).obj) :=
  D.hasStrictSheafModel_of_counit e I (embeddingCounit_quasiIso i f e M I)

local instance perfectModelDerivedSource : HasDerivedCategory.{u + 1} X.Modules :=
  HasDerivedCategory.standard _

local instance perfectModelDerivedTarget : HasDerivedCategory.{u + 1} (Spec R).Modules :=
  HasDerivedCategory.standard _

/-- The constructed original strict sheaf complex represents the
installed native derived direct image of the original coefficient. -/
def derivedPushforwardIso :
    DerivedCategory.Plus.Q.obj D.strictSheafModelPlus ≅
      (Scheme.Modules.pushforward f).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M) :=
  D.derivedPushforwardIso_of_counit e I (embeddingCounit_quasiIso i f e M I)

/-- The actual direct-image model retains the literal original sheaf
comparison and the original injective-resolution derived unit. -/
theorem derivedPushforwardIso_hom :
    (D.derivedPushforwardIso e I).hom =
      DerivedCategory.Plus.Q.map (D.sheafComparisonPlus e I) ≫
        (InjectiveResolution.rightDerivedFunctorPlusIso (Scheme.Modules.pushforward f) I).hom := rfl

end ProjectiveCohomologyModel

/-- An actual projective embedding over a Noetherian base, coherent
coefficient and relative flatness construct a strict perfect representative
of the installed actual `Rf_*`, with the original term bounds `[0,n]`. -/
theorem exists_strictPerfect_derivedPushforward_of_projectiveEmbedding
    (R : CommRingCat.{u}) [IsNoetherianRing R] (ι : Type u) {X : Scheme.{u}}
    (i : X ⟶ ProjectiveSpace R ι) [IsClosedImmersion i] (f : X ⟶ Spec R)
    (M : X.Modules) (n : ℕ) (e : ι ≃ Fin (n + 1)) (hf : i ≫ toSpec R ι = f)
    (hM : affineLocallyFiniteType X M) (hflat : Scheme.Modules.relativeFlat f M) :
    letI : HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _
    letI : HasDerivedCategory.{u + 1} (Spec R).Modules := HasDerivedCategory.standard _
    ∃ P : CochainComplex.Plus (Spec R).Modules,
      P.obj.IsStrictlyGE 0 ∧ P.obj.IsStrictlyLE (n : ℤ) ∧
        Scheme.Modules.Complex.strictPerfect (Spec R) P.obj ∧
          Nonempty (DerivedCategory.Plus.Q.obj P ≅
            (Scheme.Modules.pushforward f).rightDerivedFunctorPlus.obj
              ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)) := by
  let : M.IsQuasicoherent :=
    quasicoherent_of_affineCharts M (fun A j _ => (hM A j).1)
  let D := projectiveCohomologyModelOfEmbedding R ι i f M n e hf hM hflat
  let := D.lowerBound
  let := D.upperBound
  refine ⟨D.strictSheafModelPlus, ?_, ?_, D.strictSheafModel.property,
    ⟨D.derivedPushforwardIso e (injectiveResolution M)⟩⟩
  · change CochainComplex.IsStrictlyGE
      (((tilde.functor R).mapHomologicalComplex (.up ℤ)).obj D.complex) 0
    infer_instance
  · change CochainComplex.IsStrictlyLE
      (((tilde.functor R).mapHomologicalComplex (.up ℤ)).obj D.complex) (n : ℤ)
    infer_instance

end AlgebraicGeometry.Scheme.Cohomology
