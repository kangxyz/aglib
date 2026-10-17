/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.FiniteModel.BaseChangeResolution
public import Aglib.AlgebraicGeometry.Cohomology.Projective.FiniteModel.Perfect

/-!
# The same model gives actual perfect direct images after every base change

Native tilde of the literal scalar extension of the same finite-projective
complex represents installed derived direct image of the ordinary pulled
coefficient on the actual fibre product. The actual qcqs counit theorem
discharges the counit condition over the arbitrary new ring. No Noetherianity
or flatness of that new ring is assumed, and no derived coefficient-pullback
identification is asserted.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules.QuasiCoherent

namespace AlgebraicGeometry.Scheme.Cohomology

namespace ProjectiveCohomologyModel

/-- The original counit on the base-changed pushed resolution is a
quasi-isomorphism, using actual qcqs base change and quasicoherent pullback. -/
theorem baseChangeEmbeddingCounit_quasiIso {R : Type u} [CommRing R]
    {S : CommRingCat.{u}} {ι : Type u} {X : Scheme.{u}}
    (i : X ⟶ ProjectiveSpace R ι) [IsClosedImmersion i]
    (f : X ⟶ Spec (CommRingCat.of R)) {n : ℕ} (e : ι ≃ Fin (n + 1))
    (σ : R →+* S) (M : X.Modules) [M.IsQuasicoherent]
    (I : InjectiveResolution
      ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom σ)))).obj M)) :
    QuasiIso (Scheme.Modules.Complex.tildeGlobalSectionsCounit S (.up ℤ)
      (((Scheme.Modules.pushforward
      (pullback.snd f (Spec.map (CommRingCat.ofHom σ)))).mapCochainComplexPlus.obj
        I.cochainComplexPlus).obj)) := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (i ≫ toSpec R ι)
  let : QuasiCompact f := (quasiCompact_iff_compactSpace f).mpr inferInstance
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from i]; infer_instance⟩
  let : QuasiSeparated f := inferInstance
  let p := pullback.fst f (Spec.map (CommRingCat.ofHom σ))
  let N := (Scheme.Modules.pullback p).obj M
  let : N.IsQuasicoherent := Scheme.Modules.quasicoherent_pullback p M
  exact moduleResolutionPushforwardTildeCounit_quasiIso
    (pullback.snd f (Spec.map (CommRingCat.ofHom σ))) N I

variable {R : Type u} [CommRing R] {S : CommRingCat.{u}} {ι : Type u} {X : Scheme.{u}}
  {i : X ⟶ ProjectiveSpace R ι} {f : X ⟶ Spec (CommRingCat.of R)} {M : X.Modules} {n : ℕ}
  (D : ProjectiveCohomologyModel R ι i f M n) (σ : R →+* S)

local instance changedModelLower : (D.baseChangePlus σ).obj.IsStrictlyGE 0 := by
  let := D.lowerBound
  change CochainComplex.IsStrictlyGE
    (((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℤ)).obj D.complex) 0
  infer_instance

local instance changedModelUpper : (D.baseChangePlus σ).obj.IsStrictlyLE (n : ℤ) := by
  let := D.upperBound
  change CochainComplex.IsStrictlyLE
    (((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℤ)).obj D.complex) (n : ℤ)
  infer_instance

local instance changedModelFinite (j : ℤ) : Module.Finite S ((D.baseChangePlus σ).obj.X j) := by
  let : Module.Finite R (D.complex.X j) := D.finite_X j
  change Module.Finite S ((ModuleCat.extendScalars σ).obj (D.complex.X j))
  exact ModuleCat.finite_extendScalars σ (D.complex.X j)

local instance changedModelProjective (j : ℤ) :
    Module.Projective S ((D.baseChangePlus σ).obj.X j) := by
  let : Module.Projective R (D.complex.X j) := D.projective_X j
  change Module.Projective S ((ModuleCat.extendScalars σ).obj (D.complex.X j))
  exact ModuleCat.projective_extendScalars σ (D.complex.X j)

/-- Native tilde of the actual scalar extension of the same model is
strict perfect over the arbitrary new spectrum, with the original bounds. -/
def baseChangeStrictSheafModel : Scheme.Modules.Complex.StrictPerfect (Spec S) :=
  ⟨((tilde.functor S).mapHomologicalComplex (.up ℤ)).obj (D.baseChangePlus σ).obj,
    Scheme.Modules.Complex.strictPerfect_tilde_of_finite_projective
      S (D.baseChangePlus σ).obj 0 (n : ℤ)⟩

/-- The same actual base-changed strict sheaf complex in the native
bounded-below category. -/
def baseChangeStrictSheafModelPlus : CochainComplex.Plus (Spec S).Modules :=
  (tilde.functor S).mapCochainComplexPlus.obj (D.baseChangePlus σ)

/-- Both native packings retain the literal same actual sheaf complex. -/
theorem baseChangeStrictSheafModelPlus_obj :
    (D.baseChangeStrictSheafModelPlus σ).obj = (D.baseChangeStrictSheafModel σ).obj := rfl

variable [IsClosedImmersion i] [M.IsQuasicoherent]
  (e : ι ≃ Fin (n + 1)) (hflat : Scheme.Modules.relativeFlat f M)
  (I : InjectiveResolution
    ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom σ)))).obj M))

/-- The original lower native tilde/counit model arrow on the actual
base-changed pushed resolution, using the normalized original section map. -/
def baseChangeSheafComparison :
    (D.baseChangeStrictSheafModel σ).obj ⟶
      (((Scheme.Modules.pushforward
      (pullback.snd f (Spec.map (CommRingCat.ofHom σ)))).mapCochainComplexPlus.obj
        I.cochainComplexPlus).obj) :=
  Scheme.Modules.Complex.tildeModelMap S (D.baseChangePlus σ).obj
    (((Scheme.Modules.pushforward
      (pullback.snd f (Spec.map (CommRingCat.ofHom σ)))).mapCochainComplexPlus.obj
        I.cochainComplexPlus).obj)
    (D.baseChangeResolutionSectionsComparison σ e hflat I ≫
      (moduleSpecPushforwardGlobalSectionsComplexIso
        (pullback.snd f (Spec.map (CommRingCat.ofHom σ)))
            (.up ℤ) I.cochainComplexPlus.obj).inv)

/-- The actual same base-changed strict-model arrow is a quasi-isomorphism,
with both the original section comparison and original counit facts proved. -/
theorem baseChangeSheafComparison_quasiIso :
    QuasiIso (D.baseChangeSheafComparison σ e hflat I) := by
  let : QuasiIso (D.baseChangeResolutionSectionsComparison σ e hflat I) :=
    D.baseChangeResolutionSectionsComparison_quasiIso σ e hflat I
  let := baseChangeEmbeddingCounit_quasiIso i f e σ M I
  exact Scheme.Modules.Complex.tildeModelMap_quasiIso S (D.baseChangePlus σ).obj
    (((Scheme.Modules.pushforward
      (pullback.snd f (Spec.map (CommRingCat.ofHom σ)))).mapCochainComplexPlus.obj
        I.cochainComplexPlus).obj)
    (D.baseChangeResolutionSectionsComparison σ e hflat I ≫
      (moduleSpecPushforwardGlobalSectionsComplexIso
        (pullback.snd f (Spec.map (CommRingCat.ofHom σ)))
            (.up ℤ) I.cochainComplexPlus.obj).inv)

/-- The actual base-changed sheaf comparison retains the supplied original
native bounded-below packings. -/
def baseChangeSheafComparisonPlus :
    D.baseChangeStrictSheafModelPlus σ ⟶
      (Scheme.Modules.pushforward
      (pullback.snd f (Spec.map (CommRingCat.ofHom σ)))).mapCochainComplexPlus.obj
        I.cochainComplexPlus :=
  Scheme.Modules.Complex.tildeModelMapPlus S (D.baseChangePlus σ)
    ((Scheme.Modules.pushforward
      (pullback.snd f (Spec.map (CommRingCat.ofHom σ)))).mapCochainComplexPlus.obj
        I.cochainComplexPlus)
    (D.baseChangeResolutionSectionsComparison σ e hflat I ≫
      (moduleSpecPushforwardGlobalSectionsComplexIso
        (pullback.snd f (Spec.map (CommRingCat.ofHom σ)))
            (.up ℤ) I.cochainComplexPlus.obj).inv)

include D e hflat in
/-- The original actual base-changed pushed resolution has a native global
strict-perfect representative over the arbitrary new ring. -/
theorem hasStrictBaseChangeSheafModel : Scheme.Modules.Complex.HasStrictModel
    (((Scheme.Modules.pushforward
      (pullback.snd f (Spec.map (CommRingCat.ofHom σ)))).mapCochainComplexPlus.obj
        I.cochainComplexPlus).obj) := by
  let : QuasiIso (D.baseChangeResolutionSectionsComparison σ e hflat I) :=
    D.baseChangeResolutionSectionsComparison_quasiIso σ e hflat I
  let := baseChangeEmbeddingCounit_quasiIso i f e σ M I
  exact Scheme.Modules.Complex.hasStrictModel_of_tildeModelMap S (D.baseChangePlus σ).obj
    (((Scheme.Modules.pushforward
      (pullback.snd f (Spec.map (CommRingCat.ofHom σ)))).mapCochainComplexPlus.obj
        I.cochainComplexPlus).obj)
    (D.baseChangeResolutionSectionsComparison σ e hflat I ≫
      (moduleSpecPushforwardGlobalSectionsComplexIso
        (pullback.snd f (Spec.map (CommRingCat.ofHom σ)))
            (.up ℤ) I.cochainComplexPlus.obj).inv)
    0 (n : ℤ)

/-- The standard derived-category structure on the indicated module category. -/
local instance changedPerfectDerived (Z : Scheme.{u}) : HasDerivedCategory.{u + 1} Z.Modules :=
  HasDerivedCategory.standard _

/-- The literal tensor of the same source model, after native tilde,
represents installed actual derived direct image of the ordinary pulled
coefficient. The new ring need be neither flat nor Noetherian. -/
def baseChangeDerivedPushforwardIso :
    let Y := pullback f (Spec.map (CommRingCat.ofHom σ))
    let p := pullback.fst f (Spec.map (CommRingCat.ofHom σ))
    let r := pullback.snd f (Spec.map (CommRingCat.ofHom σ))
    DerivedCategory.Plus.Q.obj (D.baseChangeStrictSheafModelPlus σ) ≅
      (Scheme.Modules.pushforward r).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj
          ((Scheme.Modules.pullback p).obj M)) := by
  let : QuasiIso (D.baseChangeResolutionSectionsComparison σ e hflat I) :=
    D.baseChangeResolutionSectionsComparison_quasiIso σ e hflat I
  let := baseChangeEmbeddingCounit_quasiIso i f e σ M I
  exact Scheme.Modules.Complex.tildeModelDerivedIsoPlus S (D.baseChangePlus σ)
      ((Scheme.Modules.pushforward
      (pullback.snd f (Spec.map (CommRingCat.ofHom σ)))).mapCochainComplexPlus.obj
        I.cochainComplexPlus)
      (D.baseChangeResolutionSectionsComparison σ e hflat I ≫
        (moduleSpecPushforwardGlobalSectionsComplexIso
          (pullback.snd f (Spec.map (CommRingCat.ofHom σ)))
            (.up ℤ) I.cochainComplexPlus.obj).inv) ≪≫
    InjectiveResolution.rightDerivedFunctorPlusIso
      (Scheme.Modules.pushforward
      (pullback.snd f (Spec.map (CommRingCat.ofHom σ)))) I

/-- The native direct-image comparison retains the literal actual
base-changed sheaf arrow and original injective-resolution derived unit. -/
theorem baseChangeDerivedPushforwardIso_hom :
    (D.baseChangeDerivedPushforwardIso σ e hflat I).hom =
      DerivedCategory.Plus.Q.map (D.baseChangeSheafComparisonPlus σ e hflat I) ≫
        (InjectiveResolution.rightDerivedFunctorPlusIso
          (Scheme.Modules.pushforward
      (pullback.snd f (Spec.map (CommRingCat.ofHom σ)))) I).hom := rfl

end ProjectiveCohomologyModel

/-- The actual coherent relatively flat projective family over a
Noetherian base gives strict perfect original direct images after every
ring map, of the ordinary pulled coefficient, with the same term bounds. -/
theorem exists_strictPerfect_derivedPushforward_baseChange_of_projectiveEmbedding
    (R S : CommRingCat.{u}) [IsNoetherianRing R] (ι : Type u) {X : Scheme.{u}}
    (i : X ⟶ ProjectiveSpace R ι) [IsClosedImmersion i] (f : X ⟶ Spec R)
    (M : X.Modules) (n : ℕ) (e : ι ≃ Fin (n + 1)) (hf : i ≫ toSpec R ι = f)
    (hM : affineLocallyFiniteType X M) (hflat : Scheme.Modules.relativeFlat f M)
    (σ : R →+* S) :
    let Y := pullback f (Spec.map (CommRingCat.ofHom σ))
    let p := pullback.fst f (Spec.map (CommRingCat.ofHom σ))
    let r := pullback.snd f (Spec.map (CommRingCat.ofHom σ))
    letI : HasDerivedCategory.{u + 1} Y.Modules := HasDerivedCategory.standard _
    letI : HasDerivedCategory.{u + 1} (Spec S).Modules := HasDerivedCategory.standard _
    ∃ P : CochainComplex.Plus (Spec S).Modules,
      P.obj.IsStrictlyGE 0 ∧ P.obj.IsStrictlyLE (n : ℤ) ∧
        Scheme.Modules.Complex.strictPerfect (Spec S) P.obj ∧
          Nonempty (DerivedCategory.Plus.Q.obj P ≅
            (Scheme.Modules.pushforward r).rightDerivedFunctorPlus.obj
              ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj
                ((Scheme.Modules.pullback p).obj M))) := by
  let : M.IsQuasicoherent :=
    quasicoherent_of_affineCharts M (fun A j _ => (hM A j).1)
  let D := projectiveCohomologyModelOfEmbedding R ι i f M n e hf hM hflat
  let := D.lowerBound
  let := D.upperBound
  refine ⟨D.baseChangeStrictSheafModelPlus σ, ?_, ?_,
    (D.baseChangeStrictSheafModel σ).property,
    ⟨D.baseChangeDerivedPushforwardIso σ e hflat (injectiveResolution _)⟩⟩
  · change CochainComplex.IsStrictlyGE
      (((tilde.functor S).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℤ)).obj D.complex)) 0
    infer_instance
  · change CochainComplex.IsStrictlyLE
      (((tilde.functor S).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℤ)).obj D.complex)) (n : ℤ)
    infer_instance

end AlgebraicGeometry.Scheme.Cohomology
