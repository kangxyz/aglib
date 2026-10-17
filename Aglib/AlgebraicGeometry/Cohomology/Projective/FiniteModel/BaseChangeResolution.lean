/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Finiteness
public import Aglib.Algebra.Homology.DerivedCategory.KProjective.Representative
public import Aglib.AlgebraicGeometry.Cohomology.Projective.FiniteModel.DerivedBaseChange

/-!
# Actual original resolution-section models after arbitrary base change

The same scalar-extended finite-projective model has an actual chain
quasi-isomorphism to sections of any original module injective resolution
of the ordinary pulled coefficient. Its literal native localization is the
proved all-base-change derived comparison followed by the inverse original
resolution unit. No Noetherianity of the new ring or preservation of
injectives by coefficient pullback is assumed.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HomologicalComplex

namespace AlgebraicGeometry.Scheme.Cohomology.ProjectiveCohomologyModel

variable {R : Type u} [CommRing R] {ι : Type u} {X : Scheme.{u}}
  {i : X ⟶ ProjectiveSpace R ι} [IsClosedImmersion i]
  {f : X ⟶ Spec (CommRingCat.of R)} {M : X.Modules} [M.IsQuasicoherent] {n : ℕ}
  (D : ProjectiveCohomologyModel R ι i f M n)
  {B : Type u} [CommRing B] (σ : R →+* B) (e : ι ≃ Fin (n + 1))
  (hflat : Scheme.Modules.relativeFlat f M)
  (I : InjectiveResolution
    ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom σ)))).obj M))

/-- The standard derived-category structure on the indicated module category. -/
local instance changedResolutionSource (Z : Scheme.{u}) : HasDerivedCategory.{u + 1} Z.Modules :=
  HasDerivedCategory.standard _

/-- The standard derived-category structure on the indicated module category. -/
local instance changedResolutionTarget (A : Type u) [CommRing A] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} A) := HasDerivedCategory.standard _

/-- The original all-base-change model comparison, followed by the inverse
original derived unit on the actual pulled-coefficient resolution. -/
def baseChangeResolutionSectionsDerivedIsoPlus :
    let Y := pullback f (Spec.map (CommRingCat.ofHom σ))
    let r := pullback.snd f (Spec.map (CommRingCat.ofHom σ))
    let β := r.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
    DerivedCategory.Plus.Q.obj (D.baseChangePlus σ) ≅
      DerivedCategory.Plus.Q.obj
        ((moduleGlobalSectionsFunctorOfHom Y β).mapCochainComplexPlus.obj
          I.cochainComplexPlus) :=
  D.baseChangeDerivedGlobalSectionsIso σ e hflat I ≪≫
    (InjectiveResolution.rightDerivedFunctorPlusIso
      (moduleGlobalSectionsFunctorOfHom (pullback f (Spec.map (CommRingCat.ofHom σ)))
        ((pullback.snd f (Spec.map (CommRingCat.ofHom σ))).appTop.hom.comp
          (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom)) I).symm

/-- The same original comparison in the native ambient localization,
retaining the original bounded-below inclusion factors. -/
def baseChangeResolutionSectionsDerivedIso :
    let Y := pullback f (Spec.map (CommRingCat.ofHom σ))
    let r := pullback.snd f (Spec.map (CommRingCat.ofHom σ))
    let β := r.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
    DerivedCategory.Q.obj (D.baseChangePlus σ).obj ≅
      DerivedCategory.Q.obj
        (((moduleGlobalSectionsFunctorOfHom Y β).mapCochainComplexPlus.obj
          I.cochainComplexPlus).obj) :=
  ((DerivedCategory.Plus.QCompιIso (ModuleCat.{u} B)).app (D.baseChangePlus σ)).symm ≪≫
    (DerivedCategory.Plus.ι).mapIso (D.baseChangeResolutionSectionsDerivedIsoPlus σ e hflat I) ≪≫
      (DerivedCategory.Plus.QCompιIso (ModuleCat.{u} B)).app
        ((moduleGlobalSectionsFunctorOfHom (pullback f (Spec.map (CommRingCat.ofHom σ)))
          ((pullback.snd f (Spec.map (CommRingCat.ofHom σ))).appTop.hom.comp
            (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom)).mapCochainComplexPlus.obj
              I.cochainComplexPlus)

/-- The actual scalar extension of the same projective model maps by an
actual quasi-isomorphism to the original resolution sections, with exactly
the proved original derived comparison as its native `Q.map`. -/
theorem exists_baseChangeResolutionSectionsComparison :
    let Y := pullback f (Spec.map (CommRingCat.ofHom σ))
    let r := pullback.snd f (Spec.map (CommRingCat.ofHom σ))
    let β := r.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
    ∃ u : (D.baseChangePlus σ).obj ⟶
        (((moduleGlobalSectionsFunctorOfHom Y β).mapCochainComplexPlus.obj
          I.cochainComplexPlus).obj),
      QuasiIso u ∧ DerivedCategory.Q.map u =
        (D.baseChangeResolutionSectionsDerivedIso σ e hflat I).hom := by
  dsimp only
  let P := (D.baseChangePlus σ).obj
  let := D.upperBound
  let (j : ℤ) : Module.Projective R (D.complex.X j) := D.projective_X j
  let : P.IsStrictlyLE (n : ℤ) := by
    change CochainComplex.IsStrictlyLE
      (((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℤ)).obj D.complex) (n : ℤ)
    infer_instance
  let (j : ℤ) : Module.Projective B (P.X j) := by
    change Module.Projective B ((ModuleCat.extendScalars σ).obj (D.complex.X j))
    exact ModuleCat.projective_extendScalars σ (D.complex.X j)
  have (j : ℤ) : Projective (P.X j) := inferInstance
  let : P.IsKProjective := CochainComplex.isKProjective_of_projective P (n : ℤ)
  exact CochainComplex.IsKProjective.exists_quasiIso_of_derivedIso P _
    (D.baseChangeResolutionSectionsDerivedIso σ e hflat I)

/-- A chosen actual representative of the fixed original all-base-change
resolution comparison. The target resolution is independently chosen for
the ordinary pulled coefficient, rather than obtained by pulling injectives. -/
def baseChangeResolutionSectionsComparison :
    let Y := pullback f (Spec.map (CommRingCat.ofHom σ))
    let r := pullback.snd f (Spec.map (CommRingCat.ofHom σ))
    let β := r.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
    (D.baseChangePlus σ).obj ⟶
      (((moduleGlobalSectionsFunctorOfHom Y β).mapCochainComplexPlus.obj
        I.cochainComplexPlus).obj) :=
  Classical.choose (D.exists_baseChangeResolutionSectionsComparison σ e hflat I)

/-- The same actual all-base-change representative is a quasi-isomorphism. -/
theorem baseChangeResolutionSectionsComparison_quasiIso :
    QuasiIso (D.baseChangeResolutionSectionsComparison σ e hflat I) :=
  (Classical.choose_spec (D.exists_baseChangeResolutionSectionsComparison σ e hflat I)).1

/-- The actual representative keeps the original all-base-change derived
comparison under literal native localization. -/
theorem baseChangeResolutionSectionsComparison_Q_map :
    DerivedCategory.Q.map (D.baseChangeResolutionSectionsComparison σ e hflat I) =
      (D.baseChangeResolutionSectionsDerivedIso σ e hflat I).hom :=
  (Classical.choose_spec (D.exists_baseChangeResolutionSectionsComparison σ e hflat I)).2

end AlgebraicGeometry.Scheme.Cohomology.ProjectiveCohomologyModel
