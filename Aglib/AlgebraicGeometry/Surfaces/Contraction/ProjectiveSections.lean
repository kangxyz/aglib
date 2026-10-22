/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.CartierCurve.Vanishing
public import Aglib.AlgebraicGeometry.Cohomology.Projective.SerreVanishing
public import Aglib.AlgebraicGeometry.Cohomology.Projective.ClosedImmersion
public import Aglib.AlgebraicGeometry.Cohomology.Projective.Regularity.GlobalGeneration
public import Aglib.AlgebraicGeometry.Modules.ProjectionFormula.ClosedImmersion
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Pullback
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Tensor
public import Aglib.AlgebraicGeometry.Modules.Invertible.DualTensorEquivalence
public import Aglib.AlgebraicGeometry.Modules.Pullback.Free
public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Isomorphism
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor.Unit
public import Aglib.AlgebraicGeometry.Modules.ClosedImmersion.StructureQuotient
public import Aglib.AlgebraicGeometry.Modules.Pushforward.ClosedImmersion.Colimits
public import Aglib.AlgebraicGeometry.Modules.Invertible.FinitePresentation
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.FinitePresentation

/-!
# Projective Cartier vanishing and finite generating sections

An actual closed projective embedding supplies Serre vanishing for the literal
pullback of projective twists, tensor any coherent coefficient. The original
Cartier ideal sequence and the given conormal comparison construct the actual
projective-line quotient filtration. Cohomology exactness lifts its original
quotient sections, and induction combines finite kernel and quotient generators
to give finite epimorphic section families through `H^n(ndE)`. These are actual
sheaf-generating families; image construction and contraction remain further
geometric steps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open AlgebraicGeometry.Scheme.Modules.Invertible

namespace AlgebraicGeometry.Scheme.Surfaces.Contraction

universe u

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  {ι : Type u} {X : Scheme.{u}}
  (p : X ⟶ ProjectiveSpace A ι) [IsClosedImmersion p]

/-- The actual tensor twist pulled back from the specified projective embedding. -/
abbrev embeddedTensorTwist (d : ℤ) (F : X.Modules) : X.Modules :=
  (moduleTensorLeftFunctor X ((Scheme.Modules.pullback p).obj
    (twistingSheaf A ι d))).obj F

/-- Serre vanishing on a genuine closed projective subscheme, with the original
pullback tensor object and native sheaf cohomology. No relative flatness is needed. -/
theorem embeddedTensorTwist_serreVanishing (r : ℕ) (e : ι ≃ Fin (r + 1))
    (F : X.Modules) (hF : affineLocallyFiniteType X F) :
    ∃ B : ℕ, ∀ d : ℤ, (B : ℤ) ≤ d → ∀ q : ℕ, q ≠ 0 →
      Subsingleton (Sheaf.H.{u + 1} (Cohomology.moduleAddSheaf X
        (embeddedTensorTwist p d F)) q) := by
  let : Finite ι := Finite.of_equiv _ e.symm
  let : F.IsQuasicoherent :=
    quasicoherent_of_affineCharts F (fun R j _ => (hF R j).1)
  have hPF := Coherent.Pushforward.ClosedImmersion.affineLocallyFiniteType_pushforward p hF
  let : ((Scheme.Modules.pushforward p).obj F).IsQuasicoherent :=
    quasicoherent_of_affineCharts _ (fun R j _ => (hPF R j).1)
  obtain ⟨B, hB⟩ := Cohomology.projectiveSerreVanishing A ι r e
    ((Scheme.Modules.pushforward p).obj F) hPF
  refine ⟨B, fun d hd q hq => ?_⟩
  let : (embeddedTensorTwist p d F).IsQuasicoherent :=
    isQuasicoherent_moduleTensorLeftFunctor _ _
  let : ((Scheme.Modules.pushforward p).obj (embeddedTensorTwist p d F)).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_isAffineHom p _
  let := Cohomology.moduleCohomology_subsingleton_of_iso
    (closedImmersionProjectionFormulaIso p (twistingSheaf A ι d) F) q (hB d hd q hq)
  exact (Cohomology.projectiveEmbeddingCohomologyLinearEquiv A ι p
    (embeddedTensorTwist p d F) q).surjective.subsingleton

/-- Change only the displayed objects of an actual short complex. -/
def cartierSequenceOfIsos (S : ShortComplex X.Modules) {U V W : X.Modules}
    (e₁ : S.X₁ ≅ U) (e₂ : S.X₂ ≅ V) (e₃ : S.X₃ ≅ W) : ShortComplex X.Modules :=
  ShortComplex.mk (e₁.inv ≫ S.f ≫ e₂.hom) (e₂.inv ≫ S.g ≫ e₃.hom) (by
    calc
      (e₁.inv ≫ S.f ≫ e₂.hom) ≫ (e₂.inv ≫ S.g ≫ e₃.hom) =
          e₁.inv ≫ (S.f ≫ S.g) ≫ e₃.hom := by simp only [Category.assoc, Iso.hom_inv_id_assoc]
      _ = 0 := by simp only [S.zero, zero_comp, comp_zero])

theorem cartierSequenceOfIsos_shortExact (S : ShortComplex X.Modules)
    {U V W : X.Modules} (e₁ : S.X₁ ≅ U) (e₂ : S.X₂ ≅ V) (e₃ : S.X₃ ≅ W)
    (hS : S.ShortExact) : (cartierSequenceOfIsos S e₁ e₂ e₃).ShortExact := by
  let e : cartierSequenceOfIsos S e₁ e₂ e₃ ≅ S :=
    ShortComplex.isoMk e₁.symm e₂.symm e₃.symm
      (by
        dsimp only [cartierSequenceOfIsos]
        simp only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id])
      (by
        dsimp only [cartierSequenceOfIsos]
        simp only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id])
  exact ShortComplex.shortExact_of_iso e.symm hS

/-- Repeated positive Cartier twisting uses the actual dual ideal and native tensor product. -/
def cartierTwistLineBundle (J H : LineBundle X) : ℕ → LineBundle X
  | 0 => H
  | j + 1 => tensorLineBundle X (dualLineBundle X J) (cartierTwistLineBundle J H j)

/-- Nonnegative native projective twists admit a genuine finite global section family. -/
theorem finite_twist_family (R : Type u) [CommRing R] (τ : Type u)
    (r : ℕ) (e : τ ≃ Fin (r + 1)) (d : ℤ) (hd : 0 ≤ d) :
    ∃ (J : Type u) (_ : Finite J)
      (s : J → (𝟙_ (ProjectiveSpace R τ).Modules ⟶ twistingSheaf R τ d)),
      Epi (Sigma.desc s) := by
  let : Finite τ := Finite.of_equiv _ e.symm
  let P := ProjectiveSpace R τ
  let F : P.Modules := twistingSheaf R τ 0
  let : F.IsFinitePresentation := inferInstance
  have hF : affineLocallyFiniteType P F := affineLocallyFiniteType_of_finitePresentation F
  have hreg : Cohomology.IsProjectiveRegular R τ F 0 := by
    intro q hq
    let c : ℤ := 0 - (q : ℤ)
    have htw : Subsingleton (Sheaf.H.{u + 1} (Cohomology.moduleAddSheaf P
        (twistingSheaf R τ c)) q) := by
      by_cases hqr : q ≤ r
      · exact Cohomology.twistingCohomology_subsingleton_of_neg_le_degree
          R τ r e c q (by dsimp [c]; omega) (by omega)
      · exact Cohomology.projectiveCohomology_subsingleton_of_gt R τ r e
          (twistingSheaf R τ c) q (by omega)
    let eT : (moduleTensorLeftFunctor P (twistingSheaf R τ c)).obj F ≅
        twistingSheaf R τ c :=
      twistingTensorIso R τ c 0 ≪≫ eqToIso (congrArg (twistingSheaf R τ) (add_zero c))
    exact Cohomology.moduleCohomology_subsingleton_of_iso eT.symm q htw
  obtain ⟨σ, hσ⟩ := Cohomology.IsProjectiveRegular.exists_generatingSections_isFiniteType
    R τ r e hF hreg hd
  obtain ⟨J, hJ, s, hs⟩ := Cohomology.CartierCurve.finite_family_of_generatingSections σ hσ
  let : Finite J := hJ
  let eT : (moduleTensorLeftFunctor P (twistingSheaf R τ d)).obj F ≅
      twistingSheaf R τ d :=
    twistingTensorIso R τ d 0 ≪≫ eqToIso (congrArg (twistingSheaf R τ) (add_zero d))
  obtain ⟨t, ht⟩ := Cohomology.CartierCurve.finite_family_of_iso eT s hs
  exact ⟨J, hJ, t, ht⟩

-- The native pullback-unit comparison uses the structure-module unit underlying `𝟙_`.
set_option backward.isDefEq.respectTransparency false in
/-- The original pullback of a finite global family remains epimorphic. -/
theorem finite_family_pullback {Y : Scheme.{u}} (f : X ⟶ Y) {N : Y.Modules}
    {J : Type u} (s : J → (𝟙_ Y.Modules ⟶ N)) (hs : Epi (Sigma.desc s)) :
    ∃ t : J → (𝟙_ X.Modules ⟶ (Scheme.Modules.pullback f).obj N), Epi (Sigma.desc t) := by
  let T : Y.Modules ⥤ X.Modules := Scheme.Modules.pullback f
  let eU : T.obj (𝟙_ Y.Modules) ≅ 𝟙_ X.Modules := pullbackUnitIso f
  let : Epi (Sigma.desc s) := hs
  let t (j : J) : 𝟙_ X.Modules ⟶ T.obj N := eU.inv ≫ T.map (s j)
  refine ⟨t, ?_⟩
  have hfac : (Sigma.desc fun j : J =>
      eU.hom ≫ Sigma.ι (fun _ : J => 𝟙_ X.Modules) j) ≫ Sigma.desc t =
      sigmaComparison T (fun _ : J => 𝟙_ Y.Modules) ≫ T.map (Sigma.desc s) := by
    apply Sigma.hom_ext
    intro j
    dsimp only [t]
    rw [Sigma.ι_comp_desc_assoc, Category.assoc, Sigma.ι_comp_desc,
      Iso.hom_inv_id_assoc, ι_comp_sigmaComparison_assoc, ← Functor.map_comp,
      Sigma.ι_comp_desc]
  have : Epi (sigmaComparison T (fun _ : J => 𝟙_ Y.Modules) ≫ T.map (Sigma.desc s)) :=
    inferInstance
  exact epi_of_epi_fac hfac

/-- Closed direct image retains a finite global family through the original
structure-module map, which is epimorphic for the actual closed immersion. -/
theorem finite_family_pushforward {E : Scheme.{u}} (i : E ⟶ X) [IsClosedImmersion i]
    {N : E.Modules} {J : Type u}
    (s : J → (𝟙_ E.Modules ⟶ N)) (hs : Epi (Sigma.desc s)) :
    ∃ t : J → (𝟙_ X.Modules ⟶ (Scheme.Modules.pushforward i).obj N), Epi (Sigma.desc t) := by
  let T := Scheme.Modules.pushforward i
  let : Epi (Sigma.desc s) := hs
  let t (j : J) : 𝟙_ X.Modules ⟶ T.obj N := Hom.structureModuleMap i ≫ T.map (s j)
  refine ⟨t, ⟨?_⟩⟩
  intro Z f g h
  have hpart (j : J) : T.map (s j) ≫ f = T.map (s j) ≫ g := by
    apply (cancel_epi (Hom.structureModuleMap i)).mp
    simpa only [Sigma.ι_comp_desc_assoc, t, Category.assoc] using
      congrArg (fun q => Sigma.ι (fun _ : J => 𝟙_ X.Modules) j ≫ q) h
  apply (cancel_epi (T.map (Sigma.desc s))).mp
  apply (cancel_epi (sigmaComparison T (fun _ : J => 𝟙_ E.Modules))).mp
  apply Sigma.hom_ext
  intro j
  simpa only [Category.assoc, ι_comp_sigmaComparison_assoc, ← Functor.map_comp_assoc,
    Sigma.ι_comp_desc] using hpart j

section CartierSequence

variable {E : Scheme.{u}} (i : E ⟶ X) [IsClosedImmersion i]

/-- The actual Cartier ideal, retaining the original kernel object. -/
def cartierIdealLineBundle (hI : IsLocallyRankOne X (Hom.idealModule i)) : LineBundle X :=
  ⟨Hom.idealModule i, hI⟩

/-- Cancellation uses the original dual evaluation, associator and braiding. -/
def cartierCancellationIso (J M : LineBundle X) :
    tensorSheaf X (tensorSheaf X (dualLineBundle X J).val M.val) J.val ≅ M.val :=
  associator (C := X.Modules) (dualLineBundle X J).val M.val J.val ≪≫
    tensorSheafIso X (Iso.refl _) (tensorSheafBraiding X M.val J.val) ≪≫
      (associator (C := X.Modules) (dualLineBundle X J).val J.val M.val).symm ≪≫
        tensorSheafIso X (dualEvaluationIso X J) (Iso.refl M.val) ≪≫
          leftUnitor (C := X.Modules) M.val

/-- The actual Cartier sequence `M → M(E) → i_*i^*M(E)`, constructed by exact
invertible tensoring of the original ideal sequence and canonical cancellation. -/
def cartierStepSequence (hI : IsLocallyRankOne X (Hom.idealModule i))
    (M : LineBundle X) : ShortComplex X.Modules := by
  let J := cartierIdealLineBundle i hI
  let N := tensorLineBundle X (dualLineBundle X J) M
  let T := (lineBundleDualTensorEquivalence X N).inverse
  let S := (Hom.idealSequence i).map T
  let e₁ : S.X₁ ≅ M.val := by
    change tensorSheaf X (tensorSheaf X (dualLineBundle X J).val M.val) J.val ≅ M.val
    exact cartierCancellationIso J M
  let e₂ : S.X₂ ≅ N.val := by
    change tensorSheaf X N.val (SheafOfModules.unit X.ringCatSheaf) ≅ N.val
    exact rightUnitor (C := X.Modules) N.val
  let e₃ : S.X₃ ≅ (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj N.val) := by
    change tensorSheaf X N.val ((Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit E.ringCatSheaf)) ≅ _
    exact closedImmersionProjectionFormulaIso i N.val (SheafOfModules.unit E.ringCatSheaf) ≪≫
      (Scheme.Modules.pushforward i).mapIso
        (rightUnitor (C := E.Modules) ((Scheme.Modules.pullback i).obj N.val))
  exact cartierSequenceOfIsos S e₁ e₂ e₃

/-- The constructed Cartier sequence is short exact; no cohomological premise is used. -/
theorem cartierStepSequence_shortExact (hI : IsLocallyRankOne X (Hom.idealModule i))
    (M : LineBundle X) : (cartierStepSequence i hI M).ShortExact := by
  have hBase := Hom.idealSequence_shortExact i
  let : Mono (Hom.idealSequence i).f := hBase.mono_f
  let : Epi (Hom.idealSequence i).g := hBase.epi_g
  let N := tensorLineBundle X (dualLineBundle X (cartierIdealLineBundle i hI)) M
  let T := (lineBundleDualTensorEquivalence X N).inverse
  let : T.IsEquivalence := inferInstance
  dsimp only [cartierStepSequence]
  apply cartierSequenceOfIsos_shortExact
  exact hBase.map T

/-- The actual line bundle representing `nH + jE`. -/
def cartierPowerTwist (hI : IsLocallyRankOne X (Hom.idealModule i))
    (H : LineBundle X) (n j : ℕ) : LineBundle X :=
  cartierTwistLineBundle (cartierIdealLineBundle i hI) (tensorPowerLineBundle X H n) j

/-- The original successive Cartier inclusions, retaining the common multiplier
on every section pulled from the initial projective coefficient. -/
def cartierPowerInclusion (hI : IsLocallyRankOne X (Hom.idealModule i))
    (H : LineBundle X) (n : ℕ) :
    (j : ℕ) → (show X.Modules from (tensorPowerLineBundle X H n).val) ⟶
      (show X.Modules from (cartierPowerTwist i hI H n j).val)
  | 0 => 𝟙 _
  | j + 1 => cartierPowerInclusion hI H n j ≫
      (cartierStepSequence i hI (cartierPowerTwist i hI H n j)).f

end CartierSequence

section Restriction

variable {k : Type u} [CommRing k]
  (i : ProjectiveSpace k (ULift.{u} (Fin 2)) ⟶ X)

/-- The supplied conormal comparison determines the actual dual restriction.
The inverse is constructed by pullback of evaluation and native twist multiplication. -/
def conormalDualRestrictionIso (J : LineBundle X)
    (eJ : (Scheme.Modules.pullback i).obj J.val ≅
      twistingSheaf k (ULift.{u} (Fin 2)) 1) :
    (Scheme.Modules.pullback i).obj (dualLineBundle X J).val ≅
      twistingSheaf k (ULift.{u} (Fin 2)) (-1) := by
  let E := ProjectiveSpace k (ULift.{u} (Fin 2))
  let B := (Scheme.Modules.pullback i).obj (dualLineBundle X J).val
  let Oone := twistingSheaf k (ULift.{u} (Fin 2)) 1
  let OminusOne := twistingSheaf k (ULift.{u} (Fin 2)) (-1)
  letI : IsIso (pullbackTensorMap i (dualLineBundle X J).val J.val) :=
    Pullback.Tensor.pullbackTensorMap_isIso i (dualLineBundle X J).val J.val
  let eP : tensorSheaf E B Oone ≅ SheafOfModules.unit E.ringCatSheaf :=
    tensorSheafIso E (Iso.refl B) eJ.symm ≪≫
      (asIso (pullbackTensorMap i (dualLineBundle X J).val J.val)).symm ≪≫
      (Scheme.Modules.pullback i).mapIso (dualEvaluationIso X J) ≪≫ pullbackUnitIso i
  let eT : tensorSheaf E Oone OminusOne ≅ SheafOfModules.unit E.ringCatSheaf :=
    twistingTensorIso k (ULift.{u} (Fin 2)) 1 (-1) ≪≫
      twistingZeroIso k (ULift.{u} (Fin 2))
  exact (ρ_ B).symm ≪≫ tensorSheafIso E (Iso.refl B) eT.symm ≪≫
    (α_ B Oone OminusOne).symm ≪≫ tensorSheafIso E eP (Iso.refl OminusOne) ≪≫ (λ_ OminusOne)

/-- The actual restriction of every native tensor power follows from the single
specified restriction of the original line bundle. -/
def tensorPowerRestrictionIso (H : LineBundle X) (d : ℤ)
    (eH : (Scheme.Modules.pullback i).obj H.val ≅
      twistingSheaf k (ULift.{u} (Fin 2)) d) :
    (n : ℕ) → (Scheme.Modules.pullback i).obj (tensorPowerLineBundle X H n).val ≅
      twistingSheaf k (ULift.{u} (Fin 2)) ((n : ℤ) * d)
  | 0 => by
    let e₀ : (trivialLineBundle X).val ≅ SheafOfModules.unit X.ringCatSheaf :=
      coproductUniqueIso (fun _ : PUnit.{u + 1} => SheafOfModules.unit X.ringCatSheaf)
    simpa only [tensorPowerLineBundle, Int.natCast_zero, zero_mul] using
      ((Scheme.Modules.pullback i).mapIso e₀ ≪≫ pullbackUnitIso i ≪≫
        (twistingZeroIso k (ULift.{u} (Fin 2))).symm)
  | n + 1 => by
    change (Scheme.Modules.pullback i).obj
      (tensorSheaf X H.val (tensorPowerLineBundle X H n).val) ≅ _
    letI : IsIso (pullbackTensorMap i H.val (tensorPowerLineBundle X H n).val) :=
      Pullback.Tensor.pullbackTensorMap_isIso i H.val (tensorPowerLineBundle X H n).val
    refine asIso (pullbackTensorMap i H.val (tensorPowerLineBundle X H n).val) ≪≫
      tensorSheafIso _ eH (tensorPowerRestrictionIso H d eH n) ≪≫
      twistingTensorIso k (ULift.{u} (Fin 2)) d ((n : ℤ) * d) ≪≫ ?_
    exact eqToIso (congrArg (twistingSheaf k (ULift.{u} (Fin 2))) (by push_cast; ring))

/-- Every actual positive Cartier twist has the restriction predicted by the
conormal and coefficient comparisons. -/
def cartierTwistRestrictionIso (J H : LineBundle X) (m : ℤ)
    (eJ : (Scheme.Modules.pullback i).obj J.val ≅
      twistingSheaf k (ULift.{u} (Fin 2)) 1)
    (eH : (Scheme.Modules.pullback i).obj H.val ≅
      twistingSheaf k (ULift.{u} (Fin 2)) m) :
    (j : ℕ) → (Scheme.Modules.pullback i).obj (cartierTwistLineBundle J H j).val ≅
      twistingSheaf k (ULift.{u} (Fin 2)) (m - (j : ℤ))
  | 0 => by simpa only [cartierTwistLineBundle, Int.natCast_zero, sub_zero] using eH
  | j + 1 => by
    change (Scheme.Modules.pullback i).obj (tensorSheaf X (dualLineBundle X J).val
      (cartierTwistLineBundle J H j).val) ≅ _
    letI : IsIso (pullbackTensorMap i (dualLineBundle X J).val
        (cartierTwistLineBundle J H j).val) :=
      Pullback.Tensor.pullbackTensorMap_isIso i _ _
    refine asIso (pullbackTensorMap i (dualLineBundle X J).val
        (cartierTwistLineBundle J H j).val) ≪≫
      tensorSheafIso _ (conormalDualRestrictionIso i J eJ)
        (cartierTwistRestrictionIso J H m eJ eH j) ≪≫
      twistingTensorIso k (ULift.{u} (Fin 2)) (-1) (m - (j : ℤ)) ≪≫ ?_
    exact eqToIso (congrArg (twistingSheaf k (ULift.{u} (Fin 2))) (by push_cast; ring))

end Restriction

/-- Native tensor powers of a specified very ample coefficient are the
original pullbacks of the corresponding projective twists. -/
def projectivePowerIso (H : LineBundle X)
    (eH : H.val ≅ (Scheme.Modules.pullback p).obj (twistingSheaf A ι 1)) :
    (n : ℕ) → (tensorPowerLineBundle X H n).val ≅
      (Scheme.Modules.pullback p).obj (twistingSheaf A ι (n : ℤ))
  | 0 => by
    let e₀ : (trivialLineBundle X).val ≅ SheafOfModules.unit X.ringCatSheaf :=
      coproductUniqueIso (fun _ : PUnit.{u + 1} => SheafOfModules.unit X.ringCatSheaf)
    simpa only [tensorPowerLineBundle, Int.natCast_zero] using
      (e₀ ≪≫ (pullbackUnitIso p).symm ≪≫
        (Scheme.Modules.pullback p).mapIso (twistingZeroIso A ι).symm)
  | n + 1 => by
    change tensorSheaf X H.val (tensorPowerLineBundle X H n).val ≅ _
    letI : IsIso (pullbackTensorMap p (twistingSheaf A ι 1) (twistingSheaf A ι (n : ℤ))) :=
      Pullback.Tensor.pullbackTensorMap_isIso p _ _
    refine tensorSheafIso X eH (projectivePowerIso H eH n) ≪≫
      (asIso (pullbackTensorMap p (twistingSheaf A ι 1) (twistingSheaf A ι (n : ℤ)))).symm ≪≫
      (Scheme.Modules.pullback p).mapIso (twistingTensorIso A ι 1 (n : ℤ)) ≪≫ ?_
    exact eqToIso (congrArg (fun d => (Scheme.Modules.pullback p).obj
      (twistingSheaf A ι d)) (by push_cast; ring))

variable [CompactSpace X] [X.IsSeparated]
  {k : Type u} [CommRing k]
  (i : ProjectiveSpace k (ULift.{u} (Fin 2)) ⟶ X) [IsAffineHom i]

/-- A single native Serre bound controls the entire original projective-line
filtration through `nd + 1`; every actual quotient section lifts. The initial
term is compared with an actual pullback tensor twist, not assumed acyclic. -/
theorem exists_filtration_vanishing_and_section_lifts
    (r : ℕ) (e : ι ≃ Fin (r + 1)) (F : X.Modules)
    (hF : affineLocallyFiniteType X F) (d : ℕ)
    (M Q : ℕ → ℕ → X.Modules)
    (a : ∀ n j, M n j ⟶ M n (j + 1))
    (b : ∀ n j, M n (j + 1) ⟶ Q n j)
    (w : ∀ n j, a n j ≫ b n j = 0)
    (e₀ : ∀ n, M n 0 ≅ embeddedTensorTwist p (n : ℤ) F)
    (hS : ∀ n j, j < n * d + 1 →
      (ShortComplex.mk (a n j) (b n j) (w n j)).ShortExact)
    (eQ : ∀ n j, j < n * d + 1 → (Q n j ≅ (Scheme.Modules.pushforward i).obj
      (twistingSheaf k (ULift.{u} (Fin 2)) (((n * d : ℕ) : ℤ) - (j : ℤ) - 1)))) :
    ∃ B : ℕ, ∀ n : ℕ, B ≤ n →
      (∀ j, j ≤ n * d + 1 →
        Subsingleton (Sheaf.H.{u + 1} (Cohomology.moduleAddSheaf X (M n j)) 1)) ∧
      (∀ j, j < n * d + 1 → Function.Surjective ((b n j).val.app (op ⊤))) := by
  obtain ⟨B, hB⟩ := embeddedTensorTwist_serreVanishing p r e F hF
  refine ⟨B, fun n hn => ?_⟩
  have hzero : Subsingleton (Sheaf.H.{u + 1} (Cohomology.moduleAddSheaf X (M n 0)) 1) :=
    Cohomology.moduleCohomology_subsingleton_of_iso (e₀ n).symm 1
      (hB (n : ℤ) (by exact_mod_cast hn) 1 (by decide))
  exact Cohomology.CartierCurve.filtration_vanishing_and_section_lifts i
    (M n) (Q n) (a n) (b n) (w n) ((n * d : ℕ) : ℤ) (n * d + 1) (by omega)
    (hS n) (eQ n) hzero

omit [CompactSpace X] [X.IsSeparated] [IsAffineHom i] in
/-- Large powers of the specified very ample coefficient, twisted successively
by the actual exceptional Cartier curve, have vanishing first cohomology through
`nd + 1`. Every original restriction quotient section lifts. The conormal and
coefficient restriction comparisons are genuine native line-bundle isomorphisms. -/
theorem exists_cartier_vanishing_and_section_lifts [IsClosedImmersion i]
    (r : ℕ) (e : ι ≃ Fin (r + 1)) (H : LineBundle X)
    (eP : H.val ≅ (Scheme.Modules.pullback p).obj (twistingSheaf A ι 1))
    (hI : IsLocallyRankOne X (Hom.idealModule i)) (d : ℕ)
    (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
      twistingSheaf k (ULift.{u} (Fin 2)) 1)
    (eH : (Scheme.Modules.pullback i).obj H.val ≅
      twistingSheaf k (ULift.{u} (Fin 2)) (d : ℤ)) :
    ∃ B : ℕ, ∀ n : ℕ, B ≤ n →
      (∀ j, j ≤ n * d + 1 → Subsingleton (Sheaf.H.{u + 1} (Cohomology.moduleAddSheaf X
        (cartierPowerTwist i hI H n j).val) 1)) ∧
      (∀ j, j < n * d + 1 → Function.Surjective
        ((cartierStepSequence i hI (cartierPowerTwist i hI H n j)).g.val.app (op ⊤))) := by
  let : Finite ι := Finite.of_equiv _ e.symm
  let : CompactSpace (ProjectiveSpace A ι) :=
    QuasiCompact.compactSpace_of_compactSpace (toSpec A ι)
  let : (ProjectiveSpace A ι).IsSeparated := ⟨by
    rw [← terminal.comp_from (toSpec A ι)]
    infer_instance⟩
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : X.IsSeparated := ⟨by
    rw [← terminal.comp_from p]
    infer_instance⟩
  let J := cartierIdealLineBundle i hI
  let F := (trivialLineBundle X).val
  let := lineBundle_isFinitePresentation X (trivialLineBundle X)
  have hF : affineLocallyFiniteType X F := affineLocallyFiniteType_of_finitePresentation F
  let L (n j : ℕ) := cartierPowerTwist i hI H n j
  let M (n j : ℕ) : X.Modules := (L n j).val
  let Q (n j : ℕ) := (Scheme.Modules.pushforward i).obj
    ((Scheme.Modules.pullback i).obj (M n (j + 1)))
  let S (n j : ℕ) := cartierStepSequence i hI (L n j)
  let a (n j : ℕ) : M n j ⟶ M n (j + 1) := (S n j).f
  let b (n j : ℕ) : M n (j + 1) ⟶ Q n j := (S n j).g
  have w (n j : ℕ) : a n j ≫ b n j = 0 := (S n j).zero
  let eUnit : F ≅ SheafOfModules.unit X.ringCatSheaf :=
    coproductUniqueIso (fun _ : PUnit.{u + 1} => SheafOfModules.unit X.ringCatSheaf)
  have e₀ (n : ℕ) : M n 0 ≅ embeddedTensorTwist p (n : ℤ) F :=
    projectivePowerIso p H eP n ≪≫
      (rightUnitor (C := X.Modules)
        ((Scheme.Modules.pullback p).obj (twistingSheaf A ι (n : ℤ)))).symm ≪≫
      tensorSheafIso X (Iso.refl _) eUnit.symm
  have hS (n j : ℕ) (_hj : j < n * d + 1) :
      (ShortComplex.mk (a n j) (b n j) (w n j)).ShortExact := by
    change (cartierStepSequence i hI (L n j)).ShortExact
    exact cartierStepSequence_shortExact i hI (L n j)
  have eQ (n j : ℕ) (_hj : j < n * d + 1) : Q n j ≅
      (Scheme.Modules.pushforward i).obj (twistingSheaf k (ULift.{u} (Fin 2))
        (((n * d : ℕ) : ℤ) - (j : ℤ) - 1)) := by
    refine (Scheme.Modules.pushforward i).mapIso
      (cartierTwistRestrictionIso i J (tensorPowerLineBundle X H n) ((n : ℤ) * d) eI
        (tensorPowerRestrictionIso i H (d : ℤ) eH n) (j + 1) ≪≫ ?_)
    exact eqToIso (congrArg (twistingSheaf k (ULift.{u} (Fin 2))) (by push_cast; ring))
  exact exists_filtration_vanishing_and_section_lifts p i r e F hF d
    M Q a b w e₀ hS eQ

omit [CompactSpace X] [X.IsSeparated] [IsAffineHom i] in
/-- The actual Cartier coefficients through `nH+ndE` admit finite original
section families with epimorphic free maps. Quotient generators are lifted by
the proved cohomology theorem and joined to the preceding-stage generators. -/
theorem exists_cartier_finite_section_families [IsClosedImmersion i]
    (r : ℕ) (e : ι ≃ Fin (r + 1)) (H : LineBundle X)
    (eP : H.val ≅ (Scheme.Modules.pullback p).obj (twistingSheaf A ι 1))
    (hI : IsLocallyRankOne X (Hom.idealModule i)) (d : ℕ)
    (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
      twistingSheaf k (ULift.{u} (Fin 2)) 1)
    (eH : (Scheme.Modules.pullback i).obj H.val ≅
      twistingSheaf k (ULift.{u} (Fin 2)) (d : ℤ)) :
    ∃ B : ℕ, 1 ≤ B ∧ ∀ n : ℕ, B ≤ n → ∀ j : ℕ, j ≤ n * d →
      ∃ (J : Type u) (_ : Finite J)
        (s : J → (𝟙_ X.Modules ⟶ (show X.Modules from (cartierPowerTwist i hI H n j).val))),
        Epi (Sigma.desc s) := by
  obtain ⟨B, hB⟩ := exists_cartier_vanishing_and_section_lifts p i r e H eP hI d eI eH
  refine ⟨max B 1, le_max_right _ _, fun n hn => ?_⟩
  have hnB : B ≤ n := (le_max_left B 1).trans hn
  intro j
  induction j with
  | zero =>
    intro _
    obtain ⟨J, hJ, s, hs⟩ := finite_twist_family A ι r e (n : ℤ) (Int.natCast_nonneg n)
    let : Finite J := hJ
    obtain ⟨t, ht⟩ := finite_family_pullback p s hs
    obtain ⟨u, hu⟩ := Cohomology.CartierCurve.finite_family_of_iso
      (projectivePowerIso p H eP n).symm t ht
    exact ⟨J, hJ, u, hu⟩
  | succ j ih =>
    intro hj
    obtain ⟨J, hJ, sA, hA⟩ := ih (by omega)
    let : Finite J := hJ
    let S := cartierStepSequence i hI (cartierPowerTwist i hI H n j)
    let degree : ℤ := ((n * d : ℕ) : ℤ) - (j : ℤ) - 1
    obtain ⟨K, hK, sP, hP⟩ := finite_twist_family k (ULift.{u} (Fin 2))
      1 Equiv.ulift degree (by dsimp only [degree]; omega)
    let : Finite K := hK
    obtain ⟨sPush, hPush⟩ := finite_family_pushforward i sP hP
    have eQ : S.X₃ ≅ (Scheme.Modules.pushforward i).obj
        (twistingSheaf k (ULift.{u} (Fin 2)) degree) := by
      change (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj
        (cartierPowerTwist i hI H n (j + 1)).val) ≅ _
      refine (Scheme.Modules.pushforward i).mapIso
        (cartierTwistRestrictionIso i (cartierIdealLineBundle i hI)
          (tensorPowerLineBundle X H n) ((n : ℤ) * d) eI
          (tensorPowerRestrictionIso i H (d : ℤ) eH n) (j + 1) ≪≫ ?_)
      exact eqToIso (congrArg (twistingSheaf k (ULift.{u} (Fin 2)))
        (by dsimp only [degree]; push_cast; ring))
    obtain ⟨sC, hC⟩ := Cohomology.CartierCurve.finite_family_of_iso eQ.symm sPush hPush
    have hg : Function.Surjective (S.g.val.app (op ⊤)) := (hB n hnB).2 j (by omega)
    obtain ⟨sMiddle, hMiddle⟩ := Cohomology.CartierCurve.finite_family_middle S
      (cartierStepSequence_shortExact i hI (cartierPowerTwist i hI H n j)) sA hA sC hC hg
    exact ⟨J ⊕ K, inferInstance, sMiddle, hMiddle⟩

end AlgebraicGeometry.Scheme.Surfaces.Contraction
