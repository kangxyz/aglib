/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalModel.Class.Principal.Quotient
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Model.OpenComposition.Homology

/-!
# The original principal map on the direct fixed model

The source-isomorphism step normalizes the identity restriction of the
same ambient resolution. The ordinary open-comparison composition law
therefore gives a strict cochain equation, and the native restriction
homology comparisons identify the original two-stage principal arrow
with the direct chart-model arrow in every integer degree.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry HomologicalComplex

universe u
namespace AlgebraicGeometry.Scheme.Modules

private theorem principalRestrictCongr_refl {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (N : Y.Modules) :
    (restrictFunctorCongr (rfl : f = f)).hom.app N = 𝟙 _ := by
  apply Scheme.Modules.hom_ext
  intro T
  simp [restrictFunctorCongr_hom_app_app]
  rfl

private theorem principalRestrictComp_id {V P : Scheme.{u}} (j : V ⟶ P)
    [IsOpenImmersion j] (N : P.Modules) :
    (restrictFunctorComp (𝟙 V) j).hom.app N ≫
        restrictFunctorId.hom.app (N.restrict j) =
      (restrictFunctorCongr (Category.id_comp j)).hom.app N := by
  apply Scheme.Modules.hom_ext
  intro T
  simp only [Scheme.Modules.Hom.comp_app, restrictFunctorComp_hom_app_app,
    restrictFunctorId_hom_app_app, restrictFunctorCongr_hom_app_app]
  change N.presheaf.map _ ≫ N.presheaf.map _ = N.presheaf.map _
  simp only [← Functor.map_comp]
  congr 1

private theorem principalOpenIso_base_congr {W U V P : Scheme.{u}}
    (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ P) (j₀ j₁ : V ⟶ P)
    [IsOpenImmersion a] [IsOpenImmersion j₀] [IsOpenImmersion j₁]
    [IsClosedImmersion f] [IsClosedImmersion b]
    (hj : j₀ = j₁) (h₀ : IsPullback a b f j₀) (h₁ : IsPullback a b f j₁)
    (N : P.Modules) :
    (closedImmersionRightAdjointOpenIso a b f j₀ h₀).hom.app N ≫
        (closedImmersionRightAdjoint b).map ((restrictFunctorCongr hj).hom.app N) =
      (closedImmersionRightAdjointOpenIso a b f j₁ h₁).hom.app N := by
  subst j₁
  rw [principalRestrictCongr_refl, CategoryTheory.Functor.map_id]
  exact Category.comp_id _

private theorem principalOpenIso_comp_id {W' W U V P : Scheme.{u}}
    (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ P) (j : V ⟶ P)
    (c : W' ⟶ W) (d : W' ⟶ V)
    [IsOpenImmersion a] [IsOpenImmersion j] [IsOpenImmersion c]
    [IsClosedImmersion f] [IsClosedImmersion b] [IsClosedImmersion d]
    (h : IsPullback a b f j) (h' : IsPullback c d b (𝟙 V))
    (h₀ : IsPullback (c ≫ a) d f j) (N : P.Modules) :
    (restrictFunctorComp c a).hom.app ((closedImmersionRightAdjoint f).obj N) ≫
        (restrictFunctor c).map
          ((closedImmersionRightAdjointOpenIso a b f j h).hom.app N) ≫
        (closedImmersionRightAdjointOpenIso c d b (𝟙 V) h').hom.app (N.restrict j) ≫
        (closedImmersionRightAdjoint d).map
          (restrictFunctorId.hom.app (N.restrict j)) =
      (closedImmersionRightAdjointOpenIso (c ≫ a) d f j h₀).hom.app N := by
  have hc := canonicalClosedRightAdjointOpenIso_comp a b f j c d (𝟙 V) h h' N
  have hc' := congrArg (fun t => t ≫ (closedImmersionRightAdjoint d).map
    (restrictFunctorId.hom.app (N.restrict j))) hc
  calc
    _ = (closedImmersionRightAdjointOpenIso (c ≫ a) d f ((𝟙 V) ≫ j)
          (h'.paste_horiz h)).hom.app N ≫
        (closedImmersionRightAdjoint d).map
          ((restrictFunctorComp (𝟙 V) j).hom.app N ≫
            restrictFunctorId.hom.app (N.restrict j)) := by
      simpa only [Functor.map_comp, Category.assoc] using hc'
    _ = _ := by
      rw [principalRestrictComp_id]
      exact principalOpenIso_base_congr (c ≫ a) d f ((𝟙 V) ≫ j) j
        (Category.id_comp j) (h'.paste_horiz h) h₀ N

private theorem principalHomology_comp {W' W U : Scheme.{u}}
    (a : W ⟶ U) (c : W' ⟶ W) [IsOpenImmersion a] [IsOpenImmersion c]
    (K : CochainComplex U.Modules ℤ) (K₁ : CochainComplex W.Modules ℤ)
    (K₂ : CochainComplex W'.Modules ℤ)
    (O₁ : ((restrictFunctor a).mapHomologicalComplex (.up ℤ)).obj K ⟶ K₁)
    (O₂ : ((restrictFunctor c).mapHomologicalComplex (.up ℤ)).obj K₁ ⟶ K₂)
    (O₀ : ((restrictFunctor (c ≫ a)).mapHomologicalComplex (.up ℤ)).obj K ⟶ K₂)
    (hO : (canonicalRestrictionCompComplexIso a c (.up ℤ) K).hom ≫
      ((restrictFunctor c).mapHomologicalComplex (.up ℤ)).map O₁ ≫ O₂ = O₀)
    (n : ℤ) :
    (restrictFunctorComp c a).hom.app (K.homology n) ≫
        (restrictFunctor c).map
          (((K.sc n).mapHomologyIso (restrictFunctor a)).inv ≫ homologyMap O₁ n) ≫
        ((K₁.sc n).mapHomologyIso (restrictFunctor c)).inv ≫ homologyMap O₂ n =
      ((K.sc n).mapHomologyIso (restrictFunctor (c ≫ a))).inv ≫ homologyMap O₀ n := by
  let e₁ := (K.sc n).mapHomologyIso (restrictFunctor a)
  let e₂ := (K₁.sc n).mapHomologyIso (restrictFunctor c)
  let e₁₂ := ((((restrictFunctor a).mapHomologicalComplex (.up ℤ)).obj K).sc n).mapHomologyIso
    (restrictFunctor c)
  let e₀ := (K.sc n).mapHomologyIso (restrictFunctor (c ≫ a))
  have hN := ShortComplex.mapHomologyIso_inv_naturality
    ((shortComplexFunctor W.Modules (.up ℤ) n).map O₁) (restrictFunctor c)
  change (restrictFunctor c).map (homologyMap O₁ n) ≫ e₂.inv =
    e₁₂.inv ≫ homologyMap (((restrictFunctor c).mapHomologicalComplex (.up ℤ)).map O₁) n at hN
  have hR := canonicalRestrictionCompComplexIso_homology a c (.up ℤ) K n
  have hC := congrArg (fun t => homologyMap t n) hO
  simp only [homologyMap_comp] at hC
  simp only [Functor.map_comp, Category.assoc]
  change (restrictFunctorComp c a).hom.app (K.homology n) ≫
      (restrictFunctor c).map e₁.inv ≫ (restrictFunctor c).map (homologyMap O₁ n) ≫
      e₂.inv ≫ homologyMap O₂ n = e₀.inv ≫ homologyMap O₀ n
  calc
    _ = (restrictFunctorComp c a).hom.app (K.homology n) ≫
        (restrictFunctor c).map e₁.inv ≫ e₁₂.inv ≫
        homologyMap (((restrictFunctor c).mapHomologicalComplex (.up ℤ)).map O₁) n ≫
        homologyMap O₂ n := by
      simpa only [Category.assoc] using congrArg
        (fun t => (restrictFunctorComp c a).hom.app (K.homology n) ≫
          (restrictFunctor c).map e₁.inv ≫ t ≫ homologyMap O₂ n) hN
    _ = e₀.inv ≫ homologyMap (canonicalRestrictionCompComplexIso a c (.up ℤ) K).hom n ≫
        homologyMap (((restrictFunctor c).mapHomologicalComplex (.up ℤ)).map O₁) n ≫
        homologyMap O₂ n := by
      simpa only [e₁, e₁₂, e₀, Category.assoc] using congrArg
        (fun t => t ≫
          homologyMap (((restrictFunctor c).mapHomologicalComplex (.up ℤ)).map O₁) n ≫
          homologyMap O₂ n) hR
    _ = _ := by
      simpa only [Category.assoc] using congrArg (fun t => e₀.inv ≫ t) hC

private theorem principalStep_source_congr {W U V P : Scheme.{u}}
    (f : U ⟶ P) [IsClosedImmersion f] {L : P.Modules} (J : InjectiveResolution L)
    (a₀ a₁ : W ⟶ U) (j : V ⟶ P) (b : W ⟶ V)
    [IsOpenImmersion a₀] [IsOpenImmersion a₁] [IsOpenImmersion j]
    [IsClosedImmersion b] (ha : a₀ = a₁)
    (h₀ : IsPullback a₀ b f j) (h₁ : IsPullback a₁ b f j) (n : ℤ) :
    (restrictFunctorCongr ha).hom.app
        ((((closedImmersionRightAdjoint f).mapHomologicalComplex (.up ℤ)).obj
          J.cochainComplex).homology n) ≫
        closedImmersionChartModelStepHomologyMap f J a₁ j b h₁ n =
      closedImmersionChartModelStepHomologyMap f J a₀ j b h₀ n := by
  subst a₁
  rw [principalRestrictCongr_refl, Category.id_comp]

section AmbientSource
variable {A A' B B' C : CommRingCat.{u}}
  (φ : A ⟶ A') (σ : A ⟶ B) (τ : A' ⟶ B') (ψ : B ⟶ B')
  (δ : A' ⟶ C) (e : C ≃+* B')
  [IsOpenImmersion (Spec.map φ)] [IsOpenImmersion (Spec.map ψ)]
  [IsClosedImmersion (Spec.map σ)] [IsClosedImmersion (Spec.map τ)]
  [IsClosedImmersion (Spec.map δ)]
  (h : IsPullback (Spec.map ψ) (Spec.map τ) (Spec.map σ) (Spec.map φ))
  (h' : IsPullback (Spec.map e.toCommRingCatIso.inv) (Spec.map δ) (Spec.map τ)
    (𝟙 (Spec A')))
  (h₀ : IsPullback (Spec.map e.toCommRingCatIso.inv ≫ Spec.map ψ)
    (Spec.map δ) (Spec.map σ) (Spec.map φ))
  {L : (Spec A).Modules} (J : InjectiveResolution L)

private theorem principalAmbientSource_cochain_comp :
    (canonicalRestrictionCompComplexIso (Spec.map ψ) (Spec.map e.toCommRingCatIso.inv)
        (.up ℤ) (canonicalAmbientSourceSheafComplex σ J)).hom ≫
        ((restrictFunctor (Spec.map e.toCommRingCatIso.inv)).mapHomologicalComplex
          (.up ℤ)).map (canonicalAmbientModelOpenIso φ σ τ ψ h J).hom ≫
        (canonicalSourceModelOpenIso τ δ e h'
          (affineOpenRestrictedInjectiveResolution φ J)).hom =
      (closedImmersionModelOpenIso (Spec.map σ) J
        (Spec.map e.toCommRingCatIso.inv ≫ Spec.map ψ) (Spec.map φ) (Spec.map δ) h₀).hom := by
  let J' := affineOpenRestrictedInjectiveResolution φ J
  let ε := e.toCommRingCatIso.inv
  let E : ((restrictFunctor (Spec.map φ)).mapHomologicalComplex (.up ℤ)).obj
      J.cochainComplex ≅ J'.cochainComplex :=
    J.cocomplex.mapExtendIso (restrictFunctor (Spec.map φ)) ComplexShape.embeddingUpNat
  let η₁ := (closedImmersionRightAdjointOpenIso (Spec.map ψ) (Spec.map τ)
    (Spec.map σ) (Spec.map φ) h).hom
  let η₂ := (closedImmersionRightAdjointOpenIso (Spec.map ε) (Spec.map δ)
    (Spec.map τ) (𝟙 (Spec A')) h').hom
  let η₀ := (closedImmersionRightAdjointOpenIso (Spec.map ε ≫ Spec.map ψ)
    (Spec.map δ) (Spec.map σ) (Spec.map φ) h₀).hom
  ext n : 1
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    canonicalRestrictionCompComplexIso_hom_f, canonicalAmbientModelOpenIso_hom_f,
    canonicalSourceModelOpenIso_hom_f, closedImmersionModelOpenIso_hom_f,
    Functor.map_comp, Category.assoc]
  have hN := η₂.naturality (E.hom.f n)
  change (restrictFunctor (Spec.map ε)).map
      ((closedImmersionRightAdjoint (Spec.map τ)).map (E.hom.f n)) ≫
        η₂.app (J'.cochainComplex.X n) =
    η₂.app ((restrictFunctor (Spec.map φ)).obj (J.cochainComplex.X n)) ≫
      (closedImmersionRightAdjoint (Spec.map δ)).map
        ((restrictFunctor (𝟙 (Spec A'))).map (E.hom.f n)) at hN
  have hI := restrictFunctorId.hom.naturality (E.hom.f n)
  change (restrictFunctor (𝟙 (Spec A'))).map (E.hom.f n) ≫
      restrictFunctorId.hom.app (J'.cochainComplex.X n) =
    restrictFunctorId.hom.app ((restrictFunctor (Spec.map φ)).obj (J.cochainComplex.X n)) ≫
      E.hom.f n at hI
  have hO : (restrictFunctorComp (Spec.map ε) (Spec.map ψ)).hom.app
      ((closedImmersionRightAdjoint (Spec.map σ)).obj (J.cochainComplex.X n)) ≫
      (restrictFunctor (Spec.map ε)).map (η₁.app (J.cochainComplex.X n)) ≫
      η₂.app ((restrictFunctor (Spec.map φ)).obj (J.cochainComplex.X n)) ≫
      (closedImmersionRightAdjoint (Spec.map δ)).map
        (restrictFunctorId.hom.app
          ((restrictFunctor (Spec.map φ)).obj (J.cochainComplex.X n))) =
    η₀.app (J.cochainComplex.X n) :=
    principalOpenIso_comp_id (Spec.map ψ) (Spec.map τ) (Spec.map σ)
      (Spec.map φ) (Spec.map ε) (Spec.map δ) h h' h₀ (J.cochainComplex.X n)
  change (restrictFunctorComp (Spec.map ε) (Spec.map ψ)).hom.app
      ((closedImmersionRightAdjoint (Spec.map σ)).obj (J.cochainComplex.X n)) ≫
      (restrictFunctor (Spec.map ε)).map (η₁.app (J.cochainComplex.X n)) ≫
      (restrictFunctor (Spec.map ε)).map
        ((closedImmersionRightAdjoint (Spec.map τ)).map (E.hom.f n)) ≫
      η₂.app (J'.cochainComplex.X n) ≫
      (closedImmersionRightAdjoint (Spec.map δ)).map
        (restrictFunctorId.hom.app (J'.cochainComplex.X n)) =
    η₀.app (J.cochainComplex.X n) ≫
      (closedImmersionRightAdjoint (Spec.map δ)).map (E.hom.f n)
  rw [← Category.assoc ((restrictFunctor (Spec.map ε)).map
      ((closedImmersionRightAdjoint (Spec.map τ)).map (E.hom.f n))), hN]
  simp only [Category.assoc]
  rw [← Functor.map_comp, hI, Functor.map_comp]
  simpa only [Category.assoc] using congrArg
    (fun t => t ≫ (closedImmersionRightAdjoint (Spec.map δ)).map (E.hom.f n)) hO

private theorem principalAmbientSource_homology_comp (n : ℤ) :
    (restrictFunctorComp (Spec.map e.toCommRingCatIso.inv) (Spec.map ψ)).hom.app
        ((canonicalAmbientSourceSheafComplex σ J).homology n) ≫
        (restrictFunctor (Spec.map e.toCommRingCatIso.inv)).map
          (canonicalAmbientSheafHomologyMap φ σ τ ψ h J n) ≫
        canonicalSourceSheafHomologyMap τ δ e h'
          (affineOpenRestrictedInjectiveResolution φ J) n =
      closedImmersionChartModelStepHomologyMap (Spec.map σ) J
        (Spec.map e.toCommRingCatIso.inv ≫ Spec.map ψ) (Spec.map φ) (Spec.map δ) h₀ n := by
  let J' := affineOpenRestrictedInjectiveResolution φ J
  exact principalHomology_comp (Spec.map ψ) (Spec.map e.toCommRingCatIso.inv)
    (canonicalAmbientSourceSheafComplex σ J) (canonicalSourceSheafComplex τ J')
    (canonicalSourceSheafComplex δ J')
    (canonicalAmbientModelOpenIso φ σ τ ψ h J).hom
    (canonicalSourceModelOpenIso τ δ e h' J').hom
    (closedImmersionModelOpenIso (Spec.map σ) J
      (Spec.map e.toCommRingCatIso.inv ≫ Spec.map ψ) (Spec.map φ) (Spec.map δ) h₀).hom
    (principalAmbientSource_cochain_comp φ σ τ ψ δ e h h' h₀ J) n

include h₀ in
private theorem principalAmbientSource_homology_congr
    (a₀ : Spec C ⟶ Spec B) [IsOpenImmersion a₀]
    (ha : a₀ = Spec.map e.toCommRingCatIso.inv ≫ Spec.map ψ)
    (h₁ : IsPullback a₀ (Spec.map δ) (Spec.map σ) (Spec.map φ)) (n : ℤ) :
    (restrictFunctorCongr ha).hom.app ((canonicalAmbientSourceSheafComplex σ J).homology n) ≫
        (restrictFunctorComp (Spec.map e.toCommRingCatIso.inv) (Spec.map ψ)).hom.app
          ((canonicalAmbientSourceSheafComplex σ J).homology n) ≫
        (restrictFunctor (Spec.map e.toCommRingCatIso.inv)).map
          (canonicalAmbientSheafHomologyMap φ σ τ ψ h J n) ≫
        canonicalSourceSheafHomologyMap τ δ e h'
          (affineOpenRestrictedInjectiveResolution φ J) n =
      closedImmersionChartModelStepHomologyMap (Spec.map σ) J a₀
        (Spec.map φ) (Spec.map δ) h₁ n := by
  exact (congrArg (fun t => (restrictFunctorCongr ha).hom.app
      ((canonicalAmbientSourceSheafComplex σ J).homology n) ≫ t)
        (principalAmbientSource_homology_comp φ σ τ ψ δ e h h' h₀ J n)).trans
    (principalStep_source_congr (Spec.map σ) J a₀
      (Spec.map e.toCommRingCatIso.inv ≫ Spec.map ψ) (Spec.map φ) (Spec.map δ) ha h₁ h₀ n)

end AmbientSource

variable {A : CommRingCat.{u}} (s : List A) (r : A)

local instance principalModelQuotientClosed {S : CommRingCat.{u}} (t : List S) :
    IsClosedImmersion (Spec.map (regularListQuotientMap t)) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

local instance principalModelRawClosed : IsClosedImmersion
    (Spec.map (CommRingCat.ofHom (regularListPrincipalClosedMap s r))) :=
  IsClosedImmersion.spec_of_surjective _
    (IsLocalization.map_surjective_of_surjective (Submonoid.powers r) (Localization.Away r)
      (Localization.Away (Ideal.Quotient.mk (Ideal.ofList s) r)) Ideal.Quotient.mk_surjective)

local instance principalModelLocalizedClosed : IsClosedImmersion
    (Spec.map (regularListQuotientMap (A := CommRingCat.of (Localization.Away r))
      (regularListPrincipalList s r))) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- The literal principal quotient map has the original quotient Cartesian square. -/
theorem regularListPrincipalLiteralIsPullback :
    IsPullback (Spec.map (regularListPrincipalLiteralQuotientMap s r))
      (Spec.map (regularListQuotientMap (A := CommRingCat.of (Localization.Away r))
        (regularListPrincipalList s r)))
      (Spec.map (regularListQuotientMap s))
      (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away r)))) := by
  rw [regularListPrincipalLiteralQuotientMap_spec]
  exact regularListPrincipalSquare s r

variable {L : (Spec A).Modules} (J : InjectiveResolution L)

private theorem principalLiteral_native (n : ℤ) :
    let S := CommRingCat.of (Localization.Away r)
    let T := CommRingCat.of (Localization.Away (Ideal.Quotient.mk (Ideal.ofList s) r))
    let φ : A ⟶ S := CommRingCat.ofHom (algebraMap A (Localization.Away r))
    let q := regularListQuotientMap s
    let q' : S ⟶ T := CommRingCat.ofHom (regularListPrincipalClosedMap s r)
    let τ := regularListQuotientMap (A := S) (regularListPrincipalList s r)
    let : IsClosedImmersion (Spec.map τ) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    let ψ : regularListQuotientRing s ⟶ T := CommRingCat.ofHom
      (algebraMap (A ⧸ Ideal.ofList s) (Localization.Away (Ideal.Quotient.mk (Ideal.ofList s) r)))
    let ε := (regularListPrincipalQuotientEquiv s r).toCommRingCatIso.inv
    regularListPrincipalLiteralSheafHomologyMap s r J n =
      (restrictFunctorCongr (regularListPrincipalLiteralQuotientMap_spec s r)).hom.app
          ((canonicalAmbientSourceSheafComplex q J).homology n) ≫
        (restrictFunctorComp (Spec.map ε) (Spec.map ψ)).hom.app
          ((canonicalAmbientSourceSheafComplex q J).homology n) ≫
        (restrictFunctor (Spec.map ε)).map
          (canonicalAmbientSheafHomologyMap φ q q' ψ (regularListPrincipalRawSquare s r) J n) ≫
        canonicalSourceSheafHomologyMap q' τ (regularListPrincipalQuotientEquiv s r)
          (regularListPrincipalSourceOnlySquare s r)
          (affineOpenRestrictedInjectiveResolution φ J) n := rfl

/-- In every integer degree, the original literal principal map is the original
direct chart-model map for its actual Cartesian square. -/
theorem regularListPrincipalLiteralSheafHomologyMap_eq_step (n : ℤ) :
    regularListPrincipalLiteralSheafHomologyMap s r J n =
      closedImmersionChartModelStepHomologyMap (Spec.map (regularListQuotientMap s)) J
        (Spec.map (regularListPrincipalLiteralQuotientMap s r))
        (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away r))))
        (Spec.map (regularListQuotientMap (A := CommRingCat.of (Localization.Away r))
          (regularListPrincipalList s r))) (regularListPrincipalLiteralIsPullback s r) n :=
  (principalLiteral_native s r J n).trans
    (principalAmbientSource_homology_congr
      (CommRingCat.ofHom (algebraMap A (Localization.Away r)))
      (regularListQuotientMap s) (CommRingCat.ofHom (regularListPrincipalClosedMap s r))
      (CommRingCat.ofHom (algebraMap (A ⧸ Ideal.ofList s)
        (Localization.Away (Ideal.Quotient.mk (Ideal.ofList s) r))))
      (regularListQuotientMap (A := CommRingCat.of (Localization.Away r))
        (regularListPrincipalList s r)) (regularListPrincipalQuotientEquiv s r)
      (regularListPrincipalRawSquare s r) (regularListPrincipalSourceOnlySquare s r)
      (regularListPrincipalSquare s r) J
      (Spec.map (regularListPrincipalLiteralQuotientMap s r))
      (regularListPrincipalLiteralQuotientMap_spec s r)
      (regularListPrincipalLiteralIsPullback s r) n)

end AlgebraicGeometry.Scheme.Modules
