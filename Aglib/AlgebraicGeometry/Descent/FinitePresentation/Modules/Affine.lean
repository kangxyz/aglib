/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Descent.FinitePresentation.Models
public import Aglib.Algebra.Category.ModuleCat.Descent.FinitePresentation.Maps
public import Aglib.AlgebraicGeometry.Descent.Modules.ZariskiStack
public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.Diagrams
public import Aglib.AlgebraicGeometry.Modules.FinitePresentation.Basic
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Pullback
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteType
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.TildePullback
public import Mathlib.RingTheory.LocalProperties.FinitePresentation

/-!
# Finite presentation and actual affine module models

The affine module/sheaf comparison works over arbitrary commutative rings:
finite presentation of a module gives finite presentation of its tilde sheaf,
and finite presentation of an actual affine module sheaf gives finite
presentation of its actual global-section module. No Noetherian hypothesis
is used.

Over a filtered colimit of rings, the actual module model and the native
tilde/pullback comparison then give an actual affine sheaf model with a
specified pullback isomorphism. General qcqs fixed-model gluing and finite
diagram descent are separate further obligations.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite TensorProduct
open scoped ModuleCat.Algebra

namespace AlgebraicGeometry.Scheme.Modules

/-- A genuinely finitely presented module has a finitely presented associated
module sheaf over an arbitrary commutative ring. -/
theorem finitePresentation_tilde_of_moduleFinitePresentation (R : CommRingCat.{u})
    (M : ModuleCat.{u} R) [Module.FinitePresentation R M] :
    (tilde M).IsFinitePresentation := by
  classical
  obtain ⟨s, hs, hker⟩ := (inferInstance : Module.FinitePresentation R M)
  obtain ⟨t, ht⟩ := hker
  let P := presentationTilde M (s : Set M) hs (t : Set ((s : Set M) →₀ R)) ht
  have : P.IsFinite :=
    { isFiniteType_generators := ⟨inferInstanceAs (Finite (s : Set M))⟩
      isFiniteType_relations := ⟨inferInstanceAs (Finite (t : Set ((s : Set M) →₀ R)))⟩ }
  exact finitePresentation_of_presentation P

private theorem finitePresentation_quotient_finsupp
    {R : Type u} [CommRing R] {J K : Type u} [Finite J] [Finite K]
    (f : (J →₀ R) →ₗ[R] (K →₀ R)) :
    Module.FinitePresentation R ((K →₀ R) ⧸ LinearMap.range f) := by
  apply Module.finitePresentation_of_surjective (LinearMap.range f).mkQ
    (LinearMap.range f).mkQ_surjective
  rw [Submodule.ker_mkQ]
  exact Submodule.fg_range f

private theorem tilde_preimage_free_square (R : CommRingCat.{u})
    (J K : Type u)
    (f : SheafOfModules.free (R := (Spec R).ringCatSheaf) J ⟶
      SheafOfModules.free (R := (Spec R).ringCatSheaf) K) :
    (tilde.functor R).map ((tilde.functor R).preimage
        ((tildeFinsupp J).hom ≫ f ≫ (tildeFinsupp K).inv)) ≫ (tildeFinsupp K).hom =
      (tildeFinsupp J).hom ≫ f := by
  let t := (tildeFinsupp J).hom ≫ f ≫ (tildeFinsupp K).inv
  have hpre : (tilde.functor R).map ((tilde.functor R).preimage t) = t :=
    (tilde.functor R).map_preimage t
  calc
    _ = t ≫ (tildeFinsupp K).hom :=
      congrArg (fun q ↦ q ≫ (tildeFinsupp K).hom) hpre
    _ = _ := by simp only [t, Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem moduleFinitePresentation_of_globalPresentation (R : CommRingCat.{u})
    (M : (Spec R).Modules) (P : M.Presentation) [P.IsFinite] :
    Module.FinitePresentation R (moduleSpecΓFunctor.obj M) := by
  classical
  have : Finite P.generators.I :=
    SheafOfModules.GeneratingSections.IsFiniteType.finite
  have : Finite P.relations.I :=
    SheafOfModules.GeneratingSections.IsFiniteType.finite
  let f := (SheafOfModules.freeHomEquiv _).symm P.relations.s ≫ kernel.ι P.generators.π
  let f₀ : ModuleCat.of R (P.relations.I →₀ R) ⟶
      ModuleCat.of R (P.generators.I →₀ R) :=
    (tilde.functor R).preimage ((tildeFinsupp P.relations.I).hom ≫ f ≫
      (tildeFinsupp P.generators.I).inv)
  have hsquare : (tilde.functor R).map f₀ ≫ (tildeFinsupp P.generators.I).hom =
      (tildeFinsupp P.relations.I).hom ≫ f :=
    tilde_preimage_free_square R P.relations.I P.generators.I f
  let Q := (P.generators.I →₀ R) ⧸ LinearMap.range f₀.hom
  have : Module.FinitePresentation R Q := finitePresentation_quotient_finsupp f₀.hom
  let eP : cokernel f ≅ M :=
    (P.isColimit.coconePointUniqueUpToIso (colimit.isColimit _)).symm
  let e : tilde (ModuleCat.of R Q) ≅ M :=
    (tilde.functor R).mapIso (ModuleCat.cokernelIsoRangeQuotient f₀).symm ≪≫
      PreservesCokernel.iso (tilde.functor R) f₀ ≪≫
      cokernel.mapIso ((tilde.functor R).map f₀) f
        (tildeFinsupp P.relations.I) (tildeFinsupp P.generators.I) hsquare ≪≫ eP
  let eΓ : ModuleCat.of R Q ≅ moduleSpecΓFunctor.obj M :=
    tilde.isoTop (ModuleCat.of R Q) ≪≫ moduleSpecΓFunctor.mapIso e
  exact Module.FinitePresentation.of_equiv eΓ.toLinearEquiv

private theorem moduleFinitePresentation_restrictPrincipal_of_overPresentation
    (R : CommRingCat.{u}) (M : (Spec R).Modules) (r : R) (U : (Spec R).Opens)
    (h : PrimeSpectrum.basicOpen r ≤ U) (P : (M.over U).Presentation) [P.IsFinite] :
    Module.FinitePresentation (Localization.Away r)
      (moduleSpecΓFunctor.obj (M.restrict (QuasiCoherent.principalOpen R r))) := by
  let t := (Spec R).homOfLE (U := PrimeSpectrum.basicOpen r) (V := U) h
  let j := (basicOpenIsoSpecAway r).inv ≫ t
  let e : restrictFunctor U.ι ⋙ restrictFunctor j ≅
      restrictFunctor (QuasiCoherent.principalOpen R r) :=
    (restrictFunctorComp j U.ι).symm ≪≫
      restrictFunctorCongr (by simp [j, t, basicOpenIsoSpecAway])
  let P₀ := presentationOverToRestrict M U P
  let P₁ := presentationRestrict j P₀
  let P₂ := P₁.ofIsIso (e.app M).hom
  have : P₂.IsFinite := by
    dsimp [P₂, P₁, P₀, presentationRestrict]
    infer_instance
  exact moduleFinitePresentation_of_globalPresentation _ _ P₂

/-- Finite local presentations of an actual affine module sheaf imply finite
presentation of its actual global-section module, without Noetherianity. -/
theorem finitePresentation_globalSections (R : CommRingCat.{u})
    (M : (Spec R).Modules) [M.IsFinitePresentation] :
    Module.FinitePresentation R (moduleSpecΓFunctor.obj M) := by
  classical
  obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
  have := hq
  let N := moduleSpecΓFunctor.obj M
  let T : Set R := {r | Module.FinitePresentation (Localization.Away r)
    (QuasiCoherent.restrictionGlobalSections R r N)}
  have hT : Ideal.span T = ⊤ := by
    apply PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mp
    apply top_unique
    intro x hx
    obtain ⟨V, f, ⟨i, ⟨g⟩⟩, hxV⟩ := q.coversTop ⊤ x (by simp)
    have hxi : x ∈ q.X i := (leOfHom g) hxV
    obtain ⟨a, ⟨_, ⟨r, rfl⟩, rfl⟩, hxr, hrU : PrimeSpectrum.basicOpen _ ≤ _⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxi (q.X i).2
    have hr : r ∈ T := by
      have hfin := moduleFinitePresentation_restrictPrincipal_of_overPresentation
        R M r (q.X i) hrU (q.presentation i)
      let e := moduleSpecΓFunctor.mapIso
        ((restrictFunctor (QuasiCoherent.principalOpen R r)).mapIso (asIso M.fromTildeΓ))
      exact Module.FinitePresentation.of_equiv e.symm.toLinearEquiv
    exact Opens.mem_iSup.mpr ⟨r, Opens.mem_iSup.mpr ⟨hr, hxr⟩⟩
  exact Module.FinitePresentation.of_localizationSpan' T hT
    (Rₚ := fun r ↦ Localization.Away r.val)
    (fun r ↦ QuasiCoherent.toRestrictionGlobalSections R r.val N)
    (fun r ↦ r.property)

section FilteredModels

variable {I : Type u} [Category.{u} I] [IsFiltered I]
  (F : I ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)

include hc in
/-- A finitely presented module sheaf on the spectrum of a filtered ring
colimit has an actual finitely presented spectral model above a prescribed
stage, recovered by the native pullback along the specified cocone map. -/
theorem exists_spec_model_above_of_isColimit (i₀ : I)
    (M : (Spec c.pt).Modules) [M.IsFinitePresentation] :
    ∃ (j : I) (_ : i₀ ⟶ j) (N : (Spec (F.obj j)).Modules),
      N.IsFinitePresentation ∧
      Nonempty ((Scheme.Modules.pullback (Spec.map (c.ι.app j))).obj N ≅ M) := by
  have : Module.FinitePresentation c.pt (moduleSpecΓFunctor.obj M) :=
    finitePresentation_globalSections c.pt M
  obtain ⟨j, q, N, hN, hmod, hfp, he⟩ :=
    Module.FinitePresentation.exists_model_above_of_isColimit F c hc i₀
      (moduleSpecΓFunctor.obj M)
  let : AddCommGroup N := hN
  let : Module (F.obj j) N := hmod
  let : Module.FinitePresentation (F.obj j) N := hfp
  let : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra
  let e : c.pt ⊗[F.obj j] N ≃ₗ[c.pt] moduleSpecΓFunctor.obj M := he.some
  let N₀ := ModuleCat.of (F.obj j) N
  let e₀ : (ModuleCat.extendScalars (c.ι.app j).hom).obj N₀ ≅ moduleSpecΓFunctor.obj M :=
    ModuleCat.extendScalarsAlgebraIso (F.obj j) c.pt N₀ ≪≫ e.toModuleIso
  refine ⟨j, q, tilde N₀, finitePresentation_tilde_of_moduleFinitePresentation _ N₀, ?_⟩
  exact ⟨(tildePullbackIso (c.ι.app j)).app N₀ ≪≫
    (tilde.functor c.pt).mapIso e₀ ≪≫ asIso M.fromTildeΓ⟩

end FilteredModels

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

/-- An actual finitely presented module sheaf on a cofiltered affine scheme
limit has an actual fp stage model above any prescribed stage. -/
theorem exists_affine_model_above_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (M : c.pt.Modules) [M.IsFinitePresentation] :
    ∃ (j : I) (_ : j ⟶ i₀) (N : (D.obj j).Modules),
      N.IsFinitePresentation ∧ Nonempty ((pullback (c.π.app j)).obj N ≅ M) := by
  have : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  have {i j : I} (q : i ⟶ j) : IsAffineHom (D.map q) := inferInstance
  have (i : I) : CompactSpace (D.obj i) := inferInstance
  have (i : I) : QuasiSeparatedSpace (D.obj i) := inferInstance
  let F := D.op ⋙ Scheme.Γ
  let cΓ := Scheme.Γ.mapCocone c.op
  have hcΓ : IsColimit cΓ := (nonempty_isColimit_Γ_mapCocone D c hc).some
  let M' := (pullback c.pt.isoSpec.inv).obj M
  have : M'.IsFinitePresentation := inferInstance
  obtain ⟨j, q, N, hN, he⟩ := exists_spec_model_above_of_isColimit F cΓ hcΓ (.op i₀) M'
  have : N.IsFinitePresentation := hN
  let e : (pullback (Spec.map ((c.π.app j.unop).appTop))).obj N ≅ M' := he.some
  refine ⟨j.unop, q.unop, (pullback (D.obj j.unop).isoSpec.hom).obj N,
    inferInstance, ?_⟩
  exact ⟨(pullbackComp (c.π.app j.unop) (D.obj j.unop).isoSpec.hom).app N ≪≫
    (pullbackCongr (Scheme.isoSpec_hom_naturality
      (X := c.pt) (Y := D.obj j.unop) (c.π.app j.unop)).symm).app N ≪≫
    ((pullbackComp c.pt.isoSpec.hom (Spec.map ((c.π.app j.unop).appTop))).app N).symm ≪≫
    (pullback c.pt.isoSpec.hom).mapIso e ≪≫
    (pullbackComp c.pt.isoSpec.hom c.pt.isoSpec.inv).app M ≪≫
    (pullbackCongr c.pt.isoSpec.hom_inv_id).app M ≪≫
    (pullbackId c.pt).app M⟩

/-- Actual fp module models on the canonical literal base changes of an
already given affine stage scheme, with its canonical cone projections. -/
theorem exists_model_on_affine_baseChanges
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {j k} (q : j ⟶ k), IsAffineHom (D.map q)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    {X : Scheme.{u}} [IsAffine X] (f : X ⟶ D.obj i)
    (M : (Limits.pullback (c.π.app i) f).Modules) [M.IsFinitePresentation] :
    ∃ (j : Over i) (N : ((Scheme.baseChangeDiagram D i f).obj j).Modules),
      N.IsFinitePresentation ∧
      Nonempty ((pullback ((Scheme.baseChangeCone D c i f).π.app j)).obj N ≅ M) := by
  have (j : Over i) : IsAffine ((Scheme.baseChangeDiagram D i f).obj j) := by
    change IsAffine (Limits.pullback (D.map j.hom) f)
    exact isAffine_of_isAffineHom (Limits.pullback.snd (D.map j.hom) f)
  obtain ⟨j, _, N, hN, he⟩ := exists_affine_model_above_of_isLimit
    (Scheme.baseChangeDiagram D i f) (Scheme.baseChangeCone D c i f)
    (Scheme.isLimitBaseChangeCone D c hc i f) (Over.mk (𝟙 i)) M
  exact ⟨j, N, hN, he⟩

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

/-- The existing actual module-sheaf gluing construction preserves finite
presentation on a covering family of open immersions. -/
theorem finitePresentation_glued_of_openCover
    {S : Scheme.{u}} {V : Type u} {X : V → Scheme.{u}}
    (f : ∀ i, X i ⟶ S) [∀ i, IsOpenImmersion (f i)]
    (hcover : IsOpenCover (fun i ↦ (f i).opensRange))
    (D : pullbackPseudofunctor.{u}.DescentData f)
    (hfinite : ∀ i, (D.obj i).IsFinitePresentation) :
    (OpenCoverGluing.glued f D).IsFinitePresentation := by
  let G := OpenCoverGluing.glued f D
  apply finitePresentation_of_openCover G (fun i ↦ (f i).opensRange) hcover
  intro i
  have : IsIso (OpenCoverGluing.toObj f D i) :=
    OpenCoverGluing.isIso_toObj f D i (projectionSurjective S V X f D i)
  let e : (pullback (f i)).obj G ≅ D.obj i :=
    ((restrictFunctorIsoPullback (f i)).app G).symm ≪≫
      asIso (OpenCoverGluing.toObj f D i)
  have : ((pullback (f i)).obj G).IsFinitePresentation :=
    (finitePresentation_iff_of_iso e).mpr (hfinite i)
  exact (finitePresentation_iff_of_iso (restrictOpensRangeIso (f i) G)).mpr inferInstance

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

private theorem lift_map_through_comparison
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    (A₀ : C₀ ⥤ D₀) (A₁ : C₁ ⥤ D₁) (A₂ : C₂ ⥤ D₂)
    (F₀ : C₀ ⥤ C₂) (F₁ : C₀ ⥤ C₁) (G : C₁ ⥤ C₂)
    (H₀ : D₀ ⥤ D₂) (H₁ : D₀ ⥤ D₁) (K : D₁ ⥤ D₂)
    (u : F₀ ≅ F₁ ⋙ G) (U : H₀ ≅ H₁ ⋙ K)
    (β₀ : A₀ ⋙ H₀ ≅ F₀ ⋙ A₂) (β₁ : A₀ ⋙ H₁ ≅ F₁ ⋙ A₁)
    (β₂ : A₁ ⋙ K ≅ G ⋙ A₂)
    (hcoh : ∀ P, U.hom.app (A₀.obj P) ≫ K.map (β₁.hom.app P) ≫
      β₂.hom.app (F₁.obj P) = β₀.hom.app P ≫ A₂.map (u.hom.app P))
    (P Q : C₀) (f : H₀.obj (A₀.obj P) ⟶ H₀.obj (A₀.obj Q))
    (fM : F₀.obj P ⟶ F₀.obj Q)
    (hfM : A₂.map fM = β₀.inv.app P ≫ f ≫ β₀.hom.app Q)
    (gM : F₁.obj P ⟶ F₁.obj Q)
    (hgM : u.hom.app P ≫ G.map gM = fM ≫ u.hom.app Q) :
    U.hom.app (A₀.obj P) ≫
        K.map (β₁.hom.app P ≫ A₁.map gM ≫ β₁.inv.app Q) =
      f ≫ U.hom.app (A₀.obj Q) := by
  have hcancel : K.map (β₁.inv.app Q) ≫ K.map (β₁.hom.app Q) ≫
      β₂.hom.app (F₁.obj Q) = β₂.hom.app (F₁.obj Q) := by
    rw [← K.map_comp_assoc, β₁.inv_hom_id_app]
    simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  have hnat : K.map (A₁.map gM) ≫ β₂.hom.app (F₁.obj Q) =
      β₂.hom.app (F₁.obj P) ≫ A₂.map (G.map gM) :=
    β₂.hom.naturality gM
  apply (cancel_mono (K.map (β₁.hom.app Q) ≫ β₂.hom.app (F₁.obj Q))).mp
  calc
    (U.hom.app (A₀.obj P) ≫
        K.map (β₁.hom.app P ≫ A₁.map gM ≫ β₁.inv.app Q)) ≫
        (K.map (β₁.hom.app Q) ≫ β₂.hom.app (F₁.obj Q)) =
      U.hom.app (A₀.obj P) ≫ K.map (β₁.hom.app P) ≫
        K.map (A₁.map gM) ≫ β₂.hom.app (F₁.obj Q) := by
      simp only [Functor.map_comp, Category.assoc, hcancel]
    _ = (U.hom.app (A₀.obj P) ≫ K.map (β₁.hom.app P) ≫
        β₂.hom.app (F₁.obj P)) ≫ A₂.map (G.map gM) := by
      rw [hnat]
      simp only [Category.assoc]
    _ = β₀.hom.app P ≫ A₂.map (u.hom.app P) ≫ A₂.map (G.map gM) := by
      rw [hcoh]
      simp only [Category.assoc]
    _ = β₀.hom.app P ≫ A₂.map fM ≫ A₂.map (u.hom.app Q) := by
      rw [← Functor.map_comp, hgM, Functor.map_comp]
    _ = f ≫ β₀.hom.app Q ≫ A₂.map (u.hom.app Q) := by
      rw [hfM]
      simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    _ = (f ≫ U.hom.app (A₀.obj Q)) ≫
        (K.map (β₁.hom.app Q) ≫ β₂.hom.app (F₁.obj Q)) := by
      rw [← hcoh]
      simp only [Category.assoc]

private theorem map_eq_iff_of_comparison
    {C D E H : Type*} [Category C] [Category D] [Category E] [Category H]
    (A : C ⥤ D) (B : E ⥤ H) (F : C ⥤ E) (G : D ⥤ H)
    (β : A ⋙ G ≅ F ⋙ B) {P Q : C} (f g : P ⟶ Q) :
    G.map (A.map f) = G.map (A.map g) ↔ B.map (F.map f) = B.map (F.map g) := by
  have hf : G.map (A.map f) ≫ β.hom.app Q = β.hom.app P ≫ B.map (F.map f) :=
    β.hom.naturality f
  have hg : G.map (A.map g) ≫ β.hom.app Q = β.hom.app P ≫ B.map (F.map g) :=
    β.hom.naturality g
  constructor
  · intro h
    apply (cancel_epi (β.hom.app P)).mp
    rw [← hf, ← hg, h]
  · intro h
    apply (cancel_mono (β.hom.app Q)).mp
    rw [hf, hg, h]

private theorem exists_finitePresentation_tilde_iso (R : CommRingCat.{u})
    (M : (Spec R).Modules) [M.IsFinitePresentation] :
    ∃ P : ModuleCat.{u} R, Module.FinitePresentation R P ∧
      Nonempty ((tilde.functor R).obj P ≅ M) := by
  have : IsIso ((tilde.adjunction (R := R)).counit.app M) :=
    inferInstanceAs (IsIso M.fromTildeΓ)
  exact ⟨moduleSpecΓFunctor.obj M, finitePresentation_globalSections R M,
    ⟨asIso ((tilde.adjunction (R := R)).counit.app M)⟩⟩

variable {R S T : CommRingCat.{u}}

/-- Native pullback composition for the original spectrum maps in a
specified actual commuting scalar triangle. -/
def specPullbackCompOfEq (φ : R ⟶ S) (ψ : S ⟶ T) (ρ : R ⟶ T) (h : φ ≫ ψ = ρ) :
    pullback (Spec.map ρ) ≅ pullback (Spec.map φ) ⋙ pullback (Spec.map ψ) :=
  eqToIso (congrArg (fun q : R ⟶ T ↦ pullback (Spec.map q)) h.symm) ≪≫
    pullbackCongr (Spec.map_comp φ ψ) ≪≫
    (pullbackComp (Spec.map ψ) (Spec.map φ)).symm

/-- The native tilde/pullback comparison retains the original scalar
triangle and its actual pullback-composition map. -/
theorem tildePullbackIso_triangle_hom
    (φ : R ⟶ S) (ψ : S ⟶ T) (ρ : R ⟶ T) (h : φ ≫ ψ = ρ) (P : ModuleCat.{u} R) :
    (specPullbackCompOfEq φ ψ ρ h).hom.app ((tilde.functor R).obj P) ≫
        (pullback (Spec.map ψ)).map ((tildePullbackIso φ).hom.app P) ≫
        (tildePullbackIso ψ).hom.app ((ModuleCat.extendScalars φ.hom).obj P) =
      (tildePullbackIso ρ).hom.app P ≫
        (tilde.functor T).map ((ModuleCat.extendScalarsCompOfEq φ.hom ψ.hom ρ.hom
          (by rw [← h]; rfl)).hom.app P) := by
  subst ρ
  simpa only [specPullbackCompOfEq, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    ModuleCat.extendScalarsCompOfEq, eqToIso_refl, Iso.refl_trans, NatTrans.comp_app,
    Category.assoc] using
    tildePullbackIso_comp_hom_app φ ψ (Spec.map_comp φ ψ) P

variable {I : Type u} [Category.{u} I]
  (F : I ⥤ CommRingCat.{u}) (c : Cocone F)

/-- Native pullback composition for the original filtered ring cocone and
one actual stage transition, after applying spectrum. -/
def pullbackSpecCoconeCompIso {i j : I} (q : i ⟶ j) :
    pullback (Spec.map (c.ι.app i)) ≅
      pullback (Spec.map (F.map q)) ⋙ pullback (Spec.map (c.ι.app j)) :=
  specPullbackCompOfEq (F.map q) (c.ι.app j) (c.ι.app i) (c.w q)

private theorem tildePullbackIso_cocone_hom {i j : I} (q : i ⟶ j)
    (P : ModuleCat.{u} (F.obj i)) :
    (pullbackSpecCoconeCompIso F c q).hom.app ((tilde.functor (F.obj i)).obj P) ≫
        (pullback (Spec.map (c.ι.app j))).map ((tildePullbackIso (F.map q)).hom.app P) ≫
        (tildePullbackIso (c.ι.app j)).hom.app
          ((ModuleCat.extendScalars (F.map q).hom).obj P) =
      (tildePullbackIso (c.ι.app i)).hom.app P ≫
        (tilde.functor c.pt).map ((ModuleCat.extendScalarsCoconeCompIso F c q).hom.app P) :=
  tildePullbackIso_triangle_hom (F.map q) (c.ι.app j) (c.ι.app i) (c.w q) P

variable [IsFiltered I] (hc : IsColimit c)

include hc in
private theorem exists_tilde_hom_above_of_isColimit (i : I)
    (P Q : ModuleCat.{u} (F.obj i))
    [Module.FinitePresentation (F.obj i) P] [Module.FinitePresentation (F.obj i) Q]
    (f : (pullback (Spec.map (c.ι.app i))).obj ((tilde.functor (F.obj i)).obj P) ⟶
      (pullback (Spec.map (c.ι.app i))).obj ((tilde.functor (F.obj i)).obj Q)) :
    ∃ (j : I) (q : i ⟶ j)
      (g : (pullback (Spec.map (F.map q))).obj ((tilde.functor (F.obj i)).obj P) ⟶
        (pullback (Spec.map (F.map q))).obj ((tilde.functor (F.obj i)).obj Q)),
      (pullbackSpecCoconeCompIso F c q).hom.app ((tilde.functor (F.obj i)).obj P) ≫
          (pullback (Spec.map (c.ι.app j))).map g =
        f ≫ (pullbackSpecCoconeCompIso F c q).hom.app ((tilde.functor (F.obj i)).obj Q) := by
  let ρ : F.obj i ⟶ c.pt := c.ι.app i
  let βρ := tildePullbackIso (R := F.obj i) (S := c.pt) ρ
  let f₀ := βρ.inv.app P ≫ f ≫ βρ.hom.app Q
  let fM := (tilde.functor c.pt).preimage f₀
  have hfM : (tilde.functor c.pt).map fM = f₀ := (tilde.functor c.pt).map_preimage f₀
  obtain ⟨j, q, gM, hgM⟩ := ModuleCat.exists_hom_above_of_isColimit F c hc i P Q fM
  let φ : F.obj i ⟶ F.obj j := F.map q
  let ψ : F.obj j ⟶ c.pt := c.ι.app j
  let βφ := tildePullbackIso (R := F.obj i) (S := F.obj j) φ
  let βψ := tildePullbackIso (R := F.obj j) (S := c.pt) ψ
  refine ⟨j, q, βφ.hom.app P ≫ (tilde.functor (F.obj j)).map gM ≫ βφ.inv.app Q, ?_⟩
  exact lift_map_through_comparison
    (tilde.functor (F.obj i)) (tilde.functor (F.obj j)) (tilde.functor c.pt)
    (ModuleCat.extendScalars ρ.hom) (ModuleCat.extendScalars φ.hom)
    (ModuleCat.extendScalars ψ.hom)
    (pullback (Spec.map ρ)) (pullback (Spec.map φ)) (pullback (Spec.map ψ))
    (ModuleCat.extendScalarsCoconeCompIso F c q) (pullbackSpecCoconeCompIso F c q)
    βρ βφ βψ (tildePullbackIso_cocone_hom F c q) P Q f fM hfM gM hgM

include hc in
/-- An actual map between colimit pullbacks of two given fp module sheaves
on a stage spectrum descends with its original native pullback square. -/
theorem exists_spec_hom_above_of_isColimit (i : I)
    (M N : (Spec (F.obj i)).Modules) [M.IsFinitePresentation] [N.IsFinitePresentation]
    (f : (pullback (Spec.map (c.ι.app i))).obj M ⟶
      (pullback (Spec.map (c.ι.app i))).obj N) :
    ∃ (j : I) (q : i ⟶ j)
      (g : (pullback (Spec.map (F.map q))).obj M ⟶
        (pullback (Spec.map (F.map q))).obj N),
      (pullbackSpecCoconeCompIso F c q).hom.app M ≫
          (pullback (Spec.map (c.ι.app j))).map g =
        f ≫ (pullbackSpecCoconeCompIso F c q).hom.app N := by
  obtain ⟨P, hP, ⟨eM⟩⟩ := exists_finitePresentation_tilde_iso (F.obj i) M
  obtain ⟨Q, hQ, ⟨eN⟩⟩ := exists_finitePresentation_tilde_iso (F.obj i) N
  have : Module.FinitePresentation (F.obj i) P := hP
  have : Module.FinitePresentation (F.obj i) Q := hQ
  let F₀ := pullback (Spec.map (c.ι.app i))
  let f₀ := F₀.map eM.hom ≫ f ≫ F₀.map eN.inv
  obtain ⟨j, q, g₀, hg₀⟩ := exists_tilde_hom_above_of_isColimit F c hc i P Q f₀
  let Fⱼ := pullback (Spec.map (F.map q))
  let G := pullback (Spec.map (c.ι.app j))
  refine ⟨j, q, Fⱼ.map eM.inv ≫ g₀ ≫ Fⱼ.map eN.hom, ?_⟩
  exact CategoryTheory.NatIso.hom_lift_transport F₀ Fⱼ G
    (pullbackSpecCoconeCompIso F c q) eM eN f g₀ hg₀

include hc in
private theorem exists_tilde_hom_equality_above_of_isColimit (i : I)
    (P Q : ModuleCat.{u} (F.obj i))
    [Module.FinitePresentation (F.obj i) P] [Module.FinitePresentation (F.obj i) Q]
    (f g : (tilde.functor (F.obj i)).obj P ⟶ (tilde.functor (F.obj i)).obj Q)
    (h : (pullback (Spec.map (c.ι.app i))).map f =
      (pullback (Spec.map (c.ι.app i))).map g) :
    ∃ (j : I) (q : i ⟶ j),
      (pullback (Spec.map (F.map q))).map f = (pullback (Spec.map (F.map q))).map g := by
  let fM := (tilde.functor (F.obj i)).preimage f
  let gM := (tilde.functor (F.obj i)).preimage g
  have hfM : (tilde.functor (F.obj i)).map fM = f := (tilde.functor (F.obj i)).map_preimage f
  have hgM : (tilde.functor (F.obj i)).map gM = g := (tilde.functor (F.obj i)).map_preimage g
  let ρ : F.obj i ⟶ c.pt := c.ι.app i
  let Eρ := ModuleCat.extendScalars ρ.hom
  let PBρ := pullback (Spec.map ρ)
  let βρ := tildePullbackIso (R := F.obj i) (S := c.pt) ρ
  have hmodule : Eρ.map fM = Eρ.map gM := by
    apply (tilde.functor c.pt).map_injective
    apply (map_eq_iff_of_comparison (tilde.functor (F.obj i)) (tilde.functor c.pt)
      Eρ PBρ βρ fM gM).mp
    rw [hfM, hgM]
    exact h
  obtain ⟨j, q, hq⟩ := ModuleCat.exists_hom_equality_above_of_isColimit F c hc i P Q fM gM hmodule
  refine ⟨j, q, ?_⟩
  let φ : F.obj i ⟶ F.obj j := F.map q
  let Eφ := ModuleCat.extendScalars φ.hom
  let PBφ := pullback (Spec.map φ)
  let βφ := tildePullbackIso (R := F.obj i) (S := F.obj j) φ
  have hh := (map_eq_iff_of_comparison (tilde.functor (F.obj i)) (tilde.functor (F.obj j))
    Eφ PBφ βφ fM gM).mpr (congrArg (tilde.functor (F.obj j)).map hq)
  rw [hfM, hgM] at hh
  exact hh

include hc in
/-- Equality of two original fp sheaf maps on a stage spectrum holds after
one later pullback whenever it holds after the actual colimit pullback. -/
theorem exists_spec_hom_equality_above_of_isColimit (i : I)
    (M N : (Spec (F.obj i)).Modules) [M.IsFinitePresentation] [N.IsFinitePresentation]
    (f g : M ⟶ N)
    (h : (pullback (Spec.map (c.ι.app i))).map f =
      (pullback (Spec.map (c.ι.app i))).map g) :
    ∃ (j : I) (q : i ⟶ j),
      (pullback (Spec.map (F.map q))).map f = (pullback (Spec.map (F.map q))).map g := by
  obtain ⟨P, hP, ⟨eM⟩⟩ := exists_finitePresentation_tilde_iso (F.obj i) M
  obtain ⟨Q, hQ, ⟨eN⟩⟩ := exists_finitePresentation_tilde_iso (F.obj i) N
  have : Module.FinitePresentation (F.obj i) P := hP
  have : Module.FinitePresentation (F.obj i) Q := hQ
  let f₀ := eM.hom ≫ f ≫ eN.inv
  let g₀ := eM.hom ≫ g ≫ eN.inv
  have h₀ : (pullback (Spec.map (c.ι.app i))).map f₀ =
      (pullback (Spec.map (c.ι.app i))).map g₀ := by
    simp only [f₀, g₀, Functor.map_comp, h]
  obtain ⟨j, q, hq⟩ := exists_tilde_hom_equality_above_of_isColimit F c hc i P Q f₀ g₀ h₀
  refine ⟨j, q, ?_⟩
  apply (cancel_epi ((pullback (Spec.map (F.map q))).map eM.hom)).mp
  apply (cancel_mono ((pullback (Spec.map (F.map q))).map eN.inv)).mp
  simpa only [f₀, g₀, Functor.map_comp, Category.assoc] using hq

end AlgebraicGeometry.Scheme.Modules
