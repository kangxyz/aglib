/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Line.Sections
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.LocalSplitting
public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.AlgebraicGeometry.RelativeGluing

/-!
# The projective bundle of an extension of the structure module by itself

Local frames are original sections mapping to one under the original quotient.
Exactness and injectivity of the original inclusion determine their transition
scalars. The unipotent matrices of these scalars glue the existing native
projective lines, with their original cartesian charts and proper projections.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace Matrix

universe u

namespace AlgebraicGeometry.Scheme.ProjectiveBundle.RankTwoExtension

open Scheme.Modules Scheme.ProjectiveLine

variable {X : Scheme.{u}} {E : X.Modules}

/-- The actual short complex of the supplied extension maps. -/
abbrev extensionComplex (i : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ E)
    (g : E ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (hig : i ≫ g = 0) : ShortComplex X.Modules := ShortComplex.mk i g hig

/-- An affine chart together with an original section lifting one in the quotient. -/
structure AffineFrame (g : E ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules)) where
  /-- The original affine open of the base. -/
  U : X.affineOpens
  /-- The chosen original lift of the quotient generator. -/
  lift : Γ(E, U.1)
  /-- The lift maps to the original unit section. -/
  quotient_lift : g.app U.1 lift = (1 : Γ(X, U.1))

instance (g : E ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules)) : Preorder (AffineFrame g) :=
  Preorder.lift (fun b => b.U)

/-- The original affine-open spectrum comparison for a displayed frame. -/
def AffineFrame.isoSpec {g : E ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules)}
    (a : AffineFrame g) : a.U.1.toScheme ≅ Spec Γ(X, a.U.1) :=
  a.U.2.isoSpec

@[simp] theorem AffineFrame.isoSpec_hom
    {g : E ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules)} (a : AffineFrame g) :
    a.isoSpec.hom = a.U.1.toSpecΓ := rfl

/-- The original scalar restriction on the two displayed base opens. -/
abbrev scalarRestriction {U V : X.Opens} (h : U ≤ V) : Γ(X, V) →+* Γ(X, U) :=
  (X.presheaf.map (homOfLE h).op).hom

private theorem res_comp {U V W : X.Opens} (hUV : U ≤ V) (hVW : V ≤ W) :
    (scalarRestriction hUV).comp (scalarRestriction hVW) = scalarRestriction (hUV.trans hVW) := by
  change (X.presheaf.map (homOfLE hVW).op ≫ X.presheaf.map (homOfLE hUV).op).hom = _
  rw [← Functor.map_comp]
  rfl

private theorem module_res_comp (M : X.Modules) {U V W : X.Opens}
    (hUV : U ≤ V) (hVW : V ≤ W) (m : Γ(M, W)) :
    M.presheaf.map (homOfLE hUV).op (M.presheaf.map (homOfLE hVW).op m) =
      M.presheaf.map (homOfLE (hUV.trans hVW)).op m := by
  change (M.presheaf.map (homOfLE hVW).op ≫
    M.presheaf.map (homOfLE hUV).op) m = _
  rw [← Functor.map_comp]
  rfl

private theorem app_res {M N : X.Modules} (φ : M ⟶ N)
    {U V : X.Opens} (h : U ≤ V) (s : Γ(M, V)) :
    φ.app U (M.presheaf.map (homOfLE h).op s) =
      N.presheaf.map (homOfLE h).op (φ.app V s) :=
  ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE h).op) s

/-- Actual quotient frames refine every neighbourhood of the original base. -/
theorem exists_frame_le
    (g : E ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules)) [Epi g]
    (V : X.Opens) (x : X) (hx : x ∈ V) :
    ∃ b : AffineFrame g, x ∈ b.U.1 ∧ b.U.1 ≤ V := by
  obtain ⟨W, hWV, hxW, s, hs⟩ := exists_finite_local_lifts g V
    (fun _ : PUnit.{1} => (1 : Γ(X, V))) x hx
  obtain ⟨U, hU, hxU, hUW⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hxW
  refine ⟨⟨⟨U, hU⟩, E.presheaf.map (homOfLE hUW).op (s PUnit.unit), ?_⟩,
    hxU, hUW.trans hWV⟩
  have hs1 : g.app W (s PUnit.unit) = (1 : Γ(X, W)) := by
    refine (hs PUnit.unit).trans ?_
    change scalarRestriction hWV 1 = 1
    exact map_one _
  rw [app_res, hs1]
  change scalarRestriction hUW 1 = 1
  exact map_one _

/-- The affine opens with actual quotient frames cover the original base. -/
def frameCover (g : E ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules)) [Epi g] :
    X.OpenCover where
  I₀ := AffineFrame g
  X b := b.U.1.toScheme
  f b := b.U.1.ι
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, inferInstance⟩
    obtain ⟨b, hxb, _⟩ := exists_frame_le g ⊤ x (by trivial)
    exact ⟨b, ⟨⟨x, hxb⟩, rfl⟩⟩

instance (g : E ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules)) [Epi g] :
    Preorder (frameCover g).I₀ :=
  inferInstanceAs (Preorder (AffineFrame g))

instance (g : E ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules)) [Epi g] :
    (frameCover g).LocallyDirected :=
  Scheme.Cover.LocallyDirected.ofIsBasisOpensRange (by intros; simp [frameCover]; rfl) (by
    rw [Opens.isBasis_iff_nbhd]
    intro V x hx
    obtain ⟨b, hxb, hbV⟩ := exists_frame_le g V x hx
    refine ⟨b.U.1, ?_, hxb, hbV⟩
    exact ⟨b, by simp [frameCover]⟩)

private theorem frameCover_trans
    (g : E ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules)) [Epi g]
    {a b : AffineFrame g} (h : a ⟶ b) :
    (frameCover g).trans h = X.homOfLE (show a.U.1 ≤ b.U.1 from leOfHom h) := by
  apply (cancel_mono b.U.1.ι).mp
  exact ((frameCover g).trans_map h).trans (X.homOfLE_ι (leOfHom h)).symm

private theorem section_injective
    (i : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ E) [Mono i]
    (U : X.Opens) : Function.Injective (Scheme.Modules.Hom.app i U) :=
  (ModuleCat.mono_iff_injective
    ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map i)).mp inferInstance

private theorem section_kernel_lift (i : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ E)
    (g : E ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules)) (hig : i ≫ g = 0)
    (hS : (extensionComplex i g hig).ShortExact) (U : X.Opens)
    (s : Γ(E, U)) (hs : g.app U s = 0) :
    ∃ t : Γ(X, U), Scheme.Modules.Hom.app i U t = s := by
  let F := SheafOfModules.toSheaf.{u} X.ringCatSheaf
  let : PreservesFiniteLimits F := inferInstanceAs
    (PreservesFiniteLimits (SheafOfModules.toSheaf.{u} X.ringCatSheaf))
  let : PreservesFiniteColimits F := ⟨fun _ => inferInstance⟩
  have h := hS.map_of_exact F
  exact TopCat.Sheaf.sections_exact_of_left_exact (U := U) h.exact h.mono_f s hs

variable (i : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ E)
  (g : E ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
  (hig : i ≫ g = 0) (hS : (extensionComplex i g hig).ShortExact)

include hS in
/-- The original kernel exactness supplies the scalar between two actual local lifts. -/
theorem exists_transition {a b : AffineFrame g} (h : a ≤ b) :
    ∃ t : Γ(X, a.U.1), Scheme.Modules.Hom.app i a.U.1 t =
      E.presheaf.map (homOfLE (show a.U.1 ≤ b.U.1 from h)).op b.lift - a.lift := by
  apply section_kernel_lift i g hig hS
  rw [map_sub, app_res, b.quotient_lift, a.quotient_lift]
  change scalarRestriction (show a.U.1 ≤ b.U.1 from h) 1 - 1 = 0
  simp

/-- The unique original scalar changing the displayed quotient frame. -/
def transition {a b : AffineFrame g} (h : a ≤ b) : Γ(X, a.U.1) :=
  (exists_transition i g hig hS h).choose

/-- The transition scalar is identified through the original inclusion, not an abstract basis. -/
theorem transition_spec {a b : AffineFrame g} (h : a ≤ b) :
    Scheme.Modules.Hom.app i a.U.1 (transition i g hig hS h) =
      E.presheaf.map (homOfLE (show a.U.1 ≤ b.U.1 from h)).op b.lift - a.lift :=
  (exists_transition i g hig hS h).choose_spec

@[simp] theorem transition_self (a : AffineFrame g) :
    transition i g hig hS (le_refl a) = 0 := by
  let := hS.mono_f
  apply section_injective i a.U.1
  rw [transition_spec, map_zero]
  change E.presheaf.map (𝟙 (op a.U.1)) a.lift - a.lift = 0
  simp

/-- Original restriction maps give the additive transition cocycle. -/
theorem transition_comp {a b c : AffineFrame g} (hab : a ≤ b) (hbc : b ≤ c) :
    transition i g hig hS (hab.trans hbc) =
      transition i g hig hS hab +
        scalarRestriction (show a.U.1 ≤ b.U.1 from hab) (transition i g hig hS hbc) := by
  let := hS.mono_f
  apply section_injective i a.U.1
  rw [map_add, transition_spec, transition_spec]
  have hr := app_res i (show a.U.1 ≤ b.U.1 from hab) (transition i g hig hS hbc)
  change Scheme.Modules.Hom.app i a.U.1
      (scalarRestriction (show a.U.1 ≤ b.U.1 from hab) (transition i g hig hS hbc)) =
    E.presheaf.map (homOfLE (show a.U.1 ≤ b.U.1 from hab)).op
      (Scheme.Modules.Hom.app i b.U.1 (transition i g hig hS hbc)) at hr
  rw [hr, transition_spec, map_sub, module_res_comp]
  abel

/-- The original unipotent frame-change matrix, with its single ring-level implementation. -/
abbrev transitionMatrix {R : Type u} [CommRing R] (t : R) :
    Matrix.GeneralLinearGroup (Fin 2) R := Scheme.ProjectiveLine.Sections.translationMatrix R t

private theorem unipotent_zero {R : Type u} [CommRing R] : transitionMatrix (0 : R) = 1 := by
  exact Scheme.ProjectiveLine.Sections.translationMatrix_zero R

private theorem unipotent_add {R : Type u} [CommRing R] (s t : R) :
    transitionMatrix (s + t) = transitionMatrix s * transitionMatrix t := by
  exact Scheme.ProjectiveLine.Sections.translationMatrix_add R s t

private theorem unipotent_map {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (t : R) :
    Matrix.GeneralLinearGroup.map f (transitionMatrix t) = transitionMatrix (f t) := by
  exact Scheme.ProjectiveLine.Sections.translationMatrix_map R f t

/-- The local map retains the original unipotent transition and coefficient restriction. -/
def chartMap {a b : AffineFrame g} (h : a ≤ b) :
    projectiveP1 Γ(X, a.U.1) ⟶ projectiveP1 Γ(X, b.U.1) :=
  LinearChange.matrixMap _ (transitionMatrix (transition i g hig hS h)) ≫
    LinearChange.coefficientMap (scalarRestriction (show a.U.1 ≤ b.U.1 from h))

private theorem chartMap_id (a : AffineFrame g) :
    chartMap i g hig hS (le_refl a) = 𝟙 _ := by
  have hr : scalarRestriction (le_refl a.U.1) = RingHom.id Γ(X, a.U.1) := by
    ext x
    change (X.presheaf.map (𝟙 (op a.U.1))).hom x = x
    simp
  simp only [chartMap, transition_self, unipotent_zero, LinearChange.matrixMap_one,
    hr, LinearChange.coefficientMap_id, Category.id_comp]

private theorem chartMap_comp {a b c : AffineFrame g} (hab : a ≤ b) (hbc : b ≤ c) :
    chartMap i g hig hS hab ≫ chartMap i g hig hS hbc =
      chartMap i g hig hS (hab.trans hbc) := by
  unfold chartMap
  rw [Category.assoc, ← Category.assoc
    (LinearChange.coefficientMap (scalarRestriction (show a.U.1 ≤ b.U.1 from hab))),
    LinearChange.coefficientMap_matrixMap, unipotent_map]
  simp only [Category.assoc]
  rw [← Category.assoc (LinearChange.matrixMap _ _), LinearChange.matrixMap_comp,
    ← unipotent_add, add_comm, ← transition_comp]
  rw [← LinearChange.coefficientMap_comp, res_comp]

/-- The original projective lines and their original frame-change morphisms. -/
def chartFunctor : AffineFrame g ⥤ Scheme.{u} where
  obj a := projectiveP1 Γ(X, a.U.1)
  map h := chartMap i g hig hS (leOfHom h)
  map_id a := by exact chartMap_id i g hig hS a
  map_comp h k := by exact (chartMap_comp i g hig hS (leOfHom h) (leOfHom k)).symm

/-- The original projection of a frame chart to its affine open. -/
def chartProjection (a : AffineFrame g) : projectiveP1 Γ(X, a.U.1) ⟶ a.U.1.toScheme :=
  structureMap Γ(X, a.U.1) ≫ a.isoSpec.inv

private theorem spec_res_inv {a b : AffineFrame g} (h : a ≤ b) :
    Spec.map (CommRingCat.ofHom
      (scalarRestriction (show a.U.1 ≤ b.U.1 from h))) ≫ b.isoSpec.inv =
      a.isoSpec.inv ≫ X.homOfLE h := by
  have hc : a.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
      (scalarRestriction (show a.U.1 ≤ b.U.1 from h))) =
      X.homOfLE h ≫ b.isoSpec.hom :=
    a.U.1.toSpecΓ_SpecMap_presheaf_map b.U.1 h
  apply (cancel_epi a.isoSpec.hom).mp
  rw [← Category.assoc, hc]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]

private theorem chartMap_projection {a b : AffineFrame g} (h : a ≤ b) :
    chartMap i g hig hS h ≫ chartProjection g b =
      chartProjection g a ≫ X.homOfLE h := by
  simp only [chartMap, chartProjection, Category.assoc]
  rw [LinearChange.coefficientMap_over_assoc, LinearChange.matrixMap_over_assoc,
    spec_res_inv]

/-- The displayed chart square is the actual base change along the original open inclusion. -/
theorem chartMap_isPullback {a b : AffineFrame g} (h : a ≤ b) :
    IsPullback (chartMap i g hig hS h) (chartProjection g a)
      (chartProjection g b) (X.homOfLE h) := by
  let M := transitionMatrix (transition i g hig hS h)
  refine (LinearChange.coefficientMap_isPullback
    (scalarRestriction (show a.U.1 ≤ b.U.1 from h))).of_iso
    (LinearChange.matrixIso _ M).symm (Iso.refl _) a.isoSpec.symm b.isoSpec.symm
    ?_ ?_ ?_ ?_
  · change LinearChange.coefficientMap (scalarRestriction (show a.U.1 ≤ b.U.1 from h)) ≫ 𝟙 _ =
      LinearChange.matrixMap _ M⁻¹ ≫
        (LinearChange.matrixMap _ M ≫
          LinearChange.coefficientMap (scalarRestriction (show a.U.1 ≤ b.U.1 from h)))
    rw [← Category.assoc, LinearChange.matrixMap_comp, mul_inv_cancel,
      LinearChange.matrixMap_one]
    simp
  · simp only [Iso.symm_hom, chartProjection, LinearChange.matrixIso,
      LinearChange.matrixMap_over_assoc]
  · simp only [Iso.refl_hom, Iso.symm_hom, chartProjection, Category.id_comp]
  · exact spec_res_inv g h

/-- The relative gluing datum is produced from the original short exact extension. -/
def gluingData :
    letI : Epi g := hS.epi_g
    Scheme.Cover.RelativeGluingData (frameCover g) := by
  letI : Epi g := hS.epi_g
  exact {
    functor := chartFunctor i g hig hS
    natTrans := {
      app := chartProjection g
      naturality := fun {a b} h => by
        change AffineFrame g at a b
        exact (chartMap_projection i g hig hS (leOfHom h)).trans
          (congrArg (fun q => chartProjection g a ≫ q) (frameCover_trans g h).symm) }
    equifibered := fun {a b} h => by
      change AffineFrame g at a b
      change IsPullback (chartMap i g hig hS (leOfHom h))
        (chartProjection g a) (chartProjection g b) ((frameCover g).trans h)
      rw [frameCover_trans]
      exact chartMap_isPullback i g hig hS (leOfHom h) }

/-- The actual scheme glued from the projective-line charts of the given extension. -/
def projectiveBundle : Scheme.{u} :=
  letI : Epi g := hS.epi_g
  (gluingData i g hig hS).glued

/-- The structural projection of the same glued scheme to the original base. -/
def projection : projectiveBundle i g hig hS ⟶ X :=
  letI : Epi g := hS.epi_g
  (gluingData i g hig hS).toBase

/-- Every actual chart projection is proper over its original affine open. -/
instance chartProjection_isProper (a : AffineFrame g) : IsProper (chartProjection g a) := by
  unfold chartProjection
  infer_instance

/-- The projection of the actual glued bundle is proper, by locality on the original base. -/
instance projection_isProper : IsProper (projection i g hig hS) := by
  let : Epi g := hS.epi_g
  let D := gluingData i g hig hS
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsProper) (frameCover g)
  intro a
  change IsProper (pullback.snd D.toBase ((frameCover g).f a))
  apply (MorphismProperty.cancel_left_of_respectsIso (@IsProper)
    (D.isPullback_natTrans_ι_toBase a).flip.isoPullback.hom _).1
  rw [IsPullback.isoPullback_hom_snd]
  change IsProper (chartProjection g a)
  infer_instance

/-- The original colimit chart inclusion of the constructed bundle. -/
def chartInclusion (a : AffineFrame g) :
    projectiveP1 Γ(X, a.U.1) ⟶ projectiveBundle i g hig hS :=
  letI : Epi g := hS.epi_g
  colimit.ι (gluingData i g hig hS).functor a

/-- The original chart transition composes to the original colimit inclusion. -/
@[reassoc] theorem chartMap_chartInclusion {a b : AffineFrame g} (h : a ≤ b) :
    chartMap i g hig hS h ≫ chartInclusion i g hig hS b = chartInclusion i g hig hS a := by
  let : Epi g := hS.epi_g
  exact colimit.w (gluingData i g hig hS).functor (homOfLE h)

/-- The chart inclusion is the actual open immersion supplied by relative gluing. -/
instance chartInclusion_isOpenImmersion (a : AffineFrame g) :
    IsOpenImmersion (chartInclusion i g hig hS a) := by
  let : Epi g := hS.epi_g
  change IsOpenImmersion ((gluingData i g hig hS).cover.f a)
  infer_instance

/-- The original affine chart retains its exact projection triangle. -/
@[reassoc] theorem chartInclusion_projection (a : AffineFrame g) :
    chartInclusion i g hig hS a ≫ projection i g hig hS =
      chartProjection g a ≫ a.U.1.ι := by
  let : Epi g := hS.epi_g
  exact (gluingData i g hig hS).ι_toBase a

/-- Each original projective-line chart is the actual base change of the constructed projection. -/
theorem chartInclusion_isPullback (a : AffineFrame g) :
    IsPullback (chartInclusion i g hig hS a) (chartProjection g a)
      (projection i g hig hS) a.U.1.ι := by
  let : Epi g := hS.epi_g
  exact ((gluingData i g hig hS).isPullback_natTrans_ι_toBase a).flip

/-- The original quotient map is the literal infinity section in each original frame. -/
def localQuotientSection (a : AffineFrame g) :
    a.U.1.toScheme ⟶ projectiveP1 Γ(X, a.U.1) :=
  a.isoSpec.hom ≫ Scheme.ProjectiveLine.Sections.infinity Γ(X, a.U.1)

private theorem localQuotientSection_projection (a : AffineFrame g) :
    localQuotientSection g a ≫ chartProjection g a = 𝟙 _ := by
  simp only [localQuotientSection, chartProjection, Category.assoc,
    Scheme.ProjectiveLine.Sections.infinity_over_assoc, Iso.hom_inv_id]

private theorem localQuotientSection_compatible {a b : AffineFrame g} (h : a ≤ b) :
    localQuotientSection g a ≫ chartMap i g hig hS h =
      X.homOfLE (show a.U.1 ≤ b.U.1 from h) ≫ localQuotientSection g b := by
  have hc : a.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
      (scalarRestriction (show a.U.1 ≤ b.U.1 from h))) =
      X.homOfLE h ≫ b.isoSpec.hom :=
    a.U.1.toSpecΓ_SpecMap_presheaf_map b.U.1 h
  simp only [localQuotientSection, chartMap, transitionMatrix, Category.assoc]
  rw [Scheme.ProjectiveLine.Sections.infinity_translation_assoc,
    Scheme.ProjectiveLine.Sections.infinity_coefficient, ← Category.assoc, hc, Category.assoc]

/-- The original quotient chart maps satisfy the actual directed-cover matching equation. -/
theorem localQuotientSection_coverCompatible [Epi g]
    {a b : AffineFrame g} (h : a ⟶ b) :
    (frameCover g).trans h ≫
      (localQuotientSection g b ≫ chartInclusion i g hig hS b) =
      localQuotientSection g a ≫ chartInclusion i g hig hS a := by
  calc
    (frameCover g).trans h ≫
        (localQuotientSection g b ≫ chartInclusion i g hig hS b) =
        (X.homOfLE (show a.U.1 ≤ b.U.1 from leOfHom h) ≫ localQuotientSection g b) ≫
          chartInclusion i g hig hS b := by
      rw [frameCover_trans]
      exact (Category.assoc _ _ _).symm
    _ = (localQuotientSection g a ≫ chartMap i g hig hS (leOfHom h)) ≫
        chartInclusion i g hig hS b := by
      rw [localQuotientSection_compatible]
    _ = localQuotientSection g a ≫ chartInclusion i g hig hS a := by
      rw [Category.assoc]
      congr 1
      exact chartMap_chartInclusion i g hig hS (leOfHom h)

/-- The section glued from the original quotient map of the extension. -/
def quotientSection : X ⟶ projectiveBundle i g hig hS := by
  letI : Epi g := hS.epi_g
  exact (frameCover g).glueMorphismsOfLocallyDirected
    (fun a => localQuotientSection g a ≫ chartInclusion i g hig hS a)
    (fun {_ _} h => localQuotientSection_coverCompatible i g hig hS h)

/-- The canonical quotient section has the original literal morphism on every frame. -/
@[reassoc] theorem quotientSection_chart (a : AffineFrame g) :
    a.U.1.ι ≫ quotientSection i g hig hS =
      localQuotientSection g a ≫ chartInclusion i g hig hS a := by
  let : Epi g := hS.epi_g
  exact (frameCover g).map_glueMorphismsOfLocallyDirected
    (fun a => localQuotientSection g a ≫ chartInclusion i g hig hS a)
    (fun {_ _} h => localQuotientSection_coverCompatible i g hig hS h) a

/-- The canonical quotient section retains the original base triangle. -/
@[reassoc] theorem quotientSection_projection :
    quotientSection i g hig hS ≫ projection i g hig hS = 𝟙 X := by
  let : Epi g := hS.epi_g
  apply (frameCover g).hom_ext
  intro a
  change a.U.1.ι ≫ (quotientSection i g hig hS ≫ projection i g hig hS) = a.U.1.ι ≫ 𝟙 X
  rw [← Category.assoc, quotientSection_chart, Category.assoc, chartInclusion_projection,
    ← Category.assoc, localQuotientSection_projection, Category.id_comp, Category.comp_id]

/-- The original quotient section is a closed immersion into the actual proper bundle. -/
instance quotientSection_isClosedImmersion : IsClosedImmersion (quotientSection i g hig hS) := by
  have : IsClosedImmersion (quotientSection i g hig hS ≫ projection i g hig hS) := by
    rw [quotientSection_projection]
    infer_instance
  exact IsClosedImmersion.of_comp (quotientSection i g hig hS) (projection i g hig hS)


/-- The original quotient section square on every frame is cartesian. -/
theorem quotientSection_chart_isPullback (a : AffineFrame g) :
    IsPullback a.U.1.ι (localQuotientSection g a)
      (quotientSection i g hig hS) (chartInclusion i g hig hS a) := by
  have hlocal : localQuotientSection g a ≫ chartProjection g a = 𝟙 _ := by
    simp only [localQuotientSection, chartProjection, Category.assoc,
      Scheme.ProjectiveLine.Sections.infinity_over_assoc, Iso.hom_inv_id]
  have houter : IsPullback (localQuotientSection g a ≫ chartProjection g a)
      a.U.1.ι a.U.1.ι (quotientSection i g hig hS ≫ projection i g hig hS) := by
    rw [hlocal, quotientSection_projection]
    exact IsPullback.id_horiz a.U.1.ι
  exact (IsPullback.of_right houter (quotientSection_chart i g hig hS a).symm
    (chartInclusion_isPullback i g hig hS a).flip).flip

end AlgebraicGeometry.Scheme.ProjectiveBundle.RankTwoExtension
