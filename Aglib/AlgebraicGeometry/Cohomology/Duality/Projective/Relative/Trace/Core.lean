/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Trace.AffineLocal
/-!
# The original normalized relative projective trace
For a supplied Cartesian polynomial projective space over a separated scheme, the
original affine residue trace glues as an ordinary top higher-direct-image morphism.
The native upper bound and top-Hom equivalence lift that morphism to the actual
bounded-below derived direct image followed by its full-category inclusion.
All coefficient and open comparisons are the original ones. Quasicoherent coefficients
are arbitrary; no Noetherianity or coefficient flatness is assumed.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- Check the long native component conversions sequentially to bound peak memory.
set_option Elab.async false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Differentials
open AlgebraicGeometry.Scheme.Cohomology.RelativeProjectiveTrace
universe u
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Cohomology.projectiveCoefficientTraceTarget
namespace AlgebraicGeometry.Scheme.Cohomology
variable (R : Type u) [CommRing R] (ι : Type u)
  {X Y : Scheme.{u}} (a : X ⟶ ProjectiveSpace R ι) (p : X ⟶ Y)
  (f : Y ⟶ Spec (.of R)) (h : IsPullback a p (toSpec R ι) f)
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem relativeAffineTraceLocal_square
    (n : ℕ) (e : ι ≃ Fin (n + 1)) {A : CommRingCat.{u}} {W : Scheme.{u}}
    (i : W ⟶ X) (q : W ⟶ Spec A) (j : Spec A ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion j] (H : IsPullback i q p j)
    (N : Y.Modules) [N.IsQuasicoherent] :
    traceLocalHomFactoryEquation
      (relativeTopDifferentialCoefficientsFunctor p n)
      ((Scheme.Modules.pushforward p).rightDerived n) (Modules.restrictFunctor j)
      (relativeTopDifferentialCoefficientsFunctor q n)
      ((Scheme.Modules.pushforward q).rightDerived n)
      (relativeHigherRestrictionIso p i q j H n) N
      (relativeAffineTraceLocal R ι a p f h n e j N)
      (affineRelativeTraceHom (A := (A : Type u)) R ι (i ≫ a) q (j ≫ f)
        (H.paste_horiz h) n e (N.restrict j)) := by
  cases A with
  | of A =>
    let E := H.isoPullback
    let i' := pullback.fst p j
    let q' := pullback.snd p j
    let H' := IsPullback.of_hasPullback p j
    let HE : IsPullback E.inv q' q (𝟙 (Spec (.of A))) :=
      IsPullback.of_horiz_isIso
        ⟨H.isoPullback_inv_snd.trans (Category.comp_id q').symm⟩
    let M := (Modules.restrictFunctor j).obj N
    refine traceCanonicalLocalEquation p i q j H n N _
      (affineRelativeTraceHom (A := (A : Type u)) R ι (i' ≫ a) q' (j ≫ f)
        (H'.paste_horiz h) n e M) _
      (relativeAffineTraceLocal_factored R ι a p f h n e j N) ?_
    have transport {S T : Type _} (Q : S → T → Prop)
        (P : ∀ s t, Q s t → Prop) {s s' : S} {t t' : T}
        (hs : s = s') (ht : t = t') (q : Q s t) (q' : Q s' t')
        (hq : P s t q) : P s' t' q' := by
      cases hs
      cases ht
      exact (congrArg (P s t) (Subsingleton.elim q q')).mp hq
    let P (c : pullback p j ⟶ ProjectiveSpace R ι)
        (g : Spec (.of A) ⟶
          Spec (.of R)) (Hc : IsPullback c q' (toSpec R ι) g) : Prop :=
      compositeTraceRestrictionSquare (𝟭 (Spec (.of A)).Modules)
        (relativeTopDifferentialCoefficientsFunctor q n)
        ((Scheme.Modules.pushforward q).rightDerived n)
        (relativeTopDifferentialCoefficientsFunctor q' n)
        ((Scheme.Modules.pushforward q').rightDerived n) M
        ((identityHigherModelIso q E.inv q' HE n).hom.app M)
        (affineRelativeTraceHom (A := (A : Type u)) R ι (i ≫ a) q (j ≫ f)
          (H.paste_horiz h) n e M)
        (affineRelativeTraceHom (A := (A : Type u)) R ι c q' g Hc n e M)
    have ht₀ : P (E.inv ≫ (i ≫ a))
        ((𝟙 (Spec (.of A))) ≫ (j ≫ f))
        (HE.paste_horiz (H.paste_horiz h)) :=
      affineRelativeTraceHom_identity_equation (A := (A : Type u)) R ι (i ≫ a) q
        (j ≫ f) (H.paste_horiz h) E.inv q' HE n e M
    have hpath : E.inv ≫ (i ≫ a) = i' ≫ a := by
      rw [← Category.assoc, H.isoPullback_inv_fst]
    have ht : P (i' ≫ a) (j ≫ f) (H'.paste_horiz h) :=
      transport (fun c g => IsPullback c q' (toSpec R ι) g) P
        hpath (Category.id_comp (j ≫ f))
        (HE.paste_horiz (H.paste_horiz h)) (H'.paste_horiz h) ht₀
    dsimp -proj only [P, compositeTraceRestrictionSquare, Functor.id_obj,
      Functor.id_map, relativeHigherFunctor, Functor.comp_obj] at ht
    exact ht

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem relativeProjectiveHigherTrace_exists [Y.IsSeparated]
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (N : Y.Modules) [N.IsQuasicoherent] :
    ∃! t : (relativeHigherFunctor p n).obj N ⟶ N,
      ∀ c : AffineTraceChart Y,
        (Modules.restrictFunctor (affineTraceChartMap c)).map t =
          relativeAffineTraceLocal R ι a p f h n e (affineTraceChartMap c) N := by
  apply affineTrace_existsUnique ((relativeHigherFunctor p n).obj N) N
    (fun {A} j _ => relativeAffineTraceLocal R ι a p f h n e j N)
  · intro A B j k _ _
    exact relativeAffineTraceLocal_refine R ι a p f h n e j k N
  · intro A j k _ _ w
    exact relativeAffineTraceLocal_congr R ι a p f h n e w N
/-- The actual top higher-direct-image trace, glued from the original normalized affine traces. -/
@[no_expose]
def relativeProjectiveHigherTrace [Y.IsSeparated] (n : ℕ) (e : ι ≃ Fin (n + 1))
    (N : Y.Modules) [N.IsQuasicoherent] :
    ((Scheme.Modules.pushforward p).rightDerived n).obj
      ((relativeTopDifferentialCoefficientsFunctor p n).obj N) ⟶ N :=
  (relativeProjectiveHigherTrace_exists R ι a p f h n e N).choose
private theorem relativeProjectiveHigherTrace_restrict [Y.IsSeparated]
    (n : ℕ) (e : ι ≃ Fin (n + 1)) {A : CommRingCat.{u}}
    (j : Spec A ⟶ Y) [IsOpenImmersion j] (N : Y.Modules) [N.IsQuasicoherent] :
    (Modules.restrictFunctor j).map (relativeProjectiveHigherTrace R ι a p f h n e N) =
      relativeAffineTraceLocal R ι a p f h n e j N :=
  (relativeProjectiveHigherTrace_exists R ι a p f h n e N).choose_spec.1
    ⟨A, j, inferInstance⟩
/-- The actual higher-image trace preserves every original quasicoherent coefficient map. -/
@[reassoc]
theorem relativeProjectiveHigherTrace_naturality [Y.IsSeparated]
    (n : ℕ) (e : ι ≃ Fin (n + 1)) {N N' : Y.Modules}
    [N.IsQuasicoherent] [N'.IsQuasicoherent] (s : N ⟶ N') :
    ((Scheme.Modules.pushforward p).rightDerived n).map
        ((relativeTopDifferentialCoefficientsFunctor p n).map s) ≫
      relativeProjectiveHigherTrace R ι a p f h n e N' =
        relativeProjectiveHigherTrace R ι a p f h n e N ≫ s := by
  apply affineTraceCharts_hom_ext
  intro c
  simp only [Functor.map_comp, relativeProjectiveHigherTrace_restrict]
  exact relativeAffineTraceLocal_naturality R ι a p f h n e (affineTraceChartMap c) s
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option maxRecDepth 2000 in
-- The native affine model and section objects exceeded recursion depth 1000.
set_option maxHeartbeats 400000 in
-- The original affine model and section component comparison exceeds 200000 heartbeats.
/-- Original affine sections of the global Hn trace have the original polynomial residue trace. -/
theorem relativeProjectiveHigherTrace_affine [Y.IsSeparated]
    (n : ℕ) (e : ι ≃ Fin (n + 1)) {A : CommRingCat.{u}}
    (j : Spec A ⟶ Y) [IsOpenImmersion j] (N : Y.Modules) [N.IsQuasicoherent]
    (x : moduleSpecΓFunctor.obj ((((Scheme.Modules.pushforward p).rightDerived n).obj
      ((relativeTopDifferentialCoefficientsFunctor p n).obj N)).restrict j)) :
    letI : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
    letI := projectiveTopDifferentialCoefficients_isQuasicoherent A ι n e (N.restrict j)
    moduleSpecΓFunctor.map ((Modules.restrictFunctor j).map
      (relativeProjectiveHigherTrace R ι a p f h n e N)) x =
    projectiveAffineDifferentialTraceLinearEquiv A ι n e (N.restrict j)
      (moduleHigherDirectImageAffineSectionsLinearEquiv (toSpec A ι) _ (injectiveResolution _) n
        (moduleSpecΓFunctor.map (relativeProjectiveAffineHigherIso R ι a p f h n j N).hom x)) := by
  cases A with
  | of A =>
    let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
    let := projectiveTopDifferentialCoefficients_isQuasicoherent A ι n e (N.restrict j)
    rw [relativeProjectiveHigherTrace_restrict]
    have hx := relativeAffineTraceLocal_sections R ι a p f h n e j N
    dsimp -proj only [traceLocalSectionsEquation] at hx
    have hx' := hx x
    rw [relativeProjectiveAffineHigherIso_component, relativeAffineHigherNatIso_original]
    rw [affineHigherCompositeFactory_hom] at hx'
    exact hx'
/-- The original normalized trace on the actual derived differential-coefficient image. -/
@[no_expose]
def relativeProjectiveTrace [Y.IsSeparated] (n : ℕ) (e : ι ≃ Fin (n + 1))
    (N : Y.Modules) [N.IsQuasicoherent] :
    DerivedCategory.Plus.ι.obj ((Scheme.Modules.derivedPushforwardPlus p).obj
      ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj
        ((relativeTopDifferentialCoefficientsFunctor p n).obj N))) ⟶
      (DerivedCategory.singleFunctor Y.Modules (n : ℤ)).obj N := by
  let := relativeProjectiveDifferentialCoefficientsDerived_isLE R ι a p f h n e N
  exact (DerivedCategory.homToSingleAddEquiv
    (relativeTopDifferentialCoefficientsDerived p n N) (n : ℤ) N).symm
      (((Scheme.Modules.pushforward p).rightDerivedSingleHomologyIso n).inv.app
        ((relativeTopDifferentialCoefficientsFunctor p n).obj N) ≫
          relativeProjectiveHigherTrace R ι a p f h n e N)
/-- Original top homology of the derived trace is precisely the glued normalized Hn arrow. -/
@[reassoc]
theorem relativeProjectiveTrace_homology [Y.IsSeparated]
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (N : Y.Modules) [N.IsQuasicoherent] :
    (DerivedCategory.homologyFunctor Y.Modules (n : ℤ)).map
        (relativeProjectiveTrace R ι a p f h n e N) ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso Y.Modules (n : ℤ)).hom.app N =
    ((Scheme.Modules.pushforward p).rightDerivedSingleHomologyIso n).inv.app
      ((relativeTopDifferentialCoefficientsFunctor p n).obj N) ≫
        relativeProjectiveHigherTrace R ι a p f h n e N := by
  let := relativeProjectiveDifferentialCoefficientsDerived_isLE R ι a p f h n e N
  exact (DerivedCategory.homToSingleAddEquiv
    (relativeTopDifferentialCoefficientsDerived p n N) (n : ℤ) N).apply_symm_apply _
/-- The derived trace carries the original coefficient map through the original direct image. -/
@[reassoc]
theorem relativeProjectiveTrace_naturality [Y.IsSeparated]
    (n : ℕ) (e : ι ≃ Fin (n + 1)) {N N' : Y.Modules}
    [N.IsQuasicoherent] [N'.IsQuasicoherent] (s : N ⟶ N') :
    DerivedCategory.Plus.ι.map ((Scheme.Modules.derivedPushforwardPlus p).map
      ((DerivedCategory.Plus.singleFunctor X.Modules 0).map
        ((relativeTopDifferentialCoefficientsFunctor p n).map s))) ≫
      relativeProjectiveTrace R ι a p f h n e N' =
    relativeProjectiveTrace R ι a p f h n e N ≫
      (DerivedCategory.singleFunctor Y.Modules (n : ℤ)).map s := by
  let := relativeProjectiveDifferentialCoefficientsDerived_isLE R ι a p f h n e N
  let := relativeProjectiveDifferentialCoefficientsDerived_isLE R ι a p f h n e N'
  apply (DerivedCategory.homToSingleAddEquiv
    (relativeTopDifferentialCoefficientsDerived p n N) (n : ℤ) N').injective
  rw [DerivedCategory.homToSingleAddEquiv_naturality_left,
    DerivedCategory.homToSingleAddEquiv_naturality_right]
  simp only [DerivedCategory.homToSingleAddEquiv_apply, relativeProjectiveTrace_homology]
  change _ ≫ (_ ≫ _) = (_ ≫ _) ≫ s
  have hn := ((Scheme.Modules.pushforward p).rightDerivedSingleHomologyIso n).inv.naturality
    ((relativeTopDifferentialCoefficientsFunctor p n).map s)
  change (DerivedCategory.homologyFunctor Y.Modules (n : ℤ)).map
      (DerivedCategory.Plus.ι.map ((Scheme.Modules.derivedPushforwardPlus p).map
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).map
          ((relativeTopDifferentialCoefficientsFunctor p n).map s)))) ≫
      ((Scheme.Modules.pushforward p).rightDerivedSingleHomologyIso n).inv.app _ =
    ((Scheme.Modules.pushforward p).rightDerivedSingleHomologyIso n).inv.app _ ≫
      ((Scheme.Modules.pushforward p).rightDerived n).map
        ((relativeTopDifferentialCoefficientsFunctor p n).map s) at hn
  rw [← Category.assoc, hn, Category.assoc, relativeProjectiveHigherTrace_naturality]
  exact (Category.assoc _ _ _).symm
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option maxHeartbeats 400000 in
-- The original chart transport and open composition exceeded 200000 heartbeats.
/-- The global Hn trace commutes with the original comparisons on every Cartesian open square. -/
theorem relativeProjectiveHigherTrace_open [Y.IsSeparated]
    (n : ℕ) (e : ι ≃ Fin (n + 1)) {W Z : Scheme.{u}}
    (i : W ⟶ X) (q : W ⟶ Z) (j : Z ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion j] (H : IsPullback i q p j)
    (N : Y.Modules) [N.IsQuasicoherent] :
    letI : Z.IsSeparated := ⟨by rw [← terminal.comp_from j]; infer_instance⟩
    (Scheme.Modules.higherDirectImageOpenRestrictionIso i q p j H n).hom.app
        ((relativeTopDifferentialCoefficientsFunctor p n).obj N) ≫
      ((Scheme.Modules.pushforward q).rightDerived n).map
        ((relativeTopDifferentialCoefficientsRestrictionIso p i q j H.w n).hom.app N) ≫
      relativeProjectiveHigherTrace R ι (i ≫ a) q (j ≫ f) (H.paste_horiz h) n e
        (N.restrict j) =
    (Modules.restrictFunctor j).map (relativeProjectiveHigherTrace R ι a p f h n e N) := by
  let : Z.IsSeparated := ⟨by rw [← terminal.comp_from j]; infer_instance⟩
  rw [← Category.assoc, ← relativeHigherRestrictionIso_hom]
  apply affineTraceCharts_hom_ext
  rintro ⟨A, k, hk⟩
  rcases A with ⟨A⟩
  let : IsOpenImmersion k := hk
  let b := pullback.fst q k
  let r := pullback.snd q k
  let HB := IsPullback.of_hasPullback q k
  let HC := HB.paste_horiz H
  have hzL := relativeAffineTraceLocal_square R ι a p f h n e (b ≫ i) r (k ≫ j) HC N
  have transport {S T : Type _} (Q : S → T → Prop)
      (P : ∀ s t, Q s t → Prop) {s s' : S} {t t' : T}
      (hs : s = s') (ht : t = t') (q : Q s t) (q' : Q s' t')
      (hq : P s t q) : P s' t' q' := by
    cases hs
    cases ht
    exact (congrArg (P s t) (Subsingleton.elim q q')).mp hq
  let P (d : pullback q k ⟶ ProjectiveSpace R ι)
      (g : Spec (.of A) ⟶
        Spec (.of R)) (Hd : IsPullback d r (toSpec R ι) g) : Prop :=
    traceLocalHomFactoryEquation
      (relativeTopDifferentialCoefficientsFunctor q n)
      ((Scheme.Modules.pushforward q).rightDerived n) (Modules.restrictFunctor k)
      (relativeTopDifferentialCoefficientsFunctor r n)
      ((Scheme.Modules.pushforward r).rightDerived n)
      (relativeHigherRestrictionIso q b r k HB n) ((Modules.restrictFunctor j).obj N)
      (relativeAffineTraceLocal R ι (i ≫ a) q (j ≫ f) (H.paste_horiz h) n e k
        ((Modules.restrictFunctor j).obj N))
      (affineRelativeTraceHom (A := A) R ι d r g Hd n e
        ((Modules.restrictFunctor k).obj ((Modules.restrictFunctor j).obj N)))
  have hzK₀ : P (b ≫ (i ≫ a)) (k ≫ (j ≫ f)) (HB.paste_horiz (H.paste_horiz h)) :=
    relativeAffineTraceLocal_factored R ι (i ≫ a) q (j ≫ f) (H.paste_horiz h) n e k
      ((Modules.restrictFunctor j).obj N)
  have hzK : P ((b ≫ i) ≫ a) ((k ≫ j) ≫ f) (HC.paste_horiz h) :=
    transport (fun d g => IsPullback d r (toSpec R ι) g) P
      (Category.assoc b i a).symm (Category.assoc k j f).symm
      (HB.paste_horiz (H.paste_horiz h)) (HC.paste_horiz h) hzK₀
  let : ((Modules.restrictFunctor j ⋙ Modules.restrictFunctor k).obj
      N).IsQuasicoherent := inferInstanceAs ((N.restrict j).restrict k).IsQuasicoherent
  have hn := affineRelativeTraceHom_naturality_equation (A := A) R ι
    ((b ≫ i) ≫ a) r ((k ≫ j) ≫ f) (HC.paste_horiz h) n e
    (N := (Modules.restrictFunctor (k ≫ j)).obj N)
    (N' := (Modules.restrictFunctor k).obj ((Modules.restrictFunctor j).obj N))
    ((restrictFunctorComp k j).hom.app N)
  dsimp -proj only [P, Modules.restrict] at hzK
  dsimp -proj only [Modules.restrict] at hzL
  dsimp -proj only [traceLocalNaturalityEquation, Functor.id_obj, Functor.id_map,
    Functor.comp_obj] at hn
  have hs := traceOpenLocalEquation p i q j H b r k HB n N
    (relativeProjectiveHigherTrace R ι a p f h n e N)
    (relativeAffineTraceLocal R ι a p f h n e (k ≫ j) N)
    (relativeAffineTraceLocal R ι (i ≫ a) q (j ≫ f) (H.paste_horiz h) n e k
      ((Modules.restrictFunctor j).obj N))
    (affineRelativeTraceHom (A := A) R ι ((b ≫ i) ≫ a) r
      ((k ≫ j) ≫ f) (HC.paste_horiz h) n e ((Modules.restrictFunctor (k ≫ j)).obj N))
    (affineRelativeTraceHom (A := A) R ι ((b ≫ i) ≫ a) r
      ((k ≫ j) ≫ f) (HC.paste_horiz h) n e
      ((Modules.restrictFunctor k).obj ((Modules.restrictFunctor j).obj N))) hn
    (relativeProjectiveHigherTrace_restrict R ι a p f h n e (k ≫ j) N) hzL hzK
  simp only [Functor.map_comp, relativeProjectiveHigherTrace_restrict]
  exact hs
/-- The affine normalization of the original full-derived trace uses its actual Hn map. -/
theorem relativeProjectiveTrace_affine [Y.IsSeparated]
    (n : ℕ) (e : ι ≃ Fin (n + 1)) {A : CommRingCat.{u}}
    (j : Spec A ⟶ Y) [IsOpenImmersion j] (N : Y.Modules) [N.IsQuasicoherent]
    (x : moduleSpecΓFunctor.obj ((((Scheme.Modules.pushforward p).rightDerived n).obj
      ((relativeTopDifferentialCoefficientsFunctor p n).obj N)).restrict j)) :
    letI : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
    letI := projectiveTopDifferentialCoefficients_isQuasicoherent A ι n e (N.restrict j)
    moduleSpecΓFunctor.map ((Modules.restrictFunctor j).map
      (((Scheme.Modules.pushforward p).rightDerivedSingleHomologyIso n).hom.app
          ((relativeTopDifferentialCoefficientsFunctor p n).obj N) ≫
        (DerivedCategory.homologyFunctor Y.Modules (n : ℤ)).map
          (relativeProjectiveTrace R ι a p f h n e N) ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso Y.Modules (n : ℤ)).hom.app N)) x =
      projectiveAffineDifferentialTraceLinearEquiv A ι n e (N.restrict j)
        (moduleHigherDirectImageAffineSectionsLinearEquiv (toSpec A ι) _ (injectiveResolution _) n
          (moduleSpecΓFunctor.map
            (relativeProjectiveAffineHigherIso R ι a p f h n j N).hom x)) := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let := projectiveTopDifferentialCoefficients_isQuasicoherent A ι n e (N.restrict j)
  rw [relativeProjectiveTrace_homology]
  simp only [Iso.hom_inv_id_app_assoc]
  exact relativeProjectiveHigherTrace_affine R ι a p f h n e j N x
end AlgebraicGeometry.Scheme.Cohomology
