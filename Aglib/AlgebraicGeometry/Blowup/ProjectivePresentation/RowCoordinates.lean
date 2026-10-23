/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.ProjectivePresentation.AffineRow

/-!
# Original quotient coefficients and framed affine rows

The original tautological quotient is transported along an actual chart square.
Native pullback and tilde maps recover its coefficient map on the full iterated
tensor ideal. The original ideal sections determine every pure-tensor coefficient;
linearity then proves the same original framed row equation. No flatness or
post-scalar-change ideal-inclusion cancellation is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TensorProduct HomogeneousLocalization
open MvPolynomial Opposite
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.ProjectiveSpace.FromSections

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.Scheme.Blowup.ProjectivePresentation.TautologicalPullbackSections

private theorem iso_map_id {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A : C} {B : D} (e : F.obj A ≅ B) :
    e.inv ≫ F.map (𝟙 A) ≫ e.hom = 𝟙 B := by
  rw [F.map_id, Category.id_comp, Iso.inv_hom_id]

private theorem section_paste {C : Type*} [Category C] {U V W E H N : C}
    (a : U ⟶ V) (b : V ⟶ W) (h : W ⟶ E) (t : E ⟶ N)
    (k : W ⟶ H) (l : H ⟶ N) (w : U ⟶ H)
    (hn : h ≫ t = k ≫ l) (hu : a ≫ b ≫ k = w) :
    (a ≫ b ≫ h) ≫ t = w ≫ l := by
  simp only [Category.assoc]
  rw [hn, reassoc_of% hu]

private theorem section_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {M : Z.Modules} (s : SheafOfModules.unit Z.ringCatSheaf ⟶ M) :
    pullbackSection f (pullbackSection g s) ≫ (pullbackComp f g).hom.app M =
      pullbackSection (f ≫ g) s := by
  have hn := (pullbackComp f g).hom.naturality s
  simp only [Functor.comp_map] at hn
  have hu : (pullbackUnitIso f).inv ≫
      (Modules.pullback f).map (pullbackUnitIso g).inv ≫
        (pullbackComp f g).hom.app (SheafOfModules.unit Z.ringCatSheaf) =
      (pullbackUnitIso (f ≫ g)).inv := by
    apply (cancel_mono (pullbackUnitIso (f ≫ g)).hom).mp
    simp only [Category.assoc]
    rw [pullbackUnitIso_comp]
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id]
    exact iso_map_id (Modules.pullback f) (pullbackUnitIso f)
  have hp := section_paste (pullbackUnitIso f).inv
    ((Modules.pullback f).map (pullbackUnitIso g).inv)
    ((Modules.pullback f).map ((Modules.pullback g).map s))
    ((pullbackComp f g).hom.app M)
    ((pullbackComp f g).hom.app (SheafOfModules.unit Z.ringCatSheaf))
    ((Modules.pullback (f ≫ g)).map s) (pullbackUnitIso (f ≫ g)).inv hn hu
  simpa only [pullbackSection, Functor.map_comp, Category.assoc] using hp

private theorem section_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    {M : Y.Modules} (s : SheafOfModules.unit Y.ringCatSheaf ⟶ M) :
    pullbackSection f s ≫ (pullbackCongr h).hom.app M = pullbackSection g s := by
  subst g
  simp [pullbackCongr]

private theorem section_postcomp {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : Y.Modules} (s : SheafOfModules.unit Y.ringCatSheaf ⟶ M) (t : M ⟶ N) :
    pullbackSection f (s ≫ t) = pullbackSection f s ≫ (Modules.pullback f).map t := by
  simp only [pullbackSection, Functor.map_comp, Category.assoc]

variable {X W : Scheme.{u}} {I : X.IdealSheafData} (B : BlowupDatum I) (f : W ⟶ X)

/-- The literal fibre-product quotient transports an original ideal section to the same pulled
tautological section. -/
theorem pulledTautologicalQuotient_section
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ idealModule I.subschemeι) :
    pullbackSection (pullback.snd B.map f) (pullbackSection f s) ≫
      pulledTautologicalQuotient B f =
    pullbackSection (pullback.fst B.map f) (AffineCoordinates.tautologicalSection B s) := by
  simp only [pulledTautologicalQuotient]
  rw [reassoc_of% section_comp (pullback.snd B.map f) f s,
    reassoc_of% section_congr (pullback.condition (f := B.map) (g := f)).symm s,
    ← section_comp (pullback.fst B.map f) B.map s]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  exact (section_postcomp (pullback.fst B.map f) (pullbackSection B.map s)
    (tautologicalQuotient B)).symm

end AlgebraicGeometry.Scheme.Blowup.ProjectivePresentation.TautologicalPullbackSections


namespace AlgebraicGeometry.Scheme.Blowup.ProjectivePresentation.OriginalRowRestriction

private theorem iso_map_id {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A : C} {B : D} (e : F.obj A ≅ B) :
    e.inv ≫ F.map (𝟙 A) ≫ e.hom = 𝟙 B := by
  rw [F.map_id, Category.id_comp, Iso.inv_hom_id]

private theorem section_paste {C : Type*} [Category C] {U V W E H N : C}
    (a : U ⟶ V) (b : V ⟶ W) (h : W ⟶ E) (t : E ⟶ N)
    (k : W ⟶ H) (l : H ⟶ N) (w : U ⟶ H)
    (hn : h ≫ t = k ≫ l) (hu : a ≫ b ≫ k = w) :
    (a ≫ b ≫ h) ≫ t = w ≫ l := by
  simp only [Category.assoc]
  rw [hn, reassoc_of% hu]

private theorem section_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {M : Z.Modules} (s : SheafOfModules.unit Z.ringCatSheaf ⟶ M) :
    pullbackSection f (pullbackSection g s) ≫ (pullbackComp f g).hom.app M =
      pullbackSection (f ≫ g) s := by
  have hn := (pullbackComp f g).hom.naturality s
  simp only [Functor.comp_map] at hn
  have hu : (pullbackUnitIso f).inv ≫
      (Modules.pullback f).map (pullbackUnitIso g).inv ≫
        (pullbackComp f g).hom.app (SheafOfModules.unit Z.ringCatSheaf) =
      (pullbackUnitIso (f ≫ g)).inv := by
    apply (cancel_mono (pullbackUnitIso (f ≫ g)).hom).mp
    simp only [Category.assoc]
    rw [pullbackUnitIso_comp]
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id]
    exact iso_map_id (Modules.pullback f) (pullbackUnitIso f)
  have hp := section_paste (pullbackUnitIso f).inv
    ((Modules.pullback f).map (pullbackUnitIso g).inv)
    ((Modules.pullback f).map ((Modules.pullback g).map s))
    ((pullbackComp f g).hom.app M)
    ((pullbackComp f g).hom.app (SheafOfModules.unit Z.ringCatSheaf))
    ((Modules.pullback (f ≫ g)).map s) (pullbackUnitIso (f ≫ g)).inv hn hu
  simpa only [pullbackSection, Functor.map_comp, Category.assoc] using hp

private theorem section_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    {M : Y.Modules} (s : SheafOfModules.unit Y.ringCatSheaf ⟶ M) :
    pullbackSection f s ≫ (pullbackCongr h).hom.app M = pullbackSection g s := by
  subst g
  simp [pullbackCongr]

private theorem section_postcomp {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : Y.Modules} (s : SheafOfModules.unit Y.ringCatSheaf ⟶ M) (t : M ⟶ N) :
    pullbackSection f (s ≫ t) = pullbackSection f s ≫ (Modules.pullback f).map t := by
  simp only [pullbackSection, Functor.map_comp, Category.assoc]

/-- The original pulled tautological module on the literal affine scalar base change. -/
def affineLine {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] {I : Ideal R}
    (B : BlowupDatum (affineCenter R I)) :
    (pullback B.map (Spec.algebraMap R S)).Modules :=
  (pulledTautologicalLine B (Spec.algebraMap R S)).val

section ChartTransport

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra S T] {I : Ideal R}
  (B : BlowupDatum (affineCenter R I)) (a : I)
  (φ : affineBlowupAlgebra R I a →+* T)


variable (t : Spec (.of T) ⟶ pullback B.map (Spec.algebraMap R S))
  (htp : t ≫ pullback.snd B.map (Spec.algebraMap R S) = Spec.algebraMap S T)
  (hth : t ≫ pullback.fst B.map (Spec.algebraMap R S) =
    Spec.map (CommRingCat.ofHom φ) ≫ IdealFrames.chartMap B a)

private def chartQuotient :
    (Modules.pullback (Spec.algebraMap S T)).obj
        (degreeOneModule (I := affineCenter R I) (Spec.algebraMap R S)) ⟶
      (Modules.pullback t).obj (affineLine (S := S) B) :=
  (pullbackCongr htp.symm).hom.app _ ≫
    (pullbackComp t (pullback.snd B.map (Spec.algebraMap R S))).inv.app _ ≫
      (Modules.pullback t).map (pulledTautologicalQuotient B (Spec.algebraMap R S))

private theorem chartQuotient_section
    (s : SheafOfModules.unit (Spec (.of S)).ringCatSheaf ⟶
      degreeOneModule (I := affineCenter R I) (Spec.algebraMap R S)) :
    pullbackSection (Spec.algebraMap S T) s ≫ chartQuotient B t htp =
      pullbackSection t (pullbackSection (pullback.snd B.map (Spec.algebraMap R S)) s ≫
        pulledTautologicalQuotient B (Spec.algebraMap R S)) := by
  simp only [chartQuotient]
  rw [reassoc_of% section_congr htp.symm s,
    ← section_comp t (pullback.snd B.map (Spec.algebraMap R S)) s]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  exact (section_postcomp t (pullbackSection (pullback.snd B.map (Spec.algebraMap R S)) s)
    (pulledTautologicalQuotient B (Spec.algebraMap R S))).symm

/-- The actual original denominator frame transported through the displayed first projection. -/
def chartFrame :
    (Modules.pullback t).obj (affineLine (S := S) B) ≅
      SheafOfModules.unit (Spec (.of T)).ringCatSheaf :=
  (pullbackComp t (pullback.fst B.map (Spec.algebraMap R S))).app (tautologicalLine B).val ≪≫
    (pullbackCongr hth).app (tautologicalLine B).val ≪≫
      (IdealFrames.chartFrameAfterMap B a T φ).symm

private theorem chartFrame_original_section (b : I) :
    pullbackSection (Spec.algebraMap S T)
        (pullbackSection (Spec.algebraMap R S) (AffineCoordinates.idealSection R I b)) ≫
      chartQuotient B t htp ≫ (chartFrame B a φ t hth).hom =
        IdealFrames.affineMultiplication T (φ (ratio R I a b)) := by
  rw [← Category.assoc, chartQuotient_section,
    TautologicalPullbackSections.pulledTautologicalQuotient_section]
  simp only [chartFrame, Iso.trans_hom, Iso.symm_hom, Iso.app_hom]
  rw [reassoc_of% section_comp t (pullback.fst B.map (Spec.algebraMap R S))
    (AffineCoordinates.tautologicalSection B (AffineCoordinates.idealSection R I b)),
    reassoc_of% section_congr hth
      (AffineCoordinates.tautologicalSection B (AffineCoordinates.idealSection R I b))]
  have hc : pullbackSection (Spec.map (CommRingCat.ofHom φ) ≫ IdealFrames.chartMap B a)
      (AffineCoordinates.tautologicalSection B (AffineCoordinates.idealSection R I b)) =
      AffineCoordinates.chartSectionAfterMap B a b T φ :=
    (section_comp (Spec.map (CommRingCat.ofHom φ)) (IdealFrames.chartMap B a)
      (AffineCoordinates.tautologicalSection B (AffineCoordinates.idealSection R I b))).symm
  rw [hc, AffineCoordinates.chartSectionAfterMap_eq_ratio]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

private def tensorSection (v : S ⊗[R] I) :
    SheafOfModules.unit (Spec (.of S)).ringCatSheaf ⟶
      degreeOneModule (I := affineCenter R I) (Spec.algebraMap R S) :=
  (tildeSelf (R := CommRingCat.of S)).inv ≫
    (tilde.functor (CommRingCat.of S)).map
      (ModuleCat.ofHom (LinearMap.toSpanSingleton S (S ⊗[R] I) v)) ≫
        (AffineRow.tensorIdealIso I S).inv

private theorem tensorSection_one_tmul (b : I) :
    tensorSection (I := I) ((1 : S) ⊗ₜ[R] b) =
      pullbackSection (Spec.algebraMap R S) (AffineCoordinates.idealSection R I b) := by
  apply (cancel_mono (AffineRow.tensorIdealIso I S).hom).mp
  simp only [tensorSection, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (Category.id_comp _).trans (AffineRow.tensorIdealIso_section I S b).symm

private def tensorPullbackIso :
    (Modules.pullback (Spec.algebraMap S T)).obj (tilde (ModuleCat.of S (S ⊗[R] I))) ≅
      tilde (ModuleCat.of T (T ⊗[S] (S ⊗[R] I))) :=
  (tildePullbackIso (CommRingCat.ofHom (algebraMap S T))).app
      (ModuleCat.of S (S ⊗[R] I)) ≪≫
    (tilde.functor (CommRingCat.of T)).mapIso
      (ModuleCat.extendScalarsAlgebraIso S T (ModuleCat.of S (S ⊗[R] I)))

private def coefficientArrow :
    (tilde.functor (CommRingCat.of T)).obj (ModuleCat.of T (T ⊗[S] (S ⊗[R] I))) ⟶
      SheafOfModules.unit (Spec (.of T)).ringCatSheaf :=
  (tensorPullbackIso (I := I) (S := S) (T := T)).inv ≫
    (Modules.pullback (Spec.algebraMap S T)).map (AffineRow.tensorIdealIso I S).inv ≫
      chartQuotient B t htp ≫ (chartFrame B a φ t hth).hom

private def MapEquation {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {M N : C} (f : M ⟶ N) (k : F.obj M ⟶ F.obj N) : Prop := F.map f = k

private def preimageWithEquation {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (hF : F.FullyFaithful) {M N : C} (k : F.obj M ⟶ F.obj N) :
    {f : M ⟶ N // MapEquation F f k} :=
  ⟨hF.preimage k, hF.map_preimage k⟩

private def coefficientTildeArrow :
    (tilde.functor (CommRingCat.of T)).obj (ModuleCat.of T (T ⊗[S] (S ⊗[R] I))) ⟶
      (tilde.functor (CommRingCat.of T)).obj (ModuleCat.of T T) :=
  coefficientArrow B a φ t htp hth ≫ (tildeSelf (R := CommRingCat.of T)).inv

private def rowCoefficientData :
    {k : ModuleCat.of T (T ⊗[S] (S ⊗[R] I)) ⟶ ModuleCat.of T T //
      MapEquation (tilde.functor (CommRingCat.of T)) k
        (coefficientTildeArrow B a φ t htp hth)} :=
  preimageWithEquation (tilde.functor (CommRingCat.of T))
    (tilde.fullyFaithfulFunctor (R := CommRingCat.of T))
    (coefficientTildeArrow B a φ t htp hth)

private def rowCoefficient :
    ModuleCat.of T (T ⊗[S] (S ⊗[R] I)) ⟶ ModuleCat.of T T :=
  (rowCoefficientData B a φ t htp hth).val

private theorem rowCoefficient_spec :
    MapEquation (tilde.functor (CommRingCat.of T)) (rowCoefficient B a φ t htp hth)
      (coefficientTildeArrow B a φ t htp hth) :=
  (rowCoefficientData B a φ t htp hth).property

private theorem comp_hom_of_eq_inv {C : Type*} [Category C] {X U V : C}
    (e : U ≅ V) (k : X ⟶ U) (h : X ⟶ V) (hk : k = h ≫ e.inv) :
    k ≫ e.hom = h := by
  rw [hk, Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem module_span_comp {U : Type u} [AddCommGroup U] [Module T U]
    (v : U) (K : ModuleCat.of T U ⟶ ModuleCat.of T T) :
    ModuleCat.ofHom (LinearMap.toSpanSingleton T U v) ≫ K =
      ModuleCat.ofHom (LinearMap.mulLeft T (K.hom v)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
    LinearMap.toSpanSingleton_apply, LinearMap.mulLeft_apply, smul_eq_mul, mul_comm]
    using K.hom.map_smul r v

private theorem tilde_scalar_sandwich (r : T) :
    (tildeSelf (R := CommRingCat.of T)).inv ≫
      (tilde.functor (CommRingCat.of T)).map
        (ModuleCat.ofHom (LinearMap.mulLeft T r)) ≫
      (tildeSelf (R := CommRingCat.of T)).hom = IdealFrames.affineMultiplication T r := by
  change (𝟙 _) ≫ (tilde.functor (CommRingCat.of T)).map
    (ModuleCat.ofHom (LinearMap.mulLeft T r)) ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id]
  rfl

private theorem tilde_span_comp {U : Type u} [AddCommGroup U] [Module T U]
    (v : U) (K : ModuleCat.of T U ⟶ ModuleCat.of T T) :
    ((tildeSelf (R := CommRingCat.of T)).inv ≫
      (tilde.functor (CommRingCat.of T)).map
        (ModuleCat.ofHom (LinearMap.toSpanSingleton T U v))) ≫
      ((tilde.functor (CommRingCat.of T)).map K ≫
        (tildeSelf (R := CommRingCat.of T)).hom) =
      IdealFrames.affineMultiplication T (K.hom v) := by
  rw [Category.assoc, ← Functor.map_comp_assoc, module_span_comp]
  exact tilde_scalar_sandwich (K.hom v)

private theorem transported_section_coefficient {X Y : Scheme.{u}} (g : Y ⟶ X)
    {M N : X.Modules} {H K : Y.Modules}
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ N) (e : M ≅ N)
    (z : (Modules.pullback g).obj N ≅ H) (Q : (Modules.pullback g).obj M ⟶ K)
    (fr : K ≅ SheafOfModules.unit Y.ringCatSheaf)
    (v : SheafOfModules.unit Y.ringCatSheaf ⟶ H)
    (l : H ⟶ SheafOfModules.unit Y.ringCatSheaf)
    (hv : pullbackSection g s ≫ z.hom = v)
    (hl : l = z.inv ≫ (Modules.pullback g).map e.inv ≫ Q ≫ fr.hom) :
    pullbackSection g (s ≫ e.inv) ≫ Q ≫ fr.hom = v ≫ l := by
  rw [section_postcomp, ← hv, hl]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

private def RowSectionCoefficientEq (v : S ⊗[R] I) (r : T) : Prop :=
  pullbackSection (Spec.algebraMap S T) (tensorSection v) ≫
    chartQuotient B t htp ≫ (chartFrame B a φ t hth).hom =
      IdealFrames.affineMultiplication T r

private def OriginalRowSectionCoefficientEq (v : S ⊗[R] I) (r : T) : Prop :=
  pullbackSection t
      (pullbackSection (pullback.snd B.map (Spec.algebraMap R S)) (tensorSection v) ≫
        pulledTautologicalQuotient B (Spec.algebraMap R S)) ≫
    (chartFrame B a φ t hth).hom = IdealFrames.affineMultiplication T r

private theorem rowSectionCoefficientEq_original (v : S ⊗[R] I) (r : T)
    (h : RowSectionCoefficientEq B a φ t htp hth v r) :
    OriginalRowSectionCoefficientEq B a φ t hth v r := by
  unfold RowSectionCoefficientEq at h
  unfold OriginalRowSectionCoefficientEq
  rw [← Category.assoc, chartQuotient_section] at h
  exact h

private theorem rowCoefficient_section (v : S ⊗[R] I) :
    RowSectionCoefficientEq B a φ t htp hth v
      (rowCoefficient B a φ t htp hth ((1 : T) ⊗ₜ[S] v)) := by
  change
    pullbackSection (Spec.algebraMap S T) (tensorSection v) ≫
      chartQuotient B t htp ≫ (chartFrame B a φ t hth).hom =
        IdealFrames.affineMultiplication T
          (rowCoefficient B a φ t htp hth ((1 : T) ⊗ₜ[S] v))
  let s : SheafOfModules.unit (Spec (.of S)).ringCatSheaf ⟶
      tilde (ModuleCat.of S (S ⊗[R] I)) :=
    (tildeSelf (R := CommRingCat.of S)).inv ≫
      (tilde.functor (CommRingCat.of S)).map
        (ModuleCat.ofHom (LinearMap.toSpanSingleton S (S ⊗[R] I) v))
  let E := tensorPullbackIso (I := I) (S := S) (T := T)
  have hs : pullbackSection (Spec.algebraMap S T) s ≫ E.hom =
      (tildeSelf (R := CommRingCat.of T)).inv ≫
        (tilde.functor (CommRingCat.of T)).map (ModuleCat.ofHom
          (LinearMap.toSpanSingleton T (T ⊗[S] (S ⊗[R] I)) ((1 : T) ⊗ₜ[S] v))) :=
    AffineRow.pullback_tensorSection I S T v
  have hK : (tilde.functor (CommRingCat.of T)).map (rowCoefficient B a φ t htp hth) ≫
      (tildeSelf (R := CommRingCat.of T)).hom = coefficientArrow B a φ t htp hth :=
    comp_hom_of_eq_inv (tildeSelf (R := CommRingCat.of T)) _ _
      (rowCoefficient_spec B a φ t htp hth)
  exact (transported_section_coefficient (Spec.algebraMap S T) s (AffineRow.tensorIdealIso I S)
    E (chartQuotient B t htp) (chartFrame B a φ t hth) _ _ hs hK).trans
      (tilde_span_comp ((1 : T) ⊗ₜ[S] v) (rowCoefficient B a φ t htp hth))

private theorem rowCoefficient_section_of_value (v : S ⊗[R] I) (r : T)
    (hr : rowCoefficient B a φ t htp hth ((1 : T) ⊗ₜ[S] v) = r) :
    OriginalRowSectionCoefficientEq B a φ t hth v r := by
  apply rowSectionCoefficientEq_original B a φ t htp hth v r
  exact Eq.mp (congrArg (RowSectionCoefficientEq B a φ t htp hth v) hr)
    (rowCoefficient_section B a φ t htp hth v)

private theorem affineMultiplication_injective :
    Function.Injective (IdealFrames.affineMultiplication T) := by
  intro x y hxy
  have hm : ModuleCat.ofHom (LinearMap.mulLeft T x) =
      ModuleCat.ofHom (LinearMap.mulLeft T y) :=
    (tilde.fullyFaithfulFunctor (R := CommRingCat.of T)).map_injective hxy
  have hl : LinearMap.mulLeft T x = LinearMap.mulLeft T y := by
    simpa only [ModuleCat.hom_ofHom] using
      congrArg (fun ℓ : ModuleCat.of T T ⟶ ModuleCat.of T T => ℓ.hom) hm
  have he := LinearMap.congr_fun hl 1
  simpa only [LinearMap.mulLeft_apply, mul_one] using he

private theorem rowCoefficient_one_one_tmul (b : I) :
    rowCoefficient B a φ t htp hth ((1 : T) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] b)) =
      φ (ratio R I a b) := by
  apply affineMultiplication_injective (T := T)
  have hs := rowCoefficient_section B a φ t htp hth ((1 : S) ⊗ₜ[R] b)
  unfold RowSectionCoefficientEq at hs
  rw [tensorSection_one_tmul] at hs
  exact hs.symm.trans (chartFrame_original_section B a φ t htp hth b)

private theorem rowCoefficient_one_tmul_tmul (s : S) (b : I) :
    rowCoefficient B a φ t htp hth ((1 : T) ⊗ₜ[S] (s ⊗ₜ[R] b)) =
      algebraMap S T s * φ (ratio R I a b) := by
  have hs : (1 : T) ⊗ₜ[S] (s ⊗ₜ[R] b) =
      algebraMap S T s • ((1 : T) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] b)) := by
    calc
      _ = (1 : T) ⊗ₜ[S] (s • ((1 : S) ⊗ₜ[R] b)) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      _ = _ := by rw [TensorProduct.tmul_smul, IsScalarTower.algebraMap_smul]
  rw [hs, (rowCoefficient B a φ t htp hth).hom.map_smul,
    rowCoefficient_one_one_tmul, smul_eq_mul]

end ChartTransport

private theorem reconstruct_through_iso {C : Type*} [Category C] {U M N : C}
    (e : M ≅ N) (r : U ⟶ M) (s : U ⟶ N) (h : s = r ≫ e.hom) : r = s ≫ e.inv := by
  rw [h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem tildeSelf_inv_map {T : Type u} [CommRing T] (M : ModuleCat.{u} T)
    (h : ModuleCat.of T T ⟶ M) :
    (tildeSelf (R := CommRingCat.of T)).inv ≫ (tilde.functor (CommRingCat.of T)).map h =
      (tilde.functor (CommRingCat.of T)).map h :=
  Category.id_comp _

private theorem epi_comp_of_evidence {C : Type*} [Category C] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) (hf : Epi f) (hg : Epi g) : Epi (f ≫ g) := by
  let : Epi f := hf
  let : Epi g := hg
  infer_instance

section OriginalFamily

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] {I : Ideal R}
  (B : BlowupDatum (affineCenter R I))


variable (D : (Spec (.of S)).Modules)
  (eD : D ≅ SheafOfModules.unit (Spec (.of S)).ringCatSheaf)
  {ι : Type u}
  (π : (∐ fun _ : ι => D) ⟶ degreeOneModule (I := affineCenter R I) (Spec.algebraMap R S))

/-- The specified original presentation in the specified source frame. -/
def framedFamily (i : ι) :
    SheafOfModules.unit (Spec (.of S)).ringCatSheaf ⟶
      degreeOneModule (I := affineCenter R I) (Spec.algebraMap R S) :=
  eD.inv ≫ Sigma.ι (fun _ : ι => D) i ≫ π

/-- Every specified original framed entry is the section of its recovered full tensor generator. -/
private theorem framedFamily_eq_tensorSection (i : ι) :
    framedFamily D eD π i = tensorSection (AffineRow.generators I S D eD π i) := by
  let h : ModuleCat.of S S ⟶ ModuleCat.of S (S ⊗[R] I) :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton S (S ⊗[R] I)
      (AffineRow.generators I S D eD π i))
  have hr : AffineRow.row I S D eD π i =
      framedFamily D eD π i ≫ (AffineRow.tensorIdealIso I S).hom := by
    simp only [AffineRow.row, framedFamily, Category.assoc]
  have hs : (tildeSelf (R := CommRingCat.of S)).inv ≫
      (tilde.functor (CommRingCat.of S)).map h =
        framedFamily D eD π i ≫ (AffineRow.tensorIdealIso I S).hom :=
    (tildeSelf_inv_map _ h).trans ((AffineRow.generators_reconstruct_row I S D eD π i).trans hr)
  exact reconstruct_through_iso (AffineRow.tensorIdealIso I S) (framedFamily D eD π i) _ hs

instance framedFamily_epi [Epi π] : Epi (Sigma.desc (framedFamily D eD π)) := by
  have he : Sigma.desc (framedFamily D eD π) =
      Sigma.desc (AffineRow.row I S D eD π) ≫ (AffineRow.tensorIdealIso I S).inv := by
    apply Sigma.hom_ext
    intro i
    simp only [Sigma.ι_comp_desc, Sigma.ι_comp_desc_assoc, AffineRow.row,
      framedFamily, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [he]
  infer_instance

/-- The same original framed row after the actual tautological quotient. -/
def pulledFramedFamily (i : ι) :
    SheafOfModules.unit (pullback B.map (Spec.algebraMap R S)).ringCatSheaf ⟶
      affineLine (S := S) B :=
  pullbackSection (pullback.snd B.map (Spec.algebraMap R S)) (framedFamily D eD π i) ≫
    pulledTautologicalQuotient B (Spec.algebraMap R S)

instance pulledFramedFamily_epi [Epi π] : Epi (Sigma.desc (pulledFramedFamily B D eD π)) := by
  have he : Sigma.desc (pulledFramedFamily B D eD π) =
      Sigma.desc (pulledFamily (pullback.snd B.map (Spec.algebraMap R S))
        (framedFamily D eD π)) ≫ pulledTautologicalQuotient B (Spec.algebraMap R S) := by
    apply Sigma.hom_ext
    intro i
    simp only [Sigma.ι_comp_desc, Sigma.ι_comp_desc_assoc, pulledFramedFamily, pulledFamily]
  rw [he]
  exact epi_comp_of_evidence _ _
    (pulledFamily_epi (pullback.snd B.map (Spec.algebraMap R S)) (framedFamily D eD π))
    (pulledTautologicalQuotient_epi B (Spec.algebraMap R S))

end OriginalFamily

private theorem framedFamily_coefficient_of_tensor
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] {I : Ideal R}
    (B : BlowupDatum (affineCenter R I)) (a : I)
    (φ : affineBlowupAlgebra R I a →+* T)
    (t : Spec (.of T) ⟶ pullback B.map (Spec.algebraMap R S))
    (hth : t ≫ pullback.fst B.map (Spec.algebraMap R S) =
      Spec.map (CommRingCat.ofHom φ) ≫ IdealFrames.chartMap B a)
    (D : (Spec (.of S)).Modules)
    (eD : D ≅ SheafOfModules.unit (Spec (.of S)).ringCatSheaf) {ι : Type u}
    (π : (∐ fun _ : ι => D) ⟶
      degreeOneModule (I := affineCenter R I) (Spec.algebraMap R S)) (i : ι) (r : T)
    (hc : OriginalRowSectionCoefficientEq B a φ t hth
      (AffineRow.generators I S D eD π i) r) :
    pullbackSection t (pulledFramedFamily B D eD π i) ≫ (chartFrame B a φ t hth).hom =
      IdealFrames.affineMultiplication T r := by
  rw [pulledFramedFamily, framedFamily_eq_tensorSection]
  exact hc

/-- The same original framed row has the prescribed scalar-extended ratio coefficients.
The scalar linear map is identified on every original pure tensor; no row compatibility is
assumed. -/
theorem framedFamily_coefficient_of_scalarExtension
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] {I : Ideal R}
    (B : BlowupDatum (affineCenter R I)) (a : I)
    (φ : affineBlowupAlgebra R I a →+* T)
    (t : Spec (.of T) ⟶ pullback B.map (Spec.algebraMap R S))
    (htp : t ≫ pullback.snd B.map (Spec.algebraMap R S) = Spec.algebraMap S T)
    (hth : t ≫ pullback.fst B.map (Spec.algebraMap R S) =
      Spec.map (CommRingCat.ofHom φ) ≫ IdealFrames.chartMap B a)
    (D : (Spec (.of S)).Modules)
    (eD : D ≅ SheafOfModules.unit (Spec (.of S)).ringCatSheaf) {ι : Type u}
    (π : (∐ fun _ : ι => D) ⟶
      degreeOneModule (I := affineCenter R I) (Spec.algebraMap R S))
    (χ : S ⊗[R] I →ₗ[S] T)
    (hχ : ∀ (s : S) (b : I), χ (s ⊗ₜ[R] b) = algebraMap S T s * φ (ratio R I a b))
    (i : ι) :
    pullbackSection t (pulledFramedFamily B D eD π i) ≫ (chartFrame B a φ t hth).hom =
      IdealFrames.affineMultiplication T (χ (AffineRow.generators I S D eD π i)) := by
  have hv (v : S ⊗[R] I) :
      rowCoefficient B a φ t htp hth ((1 : T) ⊗ₜ[S] v) = χ v := by
    induction v using TensorProduct.inductionOn with
    | tmul s b =>
      exact (rowCoefficient_one_tmul_tmul B a φ t htp hth s b).trans (hχ s b).symm
    | add v w hv hw => simp only [TensorProduct.tmul_add, map_add, hv, hw]
  exact framedFamily_coefficient_of_tensor B a φ t hth D eD π i _
    (rowCoefficient_section_of_value B a φ t htp hth
      (AffineRow.generators I S D eD π i) _ (hv (AffineRow.generators I S D eD π i)))

end AlgebraicGeometry.Scheme.Blowup.ProjectivePresentation.OriginalRowRestriction
