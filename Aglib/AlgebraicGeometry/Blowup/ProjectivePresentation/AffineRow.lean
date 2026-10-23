/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.ProjectivePresentation.AffineCoordinates
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Free.Sections

/-!
# The original affine presentation row in full tensor-ideal coordinates

The original affine centre ideal is identified with its actual associated
module sheaf. Native affine pullback and scalar-extension comparisons then
identify its full pulled module with the sheaf of `S ⊗[R] I`. The original
ideal-element section is taken to the original unit tensor.

A specified affine epimorphic row and a specified source frame produce
actual tensor generators on the same index. Their span is the full tensor
ideal, and sheafification reconstructs every original row entry. No
flatness, image-ideal replacement, or row-compatibility premise is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TensorProduct
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.ProjectiveSpace.FromSections
open scoped ChangeOfRings

universe u

namespace AlgebraicGeometry.Scheme.Blowup.ProjectivePresentation.AffineRow

private theorem unit_paste {C : Type*} [Category C] {U O E H Z V N : C}
    (u : U ≅ O) (v : V ≅ O) (h : U ⟶ E) (t : E ⟶ H) (e : H ⟶ N)
    (r : U ⟶ Z) (j : Z ⟶ H) (m : Z ⟶ V) (k : V ⟶ N)
    (hn : h ≫ t = r ≫ j) (ht : j ≫ e = m ≫ k)
    (hu : r ≫ m ≫ v.hom = u.hom) :
    (u.inv ≫ h) ≫ (t ≫ e) = v.inv ≫ k := by
  apply (cancel_epi u.hom).mp
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [reassoc_of% hn, ht, ← hu]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

private def MapEquation {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {M N : C} (f : M ⟶ N) (k : F.obj M ⟶ F.obj N) : Prop := F.map f = k

private theorem epi_of_mapEquation {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (hF : F.Faithful) {M N : C} (f : M ⟶ N)
    (k : F.obj M ⟶ F.obj N) (h : MapEquation F f k) (hk : Epi k) : Epi f := by
  let : F.Faithful := hF
  let : Epi k := hk
  have hf : Epi (F.map f) := by
    change F.map f = k at h
    rw [h]
    infer_instance
  exact F.epi_of_epi_map hf

private theorem epi_iso_comp {C : Type*} [Category C] {X Y Z : C}
    (e : X ≅ Y) (f : Y ⟶ Z) (hf : Epi f) : Epi (e.hom ≫ f) := by
  let : Epi f := hf
  infer_instance

private theorem precomp_map_comp {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A B E : C} {U : D} (u : U ⟶ F.obj A)
    (h : A ⟶ B) (t : B ⟶ E) (k : A ⟶ E) (he : h ≫ t = k) :
    (u ≫ F.map h) ≫ F.map t = u ≫ F.map k := by
  rw [Category.assoc, ← F.map_comp, he]

private theorem unit_triangle_of_id {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A : C} {E V : D} (r : F.obj A ⟶ E) (m : E ⟶ V)
    (w : F.obj A ⟶ V) (hw : r ≫ m = w) :
    r ≫ m ≫ (Iso.refl V).hom = F.map (Iso.refl A).hom ≫ w := by
  simpa only [Iso.refl_hom, F.map_id, Category.id_comp, Category.comp_id] using hw

private theorem affine_tilde_unit_triangle {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    (tildePullbackIso φ).hom.app (ModuleCat.of R R) ≫
        (tilde.functor S).map (ModuleCat.scalarExtensionUnit φ) ≫ (tildeSelf (R := S)).hom =
      (Modules.pullback (Spec.map φ)).map (tildeSelf (R := R)).hom ≫
        (pullbackUnitIso (Spec.map φ)).hom :=
  unit_triangle_of_id (Modules.pullback (Spec.map φ))
    ((tildePullbackIso φ).hom.app (ModuleCat.of R R))
    ((tilde.functor S).map (ModuleCat.scalarExtensionUnit φ))
    (SheafOfModules.pullbackObjUnitToUnit (Spec.map φ).toRingCatSheafHom)
    (affinePullbackTildeIso_unitToUnit φ)

section OriginalIdeal

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The original affine centre ideal is the associated sheaf of the original ring ideal. -/
def originalIdealIso :
    idealModule (affineCenter R I).subschemeι ≅ tilde (ModuleCat.of R I) := by
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let : IsClosedImmersion q :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  exact (IdealFrames.imageIdealIso q).symm ≪≫
    (affineIdealIso (CommRingCat.ofHom (Ideal.Quotient.mk I))).symm ≪≫
      (tilde.functor (CommRingCat.of R)).mapIso
        (LinearEquiv.ofEq _ _ (Ideal.mk_ker (I := I))).toModuleIso

/-- The original section of an ideal element retains that same element under the comparison. -/
theorem idealSection_originalIdealIso (b : I) :
    AffineCoordinates.idealSection R I b ≫ (originalIdealIso I).hom =
      tilde.map (ModuleCat.ofHom (LinearMap.toSpanSingleton R I b)) := by
  let e := (LinearEquiv.ofEq _ _ (Ideal.mk_ker (I := I))).toModuleIso
  have he : ModuleCat.ofHom (AffineCoordinates.kernelSection R I b) ≫ e.hom =
      ModuleCat.ofHom (LinearMap.toSpanSingleton R I b) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    rfl
  have ht :
      (tilde.functor (CommRingCat.of R)).map
          (ModuleCat.ofHom (AffineCoordinates.kernelSection R I b)) ≫
        (tilde.functor (CommRingCat.of R)).map e.hom =
      (tilde.functor (CommRingCat.of R)).map
        (ModuleCat.ofHom (LinearMap.toSpanSingleton R I b)) :=
    ((tilde.functor (CommRingCat.of R)).map_comp _ _).symm.trans
      (congrArg (tilde.functor (CommRingCat.of R)).map he)
  simp only [AffineCoordinates.idealSection, originalIdealIso, Iso.trans_hom,
    Iso.symm_hom, Functor.mapIso_hom, Category.assoc, Iso.hom_inv_id_assoc]
  exact (Category.id_comp _).trans ht

end OriginalIdeal

section ScalarSections

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

private theorem scalarUnit_one_tmul (r : R) :
    ModuleCat.scalarExtensionUnit (CommRingCat.ofHom (algebraMap R S))
        ((1 : S) ⊗ₜ[R,algebraMap R S] r) = algebraMap R S r := by
  have h := ((ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).homEquiv
    (ModuleCat.of R R) (ModuleCat.of S S)).apply_symm_apply
      (ModuleCat.ringHomModuleMap (CommRingCat.ofHom (algebraMap R S)))
  exact congrArg (fun q : ModuleCat.of R R ⟶
    (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S) => q r) h

private theorem extended_spanSingleton (M : ModuleCat.{u} R) (b : M) :
    (ModuleCat.extendScalars (algebraMap R S)).map
        (ModuleCat.ofHom (LinearMap.toSpanSingleton R M b)) ≫
      (ModuleCat.extendScalarsAlgebraIso R S M).hom =
    ModuleCat.scalarExtensionUnit (CommRingCat.ofHom (algebraMap R S)) ≫
      ModuleCat.ofHom (LinearMap.toSpanSingleton S (S ⊗[R] M) ((1 : S) ⊗ₜ[R] b)) := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro r
  change (ModuleCat.extendScalarsAlgebraIso R S M).hom
      ((ModuleCat.extendScalars (algebraMap R S)).map
        (ModuleCat.ofHom (LinearMap.toSpanSingleton R M b))
          ((1 : S) ⊗ₜ[R,algebraMap R S] r)) =
    (LinearMap.toSpanSingleton S (S ⊗[R] M) ((1 : S) ⊗ₜ[R] b))
      (ModuleCat.scalarExtensionUnit (CommRingCat.ofHom (algebraMap R S))
        ((1 : S) ⊗ₜ[R,algebraMap R S] r))
  rw [ModuleCat.ExtendScalars.map_tmul, ModuleCat.extendScalarsAlgebraIso_tmul,
    scalarUnit_one_tmul]
  change (1 : S) ⊗ₜ[R] (r • b) = algebraMap R S r • ((1 : S) ⊗ₜ[R] b)
  rw [TensorProduct.tmul_smul, IsScalarTower.algebraMap_smul]

private theorem pulled_tilde_spanSingleton (M : Type u) [AddCommGroup M] [Module R M]
    (b : M) :
    pullbackSection (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        ((tildeSelf (R := CommRingCat.of R)).inv ≫
          (tilde.functor (CommRingCat.of R)).map
            (ModuleCat.ofHom (LinearMap.toSpanSingleton R M b))) ≫
      ((tildePullbackIso (CommRingCat.ofHom (algebraMap R S))).app (ModuleCat.of R M) ≪≫
        (tilde.functor (CommRingCat.of S)).mapIso
          (ModuleCat.extendScalarsAlgebraIso R S (ModuleCat.of R M))).hom =
    (tildeSelf (R := CommRingCat.of S)).inv ≫
      (tilde.functor (CommRingCat.of S)).map (ModuleCat.ofHom
        (LinearMap.toSpanSingleton S (S ⊗[R] M) ((1 : S) ⊗ₜ[R] b))) := by
  let φ : CommRingCat.of R ⟶ CommRingCat.of S := CommRingCat.ofHom (algebraMap R S)
  let h : ModuleCat.of R R ⟶ ModuleCat.of R M :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton R M b)
  let k : ModuleCat.of S S ⟶ ModuleCat.of S (S ⊗[R] M) :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton S (S ⊗[R] M) ((1 : S) ⊗ₜ[R] b))
  let e := ModuleCat.extendScalarsAlgebraIso R S (ModuleCat.of R M)
  let u := (Modules.pullback (Spec.map φ)).mapIso (tildeSelf (R := CommRingCat.of R)) ≪≫
    pullbackUnitIso (Spec.map φ)
  have hn : (Modules.pullback (Spec.map φ)).map (tilde.map h) ≫
      (tildePullbackIso φ).hom.app (ModuleCat.of R M) =
    (tildePullbackIso φ).hom.app (ModuleCat.of R R) ≫
      tilde.map ((ModuleCat.extendScalars φ.hom).map h) :=
    (tildePullbackIso φ).hom.naturality h
  have hu : (tildePullbackIso φ).hom.app (ModuleCat.of R R) ≫
      tilde.map (ModuleCat.scalarExtensionUnit φ) ≫
        (tildeSelf (R := CommRingCat.of S)).hom = u.hom :=
    affine_tilde_unit_triangle φ
  have he : (ModuleCat.extendScalars φ.hom).map h ≫ e.hom =
      ModuleCat.scalarExtensionUnit φ ≫ k :=
    extended_spanSingleton R S (ModuleCat.of R M) b
  have ht : tilde.map ((ModuleCat.extendScalars φ.hom).map h) ≫ tilde.map e.hom =
      tilde.map (ModuleCat.scalarExtensionUnit φ) ≫ tilde.map k :=
    ((tilde.functor (CommRingCat.of S)).map_comp _ _).symm.trans
      ((congrArg (tilde.functor (CommRingCat.of S)).map he).trans
        ((tilde.functor (CommRingCat.of S)).map_comp _ _))
  have hp := unit_paste u (tildeSelf (R := CommRingCat.of S))
    ((Modules.pullback (Spec.map φ)).map (tilde.map h))
    ((tildePullbackIso φ).hom.app (ModuleCat.of R M))
    ((tilde.functor (CommRingCat.of S)).map e.hom)
    ((tildePullbackIso φ).hom.app (ModuleCat.of R R))
    ((tilde.functor (CommRingCat.of S)).map ((ModuleCat.extendScalars φ.hom).map h))
    ((tilde.functor (CommRingCat.of S)).map (ModuleCat.scalarExtensionUnit φ))
    ((tilde.functor (CommRingCat.of S)).map k) hn ht hu
  simpa only [u, φ, h, k, e, pullbackSection, Iso.trans_inv, Iso.trans_hom,
    Functor.mapIso_inv, Functor.mapIso_hom, Iso.app_hom,
    CategoryTheory.Functor.map_comp, tilde.functor_map, Category.assoc] using hp

end ScalarSections

section TensorIdeal

variable {R : Type u} [CommRing R] (I : Ideal R)
  (S : Type u) [CommRing S] [Algebra R S]

/-- The full pulled ideal is associated to the full tensor module, including possible torsion. -/
def tensorIdealIso :
    degreeOneModule (I := affineCenter R I)
        (Spec.map (CommRingCat.ofHom (algebraMap R S))) ≅
      tilde (ModuleCat.of S (S ⊗[R] I)) :=
  (Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).mapIso
      (originalIdealIso I) ≪≫
    (tildePullbackIso (CommRingCat.ofHom (algebraMap R S))).app (ModuleCat.of R I) ≪≫
      (tilde.functor (CommRingCat.of S)).mapIso
        (ModuleCat.extendScalarsAlgebraIso R S (ModuleCat.of R I))

/-- The actual pulled section of the original element becomes the original unit tensor. -/
theorem tensorIdealIso_section (b : I) :
    pullbackSection (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (AffineCoordinates.idealSection R I b) ≫ (tensorIdealIso I S).hom =
      tilde.map (ModuleCat.ofHom
        (LinearMap.toSpanSingleton S (S ⊗[R] I) ((1 : S) ⊗ₜ[R] b))) := by
  let p := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let k : SheafOfModules.unit (Spec (.of R)).ringCatSheaf ⟶ tilde (ModuleCat.of R I) :=
    (tildeSelf (R := CommRingCat.of R)).inv ≫
      (tilde.functor (CommRingCat.of R)).map
        (ModuleCat.ofHom (LinearMap.toSpanSingleton R I b))
  let q := ((tildePullbackIso (CommRingCat.ofHom (algebraMap R S))).app
      (ModuleCat.of R I) ≪≫ (tilde.functor (CommRingCat.of S)).mapIso
        (ModuleCat.extendScalarsAlgebraIso R S (ModuleCat.of R I))).hom
  have hi : AffineCoordinates.idealSection R I b ≫ (originalIdealIso I).hom = k :=
    (idealSection_originalIdealIso I b).trans (Category.id_comp _).symm
  have hs : pullbackSection p (AffineCoordinates.idealSection R I b) ≫
      (Modules.pullback p).map (originalIdealIso I).hom = pullbackSection p k :=
    precomp_map_comp (Modules.pullback p) (pullbackUnitIso p).inv
      (AffineCoordinates.idealSection R I b) (originalIdealIso I).hom k hi
  calc
    _ = (pullbackSection p (AffineCoordinates.idealSection R I b) ≫
        (Modules.pullback p).map (originalIdealIso I).hom) ≫ q := by
      simp only [tensorIdealIso, p, q, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
    _ = pullbackSection p k ≫ q := congrArg (fun h => h ≫ q) hs
    _ = (tildeSelf (R := CommRingCat.of S)).inv ≫
        (tilde.functor (CommRingCat.of S)).map (ModuleCat.ofHom
          (LinearMap.toSpanSingleton S (S ⊗[R] I) ((1 : S) ⊗ₜ[R] b))) :=
      pulled_tilde_spanSingleton R S I b
    _ = _ := Category.id_comp _

/-- Pulling a section of the full tensor ideal retains its original unit tensor,
with the actual source and target tilde-unit comparisons explicit. -/
theorem pullback_tensorSection (T : Type u) [CommRing T] [Algebra S T] (v : S ⊗[R] I) :
    pullbackSection (Spec.map (CommRingCat.ofHom (algebraMap S T)))
        ((tildeSelf (R := CommRingCat.of S)).inv ≫
          (tilde.functor (CommRingCat.of S)).map
            (ModuleCat.ofHom (LinearMap.toSpanSingleton S (S ⊗[R] I) v))) ≫
      ((tildePullbackIso (CommRingCat.ofHom (algebraMap S T))).app
          (ModuleCat.of S (S ⊗[R] I)) ≪≫
        (tilde.functor (CommRingCat.of T)).mapIso
          (ModuleCat.extendScalarsAlgebraIso S T (ModuleCat.of S (S ⊗[R] I)))).hom =
    (tildeSelf (R := CommRingCat.of T)).inv ≫
      (tilde.functor (CommRingCat.of T)).map (ModuleCat.ofHom
        (LinearMap.toSpanSingleton T (T ⊗[S] (S ⊗[R] I)) ((1 : T) ⊗ₜ[S] v))) :=
  pulled_tilde_spanSingleton S T (S ⊗[R] I) v

variable (D : (Spec (CommRingCat.of S)).Modules)
  (eD : D ≅ SheafOfModules.unit (Spec (CommRingCat.of S)).ringCatSheaf)
  {ι : Type u}
  (π : (∐ fun _ : ι => D) ⟶ degreeOneModule (I := affineCenter R I)
    (Spec.map (CommRingCat.ofHom (algebraMap R S))))

/-- The original indexed affine row in the supplied source frame and actual tensor coordinates. -/
def row (i : ι) :
    SheafOfModules.unit (Spec (CommRingCat.of S)).ringCatSheaf ⟶
      tilde (ModuleCat.of S (S ⊗[R] I)) :=
  eD.inv ≫ Sigma.ι (fun _ : ι => D) i ≫ π ≫ (tensorIdealIso I S).hom

/-- The same original framed coproduct row retained as one actual sheaf map. -/
def sheafPresentation (D : (Spec (CommRingCat.of S)).Modules)
    (eD : D ≅ SheafOfModules.unit (Spec (CommRingCat.of S)).ringCatSheaf)
    (π : (∐ fun _ : ι => D) ⟶ degreeOneModule (I := affineCenter R I)
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))) :
    (tilde.functor (CommRingCat.of S)).obj (ModuleCat.of S (ι →₀ S)) ⟶
      (tilde.functor (CommRingCat.of S)).obj (ModuleCat.of S (S ⊗[R] I)) :=
  (tildeFinsupp ι).hom ≫ Sigma.desc (row I S D eD π)

/-- The actual module preimage of the same original framed sheaf presentation. -/
def linearPresentation (D : (Spec (CommRingCat.of S)).Modules)
    (eD : D ≅ SheafOfModules.unit (Spec (CommRingCat.of S)).ringCatSheaf)
    (π : (∐ fun _ : ι => D) ⟶ degreeOneModule (I := affineCenter R I)
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))) :
    ModuleCat.of S (ι →₀ S) ⟶ ModuleCat.of S (S ⊗[R] I) :=
  (tilde.fullyFaithfulFunctor (R := CommRingCat.of S)).preimage
    (sheafPresentation I S D eD π)

/-- The tensor generator corresponding to the same original coproduct summand. -/
def generators (D : (Spec (CommRingCat.of S)).Modules)
    (eD : D ≅ SheafOfModules.unit (Spec (CommRingCat.of S)).ringCatSheaf)
    (π : (∐ fun _ : ι => D) ⟶ degreeOneModule (I := affineCenter R I)
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))) (i : ι) : S ⊗[R] I :=
  linearPresentation I S D eD π (Finsupp.single i 1)

/-- Sheafification recovers the exact original framed coproduct row. -/
private theorem linearPresentation_mapEquation :
    MapEquation (tilde.functor (CommRingCat.of S)) (linearPresentation I S D eD π)
      (sheafPresentation I S D eD π) :=
  (tilde.fullyFaithfulFunctor (R := CommRingCat.of S)).map_preimage _

/-- Sheafification recovers the exact original framed coproduct row. -/
theorem linearPresentation_spec :
    tilde.map (linearPresentation I S D eD π) =
      (tildeFinsupp ι).hom ≫ Sigma.desc (row I S D eD π) :=
  linearPresentation_mapEquation I S D eD π

/-- The original presentation sends a scalar basis entry to its original generator multiple. -/
theorem linearPresentation_single (i : ι) (r : S) :
    linearPresentation I S D eD π (Finsupp.single i r) =
      r • generators I S D eD π i := by
  have hs : Finsupp.single i r = r • Finsupp.single i (1 : S) := by simp
  rw [hs]
  exact (linearPresentation I S D eD π).hom.map_smul r _

/-- Every original row entry is reconstructed from its actual extracted tensor generator. -/
theorem generators_reconstruct_row (i : ι) :
    tilde.map (ModuleCat.ofHom
        (LinearMap.toSpanSingleton S (S ⊗[R] I) (generators I S D eD π i))) =
      row I S D eD π i := by
  have he : ModuleCat.ofHom (Finsupp.lsingle i : S →ₗ[S] (ι →₀ S)) ≫
      linearPresentation I S D eD π =
    ModuleCat.ofHom
      (LinearMap.toSpanSingleton S (S ⊗[R] I) (generators I S D eD π i)) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    exact linearPresentation_single I S D eD π i r
  rw [← he, tilde.map_comp, linearPresentation_spec, ← Category.assoc,
    tildeFinsupp_hom_ιFree, SheafOfModules.ιFree, Sigma.ι_comp_desc]

variable [Epi π]

/-- The original epimorphism remains epimorphic in the supplied frames and tensor coordinates. -/
instance row_epi : Epi (Sigma.desc (row I S D eD π)) := by
  have h : Sigma.desc (row I S D eD π) =
      CategoryTheory.Limits.Sigma.map (fun _ : ι => eD.inv) ≫ π ≫
        (tensorIdealIso I S).hom := by
    apply Sigma.hom_ext
    intro i
    simp only [Sigma.ι_comp_desc, Sigma.ι_map_assoc, row]
  rw [h]
  infer_instance

/-- The original framed sheaf presentation remains epimorphic. -/
instance sheafPresentation_epi : Epi (sheafPresentation I S D eD π) := by
  exact epi_iso_comp (tildeFinsupp (R := CommRingCat.of S) ι)
    (Sigma.desc (row I S D eD π)) (row_epi I S D eD π)

/-- The original native functor reflects epimorphy through the shared map-equation boundary. -/
instance linearPresentation_epi : Epi (linearPresentation I S D eD π) := by
  exact epi_of_mapEquation (tilde.functor (CommRingCat.of S))
    (tilde.fullyFaithfulFunctor (R := CommRingCat.of S)).faithful
    (linearPresentation I S D eD π) (sheafPresentation I S D eD π)
    (linearPresentation_mapEquation I S D eD π) (sheafPresentation_epi I S D eD π)

/-- The extracted original indexed family spans the full tensor ideal. -/
theorem span_generators : Submodule.span S (Set.range (generators I S D eD π)) = ⊤ := by
  have h : (linearPresentation I S D eD π).hom =
      Finsupp.linearCombination S (generators I S D eD π) := by
    apply Finsupp.lhom_ext
    intro i r
    rw [Finsupp.linearCombination_single]
    exact linearPresentation_single I S D eD π i r
  rw [← Finsupp.range_linearCombination, ← h, LinearMap.range_eq_top]
  exact (ModuleCat.epi_iff_surjective (linearPresentation I S D eD π)).mp inferInstance

end TensorIdeal

end AlgebraicGeometry.Scheme.Blowup.ProjectivePresentation.AffineRow
