/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.NormalSurface.Cohomology
public import Aglib.Algebra.Homology.ModuleCat.HomComplex.TwoLayer.UnitNormalization

/-!
# The original degree-zero dual unit and canonical section trace

The same canonical H0/sections map, concentration isomorphism, closed-embedding
Serre map and actual resolution models identify the original degree-zero dual
unit with the existing chosen-embedding section trace. The coefficient is the
native coinduced module and its functional is normalized by the supplied
augmentation. Original dual-model naturality proves the unit equation; no
compatibility, orientation or projectivity premise is assumed by the geometric
consumer. This does not assert embedding independence of the proper trace.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules Opposite
open CochainComplex CochainComplex.HomComplex HomologicalComplex

universe u

private theorem surfaceUnitTrace_mk_zero
    {C : Type*} [Category* C] [HasShift C ℤ] {X Y : C} (f : X ⟶ Y) :
    ShiftedHom.mk₀ (0 : ℤ) rfl f =
      f ≫ (CategoryTheory.shiftFunctorZero C ℤ).inv.app Y := by
  simp [ShiftedHom.mk₀, CategoryTheory.shiftFunctorZero']

private theorem surfaceUnitTrace_right_cancel_iso
    {C : Type*} [Category* C] {X Y Z : C}
    (e : Y ≅ Z) (f : X ⟶ Y) (g : X ⟶ Z) (h : f ≫ e.hom = g) :
    f = g ≫ e.inv := by
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
    congrArg (fun k => k ≫ e.inv) h

private theorem surfaceUnitTrace_ext_mk_zero
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C] [HasExt C]
    {X Y : C} (f : X ⟶ Y) :
    (Ext.mk₀ f).hom = (DerivedCategory.singleFunctor C 0).map f ≫
      (shiftFunctorZero (DerivedCategory C) ℤ).inv.app
        ((DerivedCategory.singleFunctor C 0).obj Y) :=
  (Ext.mk₀_hom f).trans (surfaceUnitTrace_mk_zero _)

private theorem surfaceUnitTrace_postcompose
    {C : Type*} [Category* C] {X Y Z W : C}
    (a : X ⟶ Y) (b : Y ⟶ Z) (c : Z ⟶ W) (d : Y ⟶ W)
    (h : b ≫ c = d) : (a ≫ b) ≫ c = a ≫ d :=
  (Category.assoc a b c).trans (congrArg (fun f => a ≫ f) h)

private theorem surfaceUnitTrace_three_postcompose
    {C : Type*} [Category* C] {X Y Z W T : C}
    (a : X ⟶ Y) (b : Y ⟶ Z) (c : Z ⟶ W) (d : W ⟶ T) :
    (a ≫ b ≫ c) ≫ d = a ≫ b ≫ c ≫ d :=
  (Category.assoc a (b ≫ c) d).trans (congrArg (fun k => a ≫ k) (Category.assoc b c d))

private theorem surfaceUnitTrace_iso_composite_hom
    {C : Type*} [Category* C] {X Y Z W : C}
    (a : X ≅ Y) (b : Y ≅ Z) (c : Z ⟶ W) (d : Y ≅ W)
    (h : b.hom ≫ c = d.hom) : (a ≪≫ b).hom ≫ c = (a ≪≫ d).hom :=
  surfaceUnitTrace_postcompose a.hom b.hom c d.hom h

private theorem surfaceUnitTrace_iso_composite_inv
    {C : Type*} [Category* C] {X Y Z : C}
    (e : X ≅ Y) (z : Y ≅ Z) (t : X ≅ Z)
    (h : e.hom ≫ z.hom = t.hom) : z.inv ≫ e.inv = t.inv := by
  apply (cancel_mono t.hom).mp
  rw [t.inv_hom_id, ← h]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id]

private theorem surfaceUnitTrace_serre_composite_apply
    {C : Type*} [Category* C] [Preadditive C]
    {S P : Type*} [AddCommGroup S] [AddCommGroup P] {X Y Z : C}
    (F : S ≃+ (X ⟶ Y)) (t : Y ≅ Z) (G : (X ⟶ Z) ≃+ P) (x : S) :
    (F.trans ((Linear.homCongr ℤ (Iso.refl X) t).toAddEquiv.trans G)) x =
      G (F x ≫ t.hom) := by
  change G (((𝟙 X) ≫ F x) ≫ t.hom) = G (F x ≫ t.hom)
  rw [Category.id_comp]

private theorem surfaceUnitTrace_iso_linear_trans_apply
    {R : Type u} [CommRing R] {M N : ModuleCat.{u} R}
    {P : Type*} [AddCommGroup P] [Module R P]
    (e : M ≅ N) (f : N ≃ₗ[R] P) (x : M) :
    (e.toLinearEquiv.trans f) x = f (e.hom x) := rfl

private theorem surfaceUnitTrace_linear_comp_apply
    {A : Type u} [CommRing A] {L M N : ModuleCat.{u} A}
    (f : L ⟶ M) (g : M ⟶ N) (x : L) :
    (g.hom.comp f.hom) x = g (f x) := rfl

private theorem full_preimage_mk₀
    {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]
    (F : C ⥤ D) [F.Full] [F.Faithful] [F.CommShift ℤ]
    {K L : C} (f : F.obj K ⟶ F.obj L) :
    F.preimage (ShiftedHom.mk₀ (0 : ℤ) rfl f ≫ (F.commShiftIso (0 : ℤ)).inv.app L) =
      ShiftedHom.mk₀ (0 : ℤ) rfl (F.preimage f) := by
  let t := (F.commShiftIso (0 : ℤ)).app L
  have h : F.map (ShiftedHom.mk₀ (0 : ℤ) rfl (F.preimage f)) ≫ t.hom =
      ShiftedHom.mk₀ (0 : ℤ) rfl f :=
    (ShiftedHom.map_mk₀ (0 : ℤ) rfl (F.preimage f) F).trans
      (congrArg (ShiftedHom.mk₀ (0 : ℤ) rfl) (F.map_preimage f))
  apply F.map_injective
  exact (F.map_preimage _).trans
    (surfaceUnitTrace_right_cancel_iso t _ _ h).symm

private theorem surfaceUnitTrace_map_three
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {W X Y Z : C} (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z) :
    F.map (a ≫ b ≫ c) = F.map a ≫ F.map b ≫ F.map c := by
  rw [F.map_comp, F.map_comp]

private theorem surfaceUnitTrace_affine_shifted_value
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
    (F : C ⥤ D) (V : D ⥤ E) [F.CommShift ℤ] [V.CommShift ℤ]
    {X Y : C} {Z : D} {P : E} (r : ℤ)
    (c : P ⟶ V.obj (F.obj X)) (g : X ⟶ Y⟦r⟧) (t : F.obj Y ≅ Z) :
    c ≫ V.map (F.map g) ≫
        (V.mapIso ((F.commShiftIso r).app Y ≪≫
          (shiftFunctor D r).mapIso t) ≪≫ (V.commShiftIso r).app Z).hom =
      c ≫ ShiftedHom.map g (F ⋙ V) ≫ (V.map t.hom)⟦r⟧' := by
  have ht : V.map (t.hom⟦r⟧') ≫ (V.commShiftIso r).hom.app Z =
      (V.commShiftIso r).hom.app (F.obj Y) ≫ (V.map t.hom)⟦r⟧' :=
    (V.commShiftIso r).hom.naturality t.hom
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, ShiftedHom.map,
    Functor.comp_map, Functor.commShiftIso_comp_hom_app, Category.assoc]
  exact congrArg (fun k => c ≫ V.map (F.map g) ≫
    V.map ((F.commShiftIso r).hom.app Y) ≫ k) ht

private theorem affine_shifted_zero
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    [HasShift C ℤ] [HasShift D ℤ] [HasShift C' ℤ] [HasShift D' ℤ]
    (F : C ⥤ D) (IC : C ⥤ C') (ID : D ⥤ D')
    [F.CommShift ℤ] [IC.CommShift ℤ] [ID.CommShift ℤ] [IC.Full] [IC.Faithful]
    {K L : C} {N : D} {S : D'} (c : S ⟶ ID.obj (F.obj K)) (t : F.obj L ⟶ N)
    (f : IC.obj K ⟶ IC.obj L) :
    c ≫ ShiftedHom.map (IC.preimage
        (ShiftedHom.mk₀ (0 : ℤ) rfl f ≫ (IC.commShiftIso (0 : ℤ)).inv.app L))
          (F ⋙ ID) ≫
        (ID.map t)⟦(0 : ℤ)⟧' ≫ (shiftFunctorZero D' ℤ).hom.app (ID.obj N) =
      c ≫ ID.map (F.map (IC.preimage f)) ≫ ID.map t := by
  rw [full_preimage_mk₀, ShiftedHom.map_mk₀, surfaceUnitTrace_mk_zero]
  let Z := shiftFunctorZero D' ℤ
  have ht := Z.inv.naturality (ID.map t)
  change ID.map t ≫ Z.inv.app (ID.obj N) =
    Z.inv.app (ID.obj (F.obj L)) ≫ (ID.map t)⟦(0 : ℤ)⟧' at ht
  change c ≫ (ID.map (F.map (IC.preimage f)) ≫ Z.inv.app (ID.obj (F.obj L))) ≫
      (ID.map t)⟦(0 : ℤ)⟧' ≫ Z.hom.app (ID.obj N) = _
  calc
    _ = c ≫ ID.map (F.map (IC.preimage f)) ≫
        (Z.inv.app (ID.obj (F.obj L)) ≫ (ID.map t)⟦(0 : ℤ)⟧') ≫ Z.hom.app (ID.obj N) := by
      simp only [Category.assoc]
    _ = c ≫ ID.map (F.map (IC.preimage f)) ≫
        (ID.map t ≫ Z.inv.app (ID.obj N)) ≫ Z.hom.app (ID.obj N) := by rw [← ht]
    _ = _ := by
      let z : (ID.obj N)⟦(0 : ℤ)⟧ ≅ ID.obj N := Z.app (ID.obj N)
      have hc : (ID.map t ≫ z.inv) ≫ z.hom = ID.map t :=
        (Category.assoc _ _ _).trans
          ((congrArg (fun k => ID.map t ≫ k) z.inv_hom_id).trans (Category.comp_id _))
      exact congrArg (fun k => c ≫ ID.map (F.map (IC.preimage f)) ≫ k) hc

/-- Native zero-shift coherence leaves the original coefficient augmentation. -/
private theorem original_coefficient_shift_zero
    {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]
    (F : C ⥤ D) [F.CommShift ℤ] {J : C} {N : D} (e : N ≅ F.obj J) :
    (((shiftFunctor D (0 : ℤ)).mapIso e) ≪≫
        ((F.commShiftIso (0 : ℤ)).app J).symm).hom ≫
      F.map ((shiftFunctorZero C ℤ).hom.app J) =
    (shiftFunctorZero D ℤ).hom.app N ≫ e.hom := by
  let ZC := shiftFunctorZero C ℤ
  let ZD := shiftFunctorZero D ℤ
  have hz : (F.commShiftIso (0 : ℤ)).inv.app J ≫ F.map (ZC.hom.app J) =
      ZD.hom.app (F.obj J) := by
    let t : F.obj ((shiftFunctor C (0 : ℤ)).obj J) ≅ F.obj J :=
      F.mapIso ((shiftFunctorZero C ℤ).app J)
    rw [F.commShiftIso_zero, Functor.CommShift.isoZero_inv_app]
    let d : (F.obj J)⟦(0 : ℤ)⟧ ⟶ F.obj J := ZD.hom.app (F.obj J)
    change (d ≫ t.inv) ≫ t.hom = d
    exact (Category.assoc d t.inv t.hom).trans
      ((congrArg (fun k => d ≫ k) t.inv_hom_id).trans (Category.comp_id d))
  change ((shiftFunctor D (0 : ℤ)).map e.hom ≫
      (F.commShiftIso (0 : ℤ)).inv.app J) ≫ F.map (ZC.hom.app J) = _
  rw [Category.assoc, hz]
  exact ZD.hom.naturality e.hom

/-- Paste the actual source comparison and both degree-zero target normalizations. -/
private theorem original_model_value_normalization
    {C : Type*} [Category* C] {L M N P Q U V : C}
    (a : L ⟶ M) (b : M ⟶ N) (c : N ⟶ P) (f : P ⟶ Q)
    (t : Q ⟶ U) (q : U ⟶ V) {W : C} (z : Q ⟶ W) (u : W ⟶ V)
    (g : P ⟶ W) (hf : f ≫ z = g) (ht : t ≫ q = z ≫ u) :
    (((a ≫ b ≫ c) ≫ f) ≫ t) ≫ q = a ≫ b ≫ (c ≫ g) ≫ u := by
  simp only [Category.assoc]
  rw [ht, ← Category.assoc f z u, hf]

private theorem original_source_iso_square
    {C : Type*} [Category* C] {X Y Z W : C}
    (s : X ≅ Y) (a : Y ⟶ Z) (b : Z ⟶ W) (u : X ⟶ W)
    (h : s.hom ≫ a ≫ b = u) : a ≫ b = s.inv ≫ u := by
  rw [← h]
  simp only [Iso.inv_hom_id_assoc]

private theorem original_dual_model_naturality
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (Q : C ⥤ D) (G : Dᵒᵖ ⥤ E) (F : Cᵒᵖ ⥤ E) (e : Q.op ⋙ G ≅ F)
    {L K : C} {A B : D} (s : Q.obj L ≅ A) (t : Q.obj K ≅ B)
    (f : L ⟶ K) (g : A ⟶ B) (h : Q.map f ≫ t.hom = s.hom ≫ g) :
    G.map g.op ≫ (G.map s.hom.op ≫ e.hom.app (op L)) =
      (G.map t.hom.op ≫ e.hom.app (op K)) ≫ F.map f.op := by
  have h₀ := congrArg (fun z => G.map z.op) h
  simp only [op_comp, Functor.map_comp] at h₀
  have h₁ := e.hom.naturality f.op
  change G.map (Q.map f).op ≫ e.hom.app (op L) =
    e.hom.app (op K) ≫ F.map f.op at h₁
  calc
    _ = (G.map g.op ≫ G.map s.hom.op) ≫ e.hom.app (op L) :=
      (Category.assoc _ _ _).symm
    _ = (G.map t.hom.op ≫ G.map (Q.map f).op) ≫ e.hom.app (op L) :=
      congrArg (fun z => z ≫ e.hom.app (op L)) h₀.symm
    _ = G.map t.hom.op ≫ (G.map (Q.map f).op ≫ e.hom.app (op L)) :=
      Category.assoc _ _ _
    _ = G.map t.hom.op ≫ (e.hom.app (op K) ≫ F.map f.op) :=
      congrArg (fun z => G.map t.hom.op ≫ z) h₁
    _ = _ := (Category.assoc _ _ _).symm

private theorem original_homology_model_hom
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (F : C ⥤ D) (H : D ⥤ E) {X Y : C} {Z : D} {W : E}
    (e : X ≅ Y) (d : F.obj Y ≅ Z) (p : H.obj Z ≅ W) :
    (H.mapIso (F.mapIso e ≪≫ d) ≪≫ p).hom =
      ((F ⋙ H).mapIso e ≪≫ H.mapIso d ≪≫ p).hom := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp,
    Functor.comp_map, Category.assoc]

private theorem original_prefix_map_iso_trans_hom
    {C D : Type*} [Category* C] [Category* D] (H : C ⥤ D)
    {X Y Z : C} {W : D} (p : W ≅ H.obj X) (e : X ≅ Y) (f : Y ≅ Z) :
    (p ≪≫ H.mapIso (e ≪≫ f)).hom =
      (p ≪≫ H.mapIso e).hom ≫ H.map f.hom := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]

private theorem original_coefficient_zero_inverse
    {C : Type*} [Category* C] {W V U Z : C}
    (T : W ≅ V) (t : U ≅ Z) (q : V ⟶ Z) (z : W ⟶ U)
    (h : T.hom ≫ q = z ≫ t.hom) : T.inv ≫ z = q ≫ t.inv := by
  apply (cancel_mono t.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← h, Iso.inv_hom_id_assoc]

private theorem original_restricted_unit_model
    {C : Type*} [Category* C] {S A B D E T : C}
    (a : S ⟶ A) (m : A ⟶ B) (e : B ≅ D) (η : A ⟶ D)
    (k : B ≅ T) (l : A ⟶ E) (b : S ⟶ E) (f : E ⟶ T)
    (hη : η = m ≫ e.hom) (hn : m ≫ k.hom = l ≫ f) (hs : a ≫ l = b) :
    a ≫ η ≫ (e.inv ≫ k.hom) = b ≫ f := by
  calc
    _ = a ≫ m ≫ k.hom := by
      rw [hη]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = a ≫ l ≫ f := congrArg (fun z => a ≫ z) hn
    _ = _ := by rw [← Category.assoc, hs]

private theorem original_source_coefficient_reassociate
    {C : Type*} [Category* C] {L M N V W Z : C}
    (p : M ≅ L) (e : M ≅ N) (g : N ⟶ V) (t : V ≅ W) (j : W ≅ Z) :
    p.inv ≫ e.hom ≫ g ≫ t.hom ≫ j.hom =
      (p.symm ≪≫ e).hom ≫ g ≫ (t ≪≫ j).hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]

private theorem original_normalized_model_cancel
    {C : Type*} [Category* C] {K X I J N : C}
    (P : K ≅ X) (t : N ≅ J) (d : K ⟶ I) (q : I ⟶ J) (g : X ⟶ N)
    (h : d ≫ q = P.hom ≫ g ≫ t.hom) : P.inv ≫ d ≫ q ≫ t.inv = g := by
  have h' := congrArg (fun w => P.inv ≫ w ≫ t.inv) h
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id] using h'

namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
/-- The standard derived-category model for modules over the coefficient ring. -/
local instance surfaceUnitTraceModuleDerived (A : Type u) [CommRing A] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} A) := HasDerivedCategory.standard _

section OriginalSourceModel

variable {A : Type u} [CommRing A] (X : Scheme.{u}) (α : A →+* Γ(X, ⊤))
    (IX : InjectiveResolution (normalSurfaceUnit X : X.Modules))

/-- Homology of the original dual unit is precomposition by the actual structural
chain augmentation under the unchanged source models. -/
theorem normalSurfaceDerivedDualHomologyIso_unit
    (J : CochainComplex (ModuleCat.{u} A) ℤ) [J.IsKInjective] :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
        ((derivedDual J).map (DerivedCategory.Plus.ι.map
          (moduleDerivedStructureUnit X α)).op) ≫
      (TwoLayerDual.singleHomologyIso J (ModuleCat.of A A) 0).hom =
    (normalSurfaceDerivedDualHomologyIso X α IX J 0).hom ≫
      homologyMap (precomp A (normalSurfaceStructureResolutionUnit X α IX) J) 0 := by
  let Q := DerivedCategory.Q (C := ModuleCat.{u} A)
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0
  let K := moduleResolutionSectionComplex X α IX
  let L := (singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)
  let C := DerivedCategory.Plus.ι.obj (moduleDerivedStructure X α)
  let κ : L ⟶ K := normalSurfaceStructureResolutionUnit X α IX
  let η := DerivedCategory.Plus.ι.map (moduleDerivedStructureUnit X α)
  let t : Q.obj K ≅ C := normalSurfaceStructureResolutionIso X α IX
  let s := (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) 0).app
    (ModuleCat.of A A)
  let G : (DerivedCategory (ModuleCat.{u} A))ᵒᵖ ⥤ ModuleCat.{u} A :=
    derivedDualHomologyFunctor.{u, u, u + 1} J 0
  let F : (CochainComplex (ModuleCat.{u} A) ℤ)ᵒᵖ ⥤ ModuleCat.{u} A :=
    moduleHomologyFunctor.{u, u} J 0
  let E : Q.op ⋙ G ≅ F := derivedDualHomologyModelNatIso.{u, u, u + 1} J 0
  let p : F.obj (op K) ⟶ F.obj (op L) := homologyMap (precomp A κ J) 0
  have hκ : Q.map κ ≫ t.hom = s.inv ≫ η :=
    original_source_iso_square s (Q.map κ) t.hom η
      (normalSurfaceStructureResolutionUnit_normalization X α IX)
  have hmodel : (normalSurfaceDerivedDualHomologyIso X α IX J 0).hom =
      G.map t.hom.op ≫ E.hom.app (op K) :=
    original_homology_model_hom (derivedDual J) H t.op
      ((derivedDualFactors J).app (op K))
      ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) 0).app
        (moduleComplex A K J))
  have h : H.map ((derivedDual J).map η.op) ≫
      (TwoLayerDual.singleHomologyIso J (ModuleCat.of A A) 0).hom =
        (G.map t.hom.op ≫ E.hom.app (op K)) ≫ p :=
    original_dual_model_naturality Q G F E s.symm t κ η hκ
  exact h.trans (congrArg (fun z => z ≫ p) hmodel.symm)

variable {R : Type u} [CommRing R] (σ : R →+* A)

/-- The exact restriction of the original unit, expressed on its actual source model,
retains the native source-single comparison and structural chain augmentation. -/
theorem normalSurfaceRestrictedUnit_model :
    let K := moduleResolutionSectionComplex X α IX
    let U := ModuleCat.restrictScalars σ
    let P := (U.mapDerivedCategoryFactors.app K).symm ≪≫
      U.mapDerivedCategory.mapIso (normalSurfaceStructureResolutionIso X α IX)
    (U.mapDerivedCategorySingleFunctor 0).inv.app (ModuleCat.of A A) ≫
        U.mapDerivedCategory.map
          (DerivedCategory.Plus.ι.map (moduleDerivedStructureUnit X α)) ≫ P.inv =
      DerivedCategory.Q.map ((U.mapCochainComplexSingleFunctor 0).inv.app
        (ModuleCat.of A A)) ≫
      DerivedCategory.Q.map ((U.mapHomologicalComplex (.up ℤ)).map
        (normalSurfaceStructureResolutionUnit X α IX)) := by
  let K := moduleResolutionSectionComplex X α IX
  let L := (singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)
  let U := ModuleCat.restrictScalars σ
  let U₁ := U.mapDerivedCategory
  let Q := DerivedCategory.Q (C := ModuleCat.{u} A)
  let QR := DerivedCategory.Q (C := ModuleCat.{u} R)
  let t := normalSurfaceStructureResolutionIso X α IX
  let κ : L ⟶ K := normalSurfaceStructureResolutionUnit X α IX
  let η := DerivedCategory.Plus.ι.map (moduleDerivedStructureUnit X α)
  let a := (U.mapDerivedCategorySingleFunctor 0).inv.app (ModuleCat.of A A)
  let m := U₁.map (Q.map κ)
  let e := U₁.mapIso t
  let k := U.mapDerivedCategoryFactors.app K
  let l := U.mapDerivedCategoryFactors.hom.app L
  let b := QR.map ((U.mapCochainComplexSingleFunctor 0).inv.app (ModuleCat.of A A))
  let f := QR.map ((U.mapHomologicalComplex (.up ℤ)).map κ)
  have hκ : Q.map κ ≫ t.hom = η := by
    have h := normalSurfaceStructureResolutionUnit_normalization X α IX
    simpa only [DerivedCategory.singleFunctorIsoCompQ, Iso.refl_hom,
      NatTrans.id_app, Category.id_comp] using h
  have hη : U₁.map η = m ≫ e.hom :=
    (congrArg U₁.map hκ.symm).trans (U₁.map_comp (Q.map κ) t.hom)
  have hn : m ≫ k.hom = l ≫ f := U.mapDerivedCategoryFactors.hom.naturality κ
  have hs : a ≫ l = b :=
    U.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app
      (ModuleCat.of A A)
  change a ≫ U₁.map η ≫ (e.inv ≫ k.hom) = b ≫ f
  exact original_restricted_unit_model a m e (U₁.map η) k l b f hη hn hs

end OriginalSourceModel

section OriginalCoefficientModel

variable {R A : Type u} [CommRing R] [CommRing A] (σ : R →+* A)

private theorem original_coinducedSingleHomologyIso_hom (M : ModuleCat.{u} A)
    (I : CochainComplex (ModuleCat.{u} R) ℤ) :
    (coinducedSingleHomologyIso σ M I 0).hom =
      (coinducedHomologyIso σ ((singleFunctor (ModuleCat.{u} A) 0).obj M) I 0).hom ≫
      homologyMap (precomp R
        (((ModuleCat.restrictScalars σ).mapCochainComplexSingleFunctor 0).inv.app M) I) 0 := by
  let U := ModuleCat.restrictScalars σ
  let K := (singleFunctor (ModuleCat.{u} A) 0).obj M
  let L := moduleComplex A K (coinducedCoefficientComplex σ I)
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℤ) 0
  let p := ((L.sc 0).mapHomologyIso U).symm
  let e := coinductionComplexIso σ K I
  let f := (moduleComplexFunctor R I).mapIso
    (((U.mapCochainComplexSingleFunctor 0).app M).symm.op)
  exact original_prefix_map_iso_trans_hom H p e f

/-- The original coinduction/single comparison retains every actual chain source map. -/
private theorem original_coinduced_single_precomp
    (M : ModuleCat.{u} A) (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (I : CochainComplex (ModuleCat.{u} R) ℤ) [I.IsKInjective]
    (f : ((singleFunctor (ModuleCat.{u} A) 0).obj M) ⟶ K)
    (x : (moduleComplex A K (coinducedCoefficientComplex σ I)).homology 0) :
    moduleHomologyDerivedLinearEquiv
        ((singleFunctor (ModuleCat.{u} R) 0).obj ((ModuleCat.restrictScalars σ).obj M)) I 0
        ((coinducedSingleHomologyIso σ M I 0).hom
          (homologyMap (precomp A f (coinducedCoefficientComplex σ I)) 0 x)) =
      DerivedCategory.Q.map
          (((ModuleCat.restrictScalars σ).mapCochainComplexSingleFunctor 0).inv.app M) ≫
        DerivedCategory.Q.map
          (((ModuleCat.restrictScalars σ).mapHomologicalComplex (.up ℤ)).map f) ≫
          coinducedHomologyDerivedAddEquiv σ K I 0 x := by
  let U := ModuleCat.restrictScalars σ
  let J := coinducedCoefficientComplex σ I
  let L := (singleFunctor (ModuleCat.{u} A) 0).obj M
  let L₀ := (singleFunctor (ModuleCat.{u} R) 0).obj (U.obj M)
  let L₁ := (U.mapHomologicalComplex (.up ℤ)).obj L
  let K₁ := (U.mapHomologicalComplex (.up ℤ)).obj K
  let v : L₀ ⟶ L₁ := (U.mapCochainComplexSingleFunctor 0).inv.app M
  let f₁ : L₁ ⟶ K₁ := (U.mapHomologicalComplex (.up ℤ)).map f
  let eL := coinducedHomologyIso σ L I 0
  let eK := coinducedHomologyIso σ K I 0
  let eM := coinducedSingleHomologyIso σ M I 0
  let z := homologyMap (precomp A f J) 0 x
  let N₀ : ModuleCat.{u} R := (moduleComplex R L₀ I).homology 0
  let N₁ : ModuleCat.{u} R := (moduleComplex R L₁ I).homology 0
  let N₂ : ModuleCat.{u} R := (moduleComplex R K₁ I).homology 0
  let D₀ : N₀ → (DerivedCategory.Q.obj L₀ ⟶ DerivedCategory.Q.obj (I⟦(0 : ℤ)⟧)) :=
    moduleHomologyDerivedValue.{u, u, u + 1} I 0 L₀
  let D₁ : N₁ → (DerivedCategory.Q.obj L₁ ⟶ DerivedCategory.Q.obj (I⟦(0 : ℤ)⟧)) :=
    moduleHomologyDerivedValue.{u, u, u + 1} I 0 L₁
  let D₂ : N₂ → (DerivedCategory.Q.obj K₁ ⟶ DerivedCategory.Q.obj (I⟦(0 : ℤ)⟧)) :=
    moduleHomologyDerivedValue.{u, u, u + 1} I 0 K₁
  have e₀ : (moduleHomologyDerivedLinearEquiv L₀ I 0 : N₀ → _) = D₀ :=
    moduleHomologyDerivedLinearEquiv_coe.{u, u, u + 1} I 0 L₀
  have e₁ : (moduleHomologyDerivedLinearEquiv L₁ I 0 : N₁ → _) = D₁ :=
    moduleHomologyDerivedLinearEquiv_coe.{u, u, u + 1} I 0 L₁
  have e₂ : (moduleHomologyDerivedLinearEquiv K₁ I 0 : N₂ → _) = D₂ :=
    moduleHomologyDerivedLinearEquiv_coe.{u, u, u + 1} I 0 K₁
  have hs := ConcreteCategory.congr_hom
    (original_coinducedSingleHomologyIso_hom σ M I) z
  change eM.hom z = homologyMap (precomp R v I) 0 (eL.hom z) at hs
  have hn := ConcreteCategory.congr_hom (coinducedHomologyIso_naturality σ f I 0) x
  change eL.hom z = homologyMap (precomp R f₁ I) 0 (eK.hom x) at hn
  have h₀ : D₀ (homologyMap (precomp R v I) 0 (eL.hom z)) =
      DerivedCategory.Q.map v ≫ D₁ (eL.hom z) :=
    (congrFun e₀ _).symm.trans
      ((moduleHomologyDerivedLinearEquiv_precomp.{u, u, u + 1} I 0 v (eL.hom z)).trans
        (congrArg (fun w => DerivedCategory.Q.map v ≫ w) (congrFun e₁ _)))
  have h₁ : D₁ (homologyMap (precomp R f₁ I) 0 (eK.hom x)) =
      DerivedCategory.Q.map f₁ ≫ D₂ (eK.hom x) :=
    (congrFun e₁ _).symm.trans
      ((moduleHomologyDerivedLinearEquiv_precomp.{u, u, u + 1} I 0 f₁ (eK.hom x)).trans
        (congrArg (fun w => DerivedCategory.Q.map f₁ ≫ w) (congrFun e₂ _)))
  have hvalue : D₀ (eM.hom z) =
      DerivedCategory.Q.map v ≫ DerivedCategory.Q.map f₁ ≫ D₂ (eK.hom x) :=
    (congrArg D₀ hs).trans (h₀.trans
      ((congrArg (fun y => DerivedCategory.Q.map v ≫ D₁ y) hn).trans
        (congrArg (fun y => DerivedCategory.Q.map v ≫ y) h₁)))
  have hcoind : coinducedHomologyDerivedAddEquiv σ K I 0 x = D₂ (eK.hom x) :=
    congrFun (coinducedHomologyDerivedAddEquiv_coe σ K I 0) x
  exact (congrFun e₀ (eM.hom z)).trans (hvalue.trans
    (congrArg (fun w => DerivedCategory.Q.map v ≫ DerivedCategory.Q.map f₁ ≫ w)
      hcoind.symm))

variable [HasExt.{u} (ModuleCat.{u} R)]

private theorem original_ext_zero_map (M N : ModuleCat.{u} R) (ξ : Ext.{u} M N 0) :
    (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map (Ext.addEquiv₀ ξ) =
      Ext.homLinearEquiv (R := R) ξ ≫
        (shiftFunctorZero (DerivedCategory (ModuleCat.{u} R)) ℤ).hom.app
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N) := by
  let S := DerivedCategory.singleFunctor (ModuleCat.{u} R) 0
  let Z : (S.obj N)⟦(0 : ℤ)⟧ ≅ S.obj N :=
    (shiftFunctorZero (DerivedCategory (ModuleCat.{u} R)) ℤ).app (S.obj N)
  have h : S.map (Ext.addEquiv₀ ξ) ≫ Z.inv = ξ.hom :=
    (surfaceUnitTrace_ext_mk_zero (Ext.addEquiv₀ ξ)).symm.trans
      (congrArg (fun t : Ext.{u} M N 0 => t.hom) (Ext.mk₀_addEquiv₀_apply ξ))
  calc
    _ = (S.map (Ext.addEquiv₀ ξ) ≫ Z.inv) ≫ Z.hom := by
      rw [Category.assoc, Z.inv_hom_id, Category.comp_id]
    _ = _ := congrArg (fun t => t ≫ Z.hom) h

/-- The original coefficient comparison in degree zero, before geometric specialization. -/
private theorem original_coinduced_zero_precomp
    (M : ModuleCat.{u} A) (N : ModuleCat.{u} R)
    (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (I : CochainComplex (ModuleCat.{u} R) ℤ) [I.IsKInjective]
    (u : ((singleFunctor (ModuleCat.{u} R) 0).obj N) ⟶ I) [QuasiIso u]
    (f : ((singleFunctor (ModuleCat.{u} A) 0).obj M) ⟶ K)
    (x : (moduleComplex A K (coinducedCoefficientComplex σ I)).homology 0) :
    (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map
        (Ext.addEquiv₀ (coinducedSingleHomologyExtLinearEquiv.{u, u, u, u + 1, u}
          σ M N I u 0 (homologyMap (precomp A f (coinducedCoefficientComplex σ I)) 0 x))) =
      DerivedCategory.Q.map
          (((ModuleCat.restrictScalars σ).mapCochainComplexSingleFunctor 0).inv.app M) ≫
        DerivedCategory.Q.map
          (((ModuleCat.restrictScalars σ).mapHomologicalComplex (.up ℤ)).map f) ≫
        coinducedHomologyDerivedAddEquiv σ K I 0 x ≫
        DerivedCategory.Q.map
          ((shiftFunctorZero (CochainComplex (ModuleCat.{u} R) ℤ) ℤ).hom.app I) ≫
        ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) 0).app N ≪≫
          asIso (DerivedCategory.Q.map u)).inv := by
  let U := ModuleCat.restrictScalars σ
  let Q := DerivedCategory.Q (C := ModuleCat.{u} R)
  let S := DerivedCategory.singleFunctor (ModuleCat.{u} R) 0
  let y := homologyMap (precomp A f (coinducedCoefficientComplex σ I)) 0 x
  let e := coinducedSingleHomologyIso.{u, u, u} σ M I 0
  let E :
      (moduleComplex R ((singleFunctor (ModuleCat.{u} R) 0).obj (U.obj M)) I).homology 0 ≃ₗ[R]
        Ext.{u} (U.obj M) N 0 :=
    singleHomologyExtLinearEquiv.{u, u, u + 1, u} (U.obj M) N I u 0
  let ξ := coinducedSingleHomologyExtLinearEquiv.{u, u, u, u + 1, u} σ M N I u 0 y
  have hξ : ξ = E (e.hom y) := surfaceUnitTrace_iso_linear_trans_apply e E y
  let a := Q.map ((U.mapCochainComplexSingleFunctor 0).inv.app M)
  let b := Q.map ((U.mapHomologicalComplex (.up ℤ)).map f)
  let d := coinducedHomologyDerivedAddEquiv σ K I 0 x
  let s := (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) 0).app (U.obj M)
  let T := coefficientShiftIso N I u (0 : ℤ)
  let Z : (S.obj N)⟦(0 : ℤ)⟧ ≅ S.obj N :=
    (shiftFunctorZero (DerivedCategory (ModuleCat.{u} R)) ℤ).app (S.obj N)
  let q := Q.map ((shiftFunctorZero (CochainComplex (ModuleCat.{u} R) ℤ) ℤ).hom.app I)
  let t := (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) 0).app N ≪≫
    asIso (Q.map u)
  have hp := original_coinduced_single_precomp σ M K I f x
  have hext : Ext.homLinearEquiv (R := R) ξ =
      s.hom ≫ moduleHomologyDerivedLinearEquiv.{u, u, u + 1}
        ((singleFunctor (ModuleCat.{u} R) 0).obj (U.obj M)) I 0 (e.hom y) ≫ T.inv :=
    (congrArg (Ext.homLinearEquiv (R := R)) hξ).trans
      (singleHomologyExtLinearEquiv_hom.{u, u, u + 1, u} (U.obj M) N I u 0 (e.hom y))
  have hhom : Ext.homLinearEquiv (R := R) ξ = s.hom ≫ (a ≫ b ≫ d) ≫ T.inv :=
    hext.trans (congrArg (fun w => s.hom ≫ w ≫ T.inv) hp)
  have hT : T.hom ≫ q = Z.hom ≫ t.hom := original_coefficient_shift_zero Q t
  have hTinv : T.inv ≫ Z.hom = q ≫ t.inv :=
    original_coefficient_zero_inverse T t q Z.hom hT
  calc
    _ = Ext.homLinearEquiv (R := R) ξ ≫ Z.hom := original_ext_zero_map _ _ ξ
    _ = (s.hom ≫ (a ≫ b ≫ d) ≫ T.inv) ≫ Z.hom :=
      congrArg (fun w => w ≫ Z.hom) hhom
    _ = _ := by
      change ((𝟙 _) ≫ (a ≫ b ≫ d) ≫ T.inv) ≫ Z.hom = _
      rw [Category.id_comp]
      simpa only [Category.assoc] using congrArg (fun w => (a ≫ b ≫ d) ≫ w) hTinv

end OriginalCoefficientModel

section OriginalUnitFunctional

variable {R A : Type u} [CommRing R] [CommRing A] [IsRegularLocalRing R]
  [IsLocalRing A] [IsNoetherianRing A] [IsDomain A] [IsIntegrallyClosed A]
  (σ : R →+* A) [IsLocalHom σ] (hσ : σ.Finite) (hσinj : Function.Injective σ)
  (hR : ringKrullDim R = 2) (hA : ringKrullDim A = 2)
  (X : Scheme.{u}) (α : A →+* Γ(X, ⊤))
  (IX : InjectiveResolution (normalSurfaceUnit X : X.Modules))
  (IR : InjectiveResolution (ModuleCat.of R R))

/-- The actual original dual unit, in the original restricted model coordinates.
Every comparison, zero shift and augmentation is retained; projectivity is derived. -/
theorem normalSurfaceDualUnit_model :
    letI : IR.cochainComplex.IsKInjective :=
      CochainComplex.isKInjective_of_injective IR.cochainComplex 0
    letI : Module.Projective R ((ModuleCat.restrictScalars σ).obj (ModuleCat.of A A)) :=
      restrictedProjective_of_finite_normal_dimension_two σ hσ hσinj hR hA
    let J := coinducedCoefficientComplex σ IR.cochainComplex
    let C := DerivedCategory.Plus.ι.obj (moduleDerivedStructure X α)
    let η := DerivedCategory.Plus.ι.map (moduleDerivedStructureUnit X α)
    let K := moduleResolutionSectionComplex X α IX
    let U := ModuleCat.restrictScalars σ
    let P := (U.mapDerivedCategoryFactors.app K).symm ≪≫
      U.mapDerivedCategory.mapIso (normalSurfaceStructureResolutionIso X α IX)
    let t := (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) 0).app
      (ModuleCat.of R R) ≪≫ asIso (DerivedCategory.Q.map IR.ι')
    ∀ z : TwoLayerDual.homology J 0 C,
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map
          (originalCoinducedFunctional σ (TwoLayerDual.unitMap σ IR C η z)) =
        (U.mapDerivedCategorySingleFunctor 0).inv.app (ModuleCat.of A A) ≫
          U.mapDerivedCategory.map η ≫ P.inv ≫
          coinducedHomologyDerivedAddEquiv σ K IR.cochainComplex 0
            ((normalSurfaceDerivedDualHomologyIso X α IX J 0).hom z) ≫
          DerivedCategory.Q.map
            ((shiftFunctorZero (CochainComplex (ModuleCat.{u} R) ℤ) ℤ).hom.app
              IR.cochainComplex) ≫ t.inv := by
  let : IR.cochainComplex.IsKInjective :=
    CochainComplex.isKInjective_of_injective IR.cochainComplex 0
  let : Module.Projective R ((ModuleCat.restrictScalars σ).obj (ModuleCat.of A A)) :=
    restrictedProjective_of_finite_normal_dimension_two σ hσ hσinj hR hA
  let J := coinducedCoefficientComplex σ IR.cochainComplex
  let C := DerivedCategory.Plus.ι.obj (moduleDerivedStructure X α)
  let η := DerivedCategory.Plus.ι.map (moduleDerivedStructureUnit X α)
  let K := moduleResolutionSectionComplex X α IX
  let U := ModuleCat.restrictScalars σ
  let Q := DerivedCategory.Q (C := ModuleCat.{u} R)
  let S := DerivedCategory.singleFunctor (ModuleCat.{u} R) 0
  let P := (U.mapDerivedCategoryFactors.app K).symm ≪≫
    U.mapDerivedCategory.mapIso (normalSurfaceStructureResolutionIso X α IX)
  let t := (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) 0).app
    (ModuleCat.of R R) ≪≫ asIso (Q.map IR.ι')
  refine fun z => ?_
  let κ := normalSurfaceStructureResolutionUnit X α IX
  let D := normalSurfaceDerivedDualHomologyIso X α IX J 0
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0
  let z₀ := H.map ((derivedDual J).map η.op) z
  let s := TwoLayerDual.singleHomologyIso J (ModuleCat.of A A) 0
  let x := D.hom z
  let y := homologyMap (precomp A κ J) 0 x
  let E := coinducedSingleHomologyExtLinearEquiv.{u, u, u, u + 1, u}
    σ (ModuleCat.of A A) (ModuleCat.of R R) IR.cochainComplex IR.ι' 0
  have hy : s.hom z₀ = y := ConcreteCategory.congr_hom
    (normalSurfaceDerivedDualHomologyIso_unit X α IX J) z
  have hcomp : TwoLayerDual.unitMap σ IR C η z =
      (TwoLayerDual.unitNormalization σ IR).hom z₀ :=
    surfaceUnitTrace_linear_comp_apply (H.map ((derivedDual J).map η.op))
      (TwoLayerDual.unitNormalization σ IR).hom z
  have hu : Ext.addEquiv₀ (E y) =
      originalCoinducedFunctional σ (TwoLayerDual.unitMap σ IR C η z) :=
    (congrArg (fun w => Ext.addEquiv₀ (E w)) hy.symm).trans
      ((TwoLayerDual.unitNormalization_ext_zero σ hσ hσinj hR hA IR z₀).trans
        (congrArg (originalCoinducedFunctional σ) hcomp.symm))
  let a := Q.map ((U.mapCochainComplexSingleFunctor 0).inv.app (ModuleCat.of A A))
  let b := Q.map ((U.mapHomologicalComplex (.up ℤ)).map κ)
  let d := coinducedHomologyDerivedAddEquiv σ K IR.cochainComplex 0 x
  let q := Q.map ((shiftFunctorZero (CochainComplex (ModuleCat.{u} R) ℤ) ℤ).hom.app
    IR.cochainComplex)
  have hvalue : S.map (Ext.addEquiv₀ (E y)) = a ≫ b ≫ d ≫ q ≫ t.inv :=
    original_coinduced_zero_precomp σ (ModuleCat.of A A) (ModuleCat.of R R)
      K IR.cochainComplex IR.ι' κ x
  have hsource : (U.mapDerivedCategorySingleFunctor 0).inv.app (ModuleCat.of A A) ≫
      U.mapDerivedCategory.map η ≫ P.inv = a ≫ b :=
    normalSurfaceRestrictedUnit_model X α IX σ
  exact (congrArg S.map hu.symm).trans (hvalue.trans (by
    simpa only [Category.assoc] using
      congrArg (fun w => w ≫ d ≫ q ≫ t.inv) hsource.symm))

end OriginalUnitFunctional

variable (R : Type u) [CommRing R] [IsDomain R] [IsRegularLocalRing R]
    (ι : Type u) {X : Scheme.{u}} [IsIntegral X]
    (i : X ⟶ ProjectiveSpace R ι) [IsClosedImmersion i]
    [IsDominant (i ≫ toSpec R ι)]
    (hX : NormalStalks X) (hXdim : topologicalKrullDim X ≤ 2)
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    (hfin : (genericImageBaseMap R ι i).Finite)

/-- The higher-degree canonical reconstruction specializes to the exact section reconstruction. -/
theorem normalSurfaceCanonicalDegreeIso_zero_hom :
    (normalSurfaceCanonicalDegreeIso R ι i hX hXdim n e hfin 0).hom ≫
        (shiftFunctorZero (DerivedCategory X.Modules) ℤ).hom.app
          ((DerivedCategory.singleFunctor X.Modules 0).obj
            (normalSurfaceCanonicalModule R ι i n)) =
      (normalSurfaceCanonicalShiftIso R ι i hX hXdim n e hfin).hom := by
  let ω : X.Modules := normalSurfaceCanonicalModule R ι i n
  let C := DerivedCategory.Plus.ι.obj (normalSurfaceDualizingObject R ι i n)
  let d : C ≅ (DerivedCategory.singleFunctor X.Modules (n : ℤ)).obj ω :=
    DerivedCategory.Plus.ι.mapIso (normalSurfaceCanonicalIso R ι i hX hXdim n e hfin)
  let a := (CategoryTheory.shiftFunctor (DerivedCategory X.Modules) (n : ℤ)).mapIso d
  let b := normalSurfaceSingleReindexIso ω n 0
  let c := (shiftFunctorZero (DerivedCategory X.Modules) ℤ).hom.app
    ((DerivedCategory.singleFunctor X.Modules 0).obj ω)
  let t := relativeClosedEmbeddingTraceTargetIso n ω
  have h : b.hom ≫ c = t.hom := normalSurfaceSingleReindexIso_zero ω n
  exact surfaceUnitTrace_iso_composite_hom a b c t h

/-- Its inverse retains the same native zero-shift comparison. -/
theorem normalSurfaceCanonicalDegreeIso_zero_inv :
    (shiftFunctorZero (DerivedCategory X.Modules) ℤ).inv.app
        ((DerivedCategory.singleFunctor X.Modules 0).obj
          (normalSurfaceCanonicalModule R ι i n)) ≫
      (normalSurfaceCanonicalDegreeIso R ι i hX hXdim n e hfin 0).inv =
    (normalSurfaceCanonicalShiftIso R ι i hX hXdim n e hfin).inv := by
  let ω : X.Modules := normalSurfaceCanonicalModule R ι i n
  let C := (DerivedCategory.Plus.ι.obj (normalSurfaceDualizingObject R ι i n))⟦(n : ℤ)⟧
  let S := (DerivedCategory.singleFunctor X.Modules 0).obj ω
  let E : C ≅ S⟦(0 : ℤ)⟧ := normalSurfaceCanonicalDegreeIso R ι i hX hXdim n e hfin 0
  let T : C ≅ S := normalSurfaceCanonicalShiftIso R ι i hX hXdim n e hfin
  let Z : S⟦(0 : ℤ)⟧ ≅ S := (shiftFunctorZero (DerivedCategory X.Modules) ℤ).app S
  have h : E.hom ≫ Z.hom = T.hom :=
    normalSurfaceCanonicalDegreeIso_zero_hom R ι i hX hXdim n e hfin
  exact surfaceUnitTrace_iso_composite_inv E Z T h

variable {A : Type u} [CommRing A] (α : A →+* Γ(X, ⊤))

/-- Degree-zero cohomology of an original module morphism has the exact original section lift. -/
theorem normalSurfaceCohomologyInput_zero_mk₀
    (f : (normalSurfaceUnit X : X.Modules) ⟶
      normalSurfaceCanonicalModule R ι i n) :
    normalSurfaceCohomologyInputLinearEquiv R ι i hX hXdim n e hfin α 0
        (moduleExtCohomologyMap X (normalSurfaceCanonicalModule R ι i n) 0 (Ext.mk₀ f)) =
      normalSurfaceCanonicalSectionsAddEquiv R ι i hX hXdim n e hfin
        (unitHomGlobalSectionsEquiv X (normalSurfaceCanonicalModule R ι i n) f) := by
  let := moduleCategoryLinearOfHom X α
  let O : X.Modules := normalSurfaceUnit X
  let ω : X.Modules := normalSurfaceCanonicalModule R ι i n
  let := moduleCohomologyModuleOfHom X α ω 0
  let H : Ext.{u + 1} (C := X.Modules) O ω 0 ≃ₗ[A]
      Sheaf.H.{u + 1} (moduleAddSheaf X ω) 0 :=
    moduleExtCohomologyLinearEquivOfCategory X α ω 0
  let F := DerivedCategory.singleFunctor X.Modules 0
  let D : Ext.{u + 1} (C := X.Modules) O ω 0 ≃ₗ[A]
      (F.obj O ⟶ (F.obj ω)⟦(0 : ℤ)⟧) :=
    Ext.homLinearEquiv (R := A) (X := O) (Y := ω) (n := 0)
  let E := normalSurfaceCanonicalDegreeIso R ι i hX hXdim n e hfin 0
  let G : (O ⟶ ω) ≃+ Γ(ω, ⊤) := unitHomGlobalSectionsAddEquiv X ω
  have hH : H.symm (moduleExtCohomologyMap X ω 0 (Ext.mk₀ f)) = Ext.mk₀ f :=
    H.symm_apply_apply (Ext.mk₀ f)
  let T := normalSurfaceCanonicalShiftIso R ι i hX hXdim n e hfin
  let Z : (F.obj ω)⟦(0 : ℤ)⟧ ≅ F.obj ω :=
    (shiftFunctorZero (DerivedCategory X.Modules) ℤ).app (F.obj ω)
  have hD : D (Ext.mk₀ f) = F.map f ≫ Z.inv := surfaceUnitTrace_ext_mk_zero f
  have hZ : Z.inv ≫ E.inv = T.inv :=
    normalSurfaceCanonicalDegreeIso_zero_inv R ι i hX hXdim n e hfin
  have hleft : D (Ext.mk₀ f) ≫ E.inv = F.map f ≫ T.inv :=
    (congrArg (fun w => w ≫ E.inv) hD).trans
      (surfaceUnitTrace_postcompose (F.map f) Z.inv E.inv T.inv hZ)
  have hG : G.symm (unitHomGlobalSectionsEquiv X ω f) = f := G.symm_apply_apply f
  have hright : normalSurfaceCanonicalSectionsAddEquiv R ι i hX hXdim n e hfin
      (unitHomGlobalSectionsEquiv X ω f) = F.map f ≫ T.inv :=
    (normalSurfaceCanonicalSectionsAddEquiv_apply R ι i hX hXdim n e hfin
      (unitHomGlobalSectionsEquiv X ω f)).trans
      (congrArg (fun w => F.map w ≫ T.inv) hG)
  change ((𝟙 _) ≫ D (H.symm (moduleExtCohomologyMap X ω 0 (Ext.mk₀ f)))) ≫ E.inv = _
  rw [Category.id_comp, hH]
  exact hleft.trans hright.symm

/-- The actual original H0/sections equivalence normalizes the SAME degree-zero source map. -/
theorem normalSurfaceCohomologyInput_zero_sections
    (x : Sheaf.H.{u + 1} (moduleAddSheaf X (normalSurfaceCanonicalModule R ι i n)) 0) :
    normalSurfaceCohomologyInputLinearEquiv R ι i hX hXdim n e hfin α 0 x =
      normalSurfaceCanonicalSectionsAddEquiv R ι i hX hXdim n e hfin
        (Sheaf.H.equiv₀ (moduleAddSheaf X (normalSurfaceCanonicalModule R ι i n))
          isTerminalTop x) := by
  obtain ⟨y, rfl⟩ := (moduleExtCohomologyMap_bijective X
    (normalSurfaceCanonicalModule R ι i n) 0).surjective x
  obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective
    (normalSurfaceUnit X : X.Modules)
    (normalSurfaceCanonicalModule R ι i n)).surjective y
  exact (normalSurfaceCohomologyInput_zero_mk₀ R ι i hX hXdim n e hfin α f).trans
    (congrArg (normalSurfaceCanonicalSectionsAddEquiv R ι i hX hXdim n e hfin)
      (moduleExtCohomologyMap_mk₀_sections X (normalSurfaceCanonicalModule R ι i n) f).symm)

omit [IsDomain R] [IsRegularLocalRing R] [IsIntegral X]
  [IsDominant (i ≫ toSpec R ι)] in
/-- The affine comparison can be expressed using the actual native shifted-Hom map. -/
theorem normalSurfaceAffineHomAddEquiv_shifted_apply (r : ℕ)
    (f : DerivedCategory.Plus.ι.obj ((derivedPushforwardPlus (i ≫ toSpec R ι)).obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj
          (normalSurfaceUnit X))) ⟶
      ((DerivedCategory.singleFunctor (Spec (.of R)).Modules 0).obj
        (normalSurfaceUnit (Spec (.of R))))⟦(r : ℤ)⟧) :
    let Y := Spec (.of R)
    let L := (DerivedCategory.Plus.singleFunctor Y.Modules 0).obj
      (normalSurfaceUnit Y)
    let F := (moduleGlobalSectionsFunctorOfHom Y (ΓSpecIso (.of R)).inv.hom).rightDerivedFunctorPlus
    let C := (moduleDerivedGlobalSectionsPushforwardCompIso (i ≫ toSpec R ι)
      (ΓSpecIso (.of R)).inv.hom).app
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj
          (normalSurfaceUnit X))
    normalSurfaceAffineHomAddEquiv R ι i n e r f =
      DerivedCategory.Plus.ι.map C.hom ≫
        ShiftedHom.map (DerivedCategory.Plus.ι.preimage
          (f ≫ (DerivedCategory.Plus.ι.commShiftIso (r : ℤ)).inv.app L))
            (F ⋙ DerivedCategory.Plus.ι) ≫
        (DerivedCategory.Plus.ι.map (affineDerivedStructureTargetIso (.of R)).hom)⟦(r : ℤ)⟧' := by
  let Y := Spec (.of R)
  let OX : X.Modules := normalSurfaceUnit X
  let OY : Y.Modules := normalSurfaceUnit Y
  let SX := DerivedCategory.Plus.singleFunctor X.Modules 0
  let P := derivedPushforwardPlus (i ≫ toSpec R ι)
  let K := P.obj (SX.obj OX)
  let L := (DerivedCategory.Plus.singleFunctor Y.Modules 0).obj OY
  let F := (moduleGlobalSectionsFunctorOfHom Y (ΓSpecIso (.of R)).inv.hom).rightDerivedFunctorPlus
  let IY : DerivedCategory.Plus Y.Modules ⥤ DerivedCategory Y.Modules := DerivedCategory.Plus.ι
  let IR : DerivedCategory.Plus (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R) :=
    DerivedCategory.Plus.ι
  let N := (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)
  let C : moduleDerivedStructure X (chosenEmbeddingBaseScalar R i (toSpec R ι)) ≅ F.obj K :=
    (moduleDerivedGlobalSectionsPushforwardCompIso
      (i ≫ toSpec R ι) (ΓSpecIso (.of R)).inv.hom).app (SX.obj OX)
  let t : F.obj L ≅ N := affineDerivedStructureTargetIso (.of R)
  let g : K ⟶ L⟦(r : ℤ)⟧ :=
    IY.preimage (f ≫ (IY.commShiftIso (r : ℤ)).inv.app L)
  exact (normalSurfaceAffineHomAddEquiv_apply R ι i n e r f).trans
    (surfaceUnitTrace_affine_shifted_value F IR (r : ℤ) (IR.map C.hom) g t)

omit [IsDomain R] [IsRegularLocalRing R] [IsIntegral X]
  [IsDominant (i ≫ toSpec R ι)] in
/-- Native zero-shift cancellation recovers the SAME ordinary module-valued affine map. -/
theorem normalSurfaceAffineHomAddEquiv_zero
    (f : DerivedCategory.Plus.ι.obj ((derivedPushforwardPlus (i ≫ toSpec R ι)).obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj
          (normalSurfaceUnit X))) ⟶
      (DerivedCategory.singleFunctor (Spec (.of R)).Modules 0).obj
        (normalSurfaceUnit (Spec (.of R)))) :
    normalSurfaceAffineHomAddEquiv R ι i n e 0
        (ShiftedHom.mk₀ (0 : ℤ) rfl f) ≫
        (shiftFunctorZero (DerivedCategory (ModuleCat.{u} R)) ℤ).hom.app
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) =
      DerivedCategory.Plus.ι.map
        ((moduleDerivedGlobalSectionsPushforwardCompIso (i ≫ toSpec R ι)
          (ΓSpecIso (.of R)).inv.hom).hom.app
            ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj
              (normalSurfaceUnit X)) ≫
          (moduleGlobalSectionsFunctorOfHom (Spec (.of R))
            (ΓSpecIso (.of R)).inv.hom).rightDerivedFunctorPlus.map
              (DerivedCategory.Plus.ι.preimage
                (X := (derivedPushforwardPlus (i ≫ toSpec R ι)).obj
                  ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj (normalSurfaceUnit X)))
                (Y := (DerivedCategory.Plus.singleFunctor (Spec (.of R)).Modules 0).obj
                  (normalSurfaceUnit (Spec (.of R)))) f) ≫
          (affineDerivedStructureTargetIso (.of R)).hom) := by
  let Y := Spec (.of R)
  let OX : X.Modules := normalSurfaceUnit X
  let OY : Y.Modules := normalSurfaceUnit Y
  let SX := DerivedCategory.Plus.singleFunctor X.Modules 0
  let P := derivedPushforwardPlus (i ≫ toSpec R ι)
  let K := P.obj (SX.obj OX)
  let L := (DerivedCategory.Plus.singleFunctor Y.Modules 0).obj OY
  let F := (moduleGlobalSectionsFunctorOfHom Y (ΓSpecIso (.of R)).inv.hom).rightDerivedFunctorPlus
  let IY : DerivedCategory.Plus Y.Modules ⥤ DerivedCategory Y.Modules := DerivedCategory.Plus.ι
  let IR : DerivedCategory.Plus (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R) :=
    DerivedCategory.Plus.ι
  let N := (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)
  let C : moduleDerivedStructure X (chosenEmbeddingBaseScalar R i (toSpec R ι)) ≅ F.obj K :=
    (moduleDerivedGlobalSectionsPushforwardCompIso
      (i ≫ toSpec R ι) (ΓSpecIso (.of R)).inv.hom).app (SX.obj OX)
  let t : F.obj L ≅ N := affineDerivedStructureTargetIso (.of R)
  let Z := (shiftFunctorZero (DerivedCategory (ModuleCat.{u} R)) ℤ).hom.app (IR.obj N)
  let a := ShiftedHom.map
    (IY.preimage (ShiftedHom.mk₀ (0 : ℤ) rfl f ≫ (IY.commShiftIso (0 : ℤ)).inv.app L))
      (F ⋙ IR)
  let b := (IR.map t.hom)⟦(0 : ℤ)⟧'
  have hvalue := normalSurfaceAffineHomAddEquiv_shifted_apply
    R ι i n e 0 (ShiftedHom.mk₀ (0 : ℤ) rfl f)
  have hzero : IR.map C.hom ≫ a ≫ b ≫ Z =
      IR.map C.hom ≫ IR.map (F.map (IY.preimage (X := K) (Y := L) f)) ≫ IR.map t.hom :=
    affine_shifted_zero F IY IR (IR.map C.hom) t.hom f
  exact (congrArg (fun k => k ≫ Z) hvalue).trans
    ((surfaceUnitTrace_three_postcompose (IR.map C.hom) a b Z).trans
      (hzero.trans (surfaceUnitTrace_map_three IR C.hom
        (F.map (IY.preimage (X := K) (Y := L) f)) t.hom).symm))

omit [IsDomain R] [IsIntegral X] [IsDominant (i ≫ toSpec R ι)] in
/-- The degree-zero geometric comparison is exactly the previously normalized SAME Phi. -/
theorem normalSurfaceDerivedSerreAddEquiv_zero
    (s : chosenEmbeddingUnitTraceSource R i (toSpec R ι) n) :
    normalSurfaceDerivedSerreAddEquiv R ι i n e 0 s ≫
        (shiftFunctorZero (DerivedCategory (ModuleCat.{u} R)) ℤ).hom.app
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) =
      DerivedCategory.Plus.ι.map
        (chosenEmbeddingModuleSerreMap R ι i (toSpec R ι) (𝟙 (ProjectiveSpace R ι))
          (IsPullback.id_horiz (toSpec R ι)) n e s) := by
  let Y := Spec (.of R)
  let OY : Y.Modules := normalSurfaceUnit Y
  let : OY.IsQuasicoherent := isQuasicoherent_unit Y
  let raw := relativeClosedEmbeddingSerreMap i (toSpec R ι) R ι (𝟙 _) (𝟙 _)
    (IsPullback.id_horiz (toSpec R ι)) n e OY (normalSurfaceUnit X) n s
  let γ := relativeClosedEmbeddingDegreeZeroSerreMap i (toSpec R ι) R ι (𝟙 _) (𝟙 _)
    (IsPullback.id_horiz (toSpec R ι)) n e OY (normalSurfaceUnit X) s
  let S := (DerivedCategory.singleFunctor Y.Modules 0).obj OY
  let Z : S⟦(0 : ℤ)⟧ ≅ S := (shiftFunctorZero (DerivedCategory Y.Modules) ℤ).app S
  let T := normalSurfaceSingleReindexIso OY n 0
  let T₀ := relativeClosedEmbeddingTraceTargetIso n OY
  have hT : T.hom ≫ Z.hom = T₀.hom := normalSurfaceSingleReindexIso_zero OY n
  have hγ : raw ≫ T₀.hom = γ := rfl
  have hpost : (raw ≫ T.hom) ≫ Z.hom = γ :=
    (surfaceUnitTrace_postcompose raw T.hom Z.hom T₀.hom hT).trans hγ
  have ht : raw ≫ T.hom = ShiftedHom.mk₀ (0 : ℤ) rfl γ :=
    (surfaceUnitTrace_right_cancel_iso Z _ _ hpost).trans (surfaceUnitTrace_mk_zero γ).symm
  let E := normalSurfaceSerreDegreeAddEquiv R ι i n e 0
  let G := normalSurfaceAffineHomAddEquiv R ι i n e 0
  let W := (shiftFunctorZero (DerivedCategory (ModuleCat.{u} R)) ℤ).hom.app
    ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))
  have hvalue : normalSurfaceDerivedSerreAddEquiv R ι i n e 0 s = G (raw ≫ T.hom) :=
    surfaceUnitTrace_serre_composite_apply E T G s
  exact (congrArg (fun k => k ≫ W) hvalue).trans
    ((congrArg (fun k => G k ≫ W) ht).trans
      (normalSurfaceAffineHomAddEquiv_zero R ι i n e γ))

variable (σ : R →+* A) (g : X ⟶ Spec (.of A))
    (hg : i ≫ toSpec R ι = g ≫ Spec.map (CommRingCat.ofHom σ))
    (IX : InjectiveResolution (normalSurfaceUnit X : X.Modules))
    (IR : InjectiveResolution (ModuleCat.of R R))

/-- The original cohomology model comparison in degree zero is exactly the existing
section Phi0 after the actual source-model maps and the original coefficient augmentation. -/
theorem normalSurfaceCohomologyModel_zero_phi0
    (x : Sheaf.H.{u + 1} (moduleAddSheaf X (normalSurfaceCanonicalModule R ι i n)) 0) :
    normalSurfaceCohomologyModelAddEquiv R ι i hX hXdim n e hfin σ g hg IX IR 0 x ≫
        DerivedCategory.Q.map
          ((shiftFunctorZero (CochainComplex (ModuleCat.{u} R) ℤ) ℤ).hom.app
            IR.cochainComplex) =
      ((ModuleCat.restrictScalars σ).mapDerivedCategoryFactors.app
        (moduleResolutionSectionComplex X (normalSurfaceTraceScalar g) IX)).inv ≫
      (ModuleCat.restrictScalars σ).mapDerivedCategory.map
        (normalSurfaceStructureResolutionIso X (normalSurfaceTraceScalar g) IX).hom ≫
      normalSurfaceSectionsPhi0 R ι i hX hXdim n e hfin σ g hg
        (Sheaf.H.equiv₀ (moduleAddSheaf X (normalSurfaceCanonicalModule R ι i n))
          isTerminalTop x) ≫
      (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) 0).hom.app
        (ModuleCat.of R R) ≫ DerivedCategory.Q.map IR.ι' := by
  let αA := normalSurfaceTraceScalar g
  let αR := chosenEmbeddingBaseScalar R i (toSpec R ι)
  let hα := normalSurfaceTraceScalar_compatibility R ι i σ g hg
  let := moduleCategoryLinearOfHom X αA
  let := moduleCohomologyModuleOfHom X αA (normalSurfaceCanonicalModule R ι i n) 0
  let K := moduleResolutionSectionComplex X αA IX
  let U := ModuleCat.restrictScalars σ
  let Q := DerivedCategory.Q (C := ModuleCat.{u} R)
  let E := normalSurfaceCohomologyInputLinearEquiv R ι i hX hXdim n e hfin αA 0
  let Φ := normalSurfaceDerivedSerreAddEquiv R ι i n e 0
  let s := Sheaf.H.equiv₀ (moduleAddSheaf X (normalSurfaceCanonicalModule R ι i n))
    isTerminalTop x
  let s' := normalSurfaceCanonicalSectionsAddEquiv R ι i hX hXdim n e hfin s
  let γ := DerivedCategory.Plus.ι.map
    (chosenEmbeddingModuleSerreMap R ι i (toSpec R ι) (𝟙 (ProjectiveSpace R ι))
      (IsPullback.id_horiz (toSpec R ι)) n e s')
  let Z := (shiftFunctorZero (DerivedCategory (ModuleCat.{u} R)) ℤ).app
    ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))
  have hE : E x = s' :=
    normalSurfaceCohomologyInput_zero_sections R ι i hX hXdim n e hfin αA x
  have hΦ : Φ (E x) ≫ Z.hom = γ :=
    (congrArg (fun z => Φ z ≫ Z.hom) hE).trans
      (normalSurfaceDerivedSerreAddEquiv_zero R ι i n e s')
  let a := (U.mapDerivedCategoryFactors.app K).inv
  let b := U.mapDerivedCategory.map (normalSurfaceStructureResolutionIso X αA IX).hom
  let c := (moduleDerivedStructureRestrictionIso X σ αA αR hα).inv
  let T := coefficientShiftIso (ModuleCat.of R R) IR.cochainComplex IR.ι' (0 : ℤ)
  let q := Q.map ((shiftFunctorZero (CochainComplex (ModuleCat.{u} R) ℤ) ℤ).hom.app
    IR.cochainComplex)
  let t := (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) 0).app
    (ModuleCat.of R R) ≪≫ asIso (Q.map IR.ι')
  have hT : T.hom ≫ q = Z.hom ≫ t.hom := original_coefficient_shift_zero Q t
  change (((a ≫ b ≫ c) ≫ Φ (E x)) ≫ T.hom) ≫ q =
    a ≫ b ≫ (c ≫ γ) ≫ t.hom
  exact original_model_value_normalization a b c (Φ (E x)) T.hom q Z.hom t.hom γ hΦ hT

variable [IsLocalRing A] [IsNoetherianRing A] [IsDomain A] [IsIntegrallyClosed A]
    [IsLocalHom σ] (hσ : σ.Finite) (hσinj : Function.Injective σ)
    (hR : ringKrullDim R = 2) (hA : ringKrullDim A = 2)

/-- The original dual unit on actual canonical H0 is exactly the existing section trace,
under the unchanged cohomology/sections normalization. No compatibility is assumed. -/
theorem normalSurfaceCohomologyDual_unit_trace
    (x : Sheaf.H.{u + 1} (moduleAddSheaf X (normalSurfaceCanonicalModule R ι i n)) 0) :
    letI : Module.Projective R ((ModuleCat.restrictScalars σ).obj (ModuleCat.of A A)) :=
      restrictedProjective_of_finite_normal_dimension_two σ hσ hσinj hR hA
    TwoLayerDual.unitMap σ IR
        (DerivedCategory.Plus.ι.obj (moduleDerivedStructure X (normalSurfaceTraceScalar g)))
        (DerivedCategory.Plus.ι.map (moduleDerivedStructureUnit X (normalSurfaceTraceScalar g)))
        (normalSurfaceCohomologyDualLinearEquiv R ι i hX hXdim n e hfin σ g hg IX IR 0 x) =
      normalSurfaceSectionsTraceCoinduced R ι i hX hXdim n e hfin σ g hg
        (Sheaf.H.equiv₀ (moduleAddSheaf X (normalSurfaceCanonicalModule R ι i n))
          isTerminalTop x) := by
  let : Module.Projective R ((ModuleCat.restrictScalars σ).obj (ModuleCat.of A A)) :=
    restrictedProjective_of_finite_normal_dimension_two σ hσ hσinj hR hA
  let : IR.cochainComplex.IsKInjective :=
    CochainComplex.isKInjective_of_injective IR.cochainComplex 0
  let αA := normalSurfaceTraceScalar g
  let := moduleCategoryLinearOfHom X αA
  let := moduleCohomologyModuleOfHom X αA (normalSurfaceCanonicalModule R ι i n) 0
  let J := coinducedCoefficientComplex σ IR.cochainComplex
  let C := DerivedCategory.Plus.ι.obj (moduleDerivedStructure X αA)
  let η := DerivedCategory.Plus.ι.map (moduleDerivedStructureUnit X αA)
  let K := moduleResolutionSectionComplex X αA IX
  let U := ModuleCat.restrictScalars σ
  let Q := DerivedCategory.Q (C := ModuleCat.{u} R)
  let S := DerivedCategory.singleFunctor (ModuleCat.{u} R) 0
  let eK := normalSurfaceStructureResolutionIso X αA IX
  let P := (U.mapDerivedCategoryFactors.app K).symm ≪≫ U.mapDerivedCategory.mapIso eK
  let t₀ := (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) 0).app
    (ModuleCat.of R R)
  let j := asIso (Q.map IR.ι')
  let t := t₀ ≪≫ j
  let q := Q.map ((shiftFunctorZero (CochainComplex (ModuleCat.{u} R) ℤ) ℤ).hom.app
    IR.cochainComplex)
  let s := Sheaf.H.equiv₀ (moduleAddSheaf X (normalSurfaceCanonicalModule R ι i n))
    isTerminalTop x
  let γ := normalSurfaceSectionsPhi0 R ι i hX hXdim n e hfin σ g hg s
  let E := normalSurfaceCohomologyModelAddEquiv R ι i hX hXdim n e hfin σ g hg IX IR 0
  let D := normalSurfaceDualModelAddEquiv R σ g IX IR 0
  let z := normalSurfaceCohomologyDualLinearEquiv R ι i hX hXdim n e hfin σ g hg IX IR 0 x
  have hz : D z = E x := by
    have h := normalSurfaceCohomologyDualLinearEquiv_apply
      R ι i hX hXdim n e hfin σ g hg IX IR 0 x
    refine (congrArg D h).trans ?_
    change D (D.symm (E x)) = E x
    exact D.apply_symm_apply (E x)
  have hmodel : E x ≫ q = P.hom ≫ γ ≫ t.hom :=
    (normalSurfaceCohomologyModel_zero_phi0 R ι i hX hXdim n e hfin σ g hg IX IR x).trans
      (original_source_coefficient_reassociate (U.mapDerivedCategoryFactors.app K)
        (U.mapDerivedCategory.mapIso eK) γ t₀ j)
  have hv : D z ≫ q = P.hom ≫ γ ≫ t.hom :=
    (congrArg (fun w => w ≫ q) hz).trans hmodel
  have hc : P.inv ≫ D z ≫ q ≫ t.inv = γ :=
    original_normalized_model_cancel P t (D z) q γ hv
  have hu := normalSurfaceDualUnit_model σ hσ hσinj hR hA X αA IX IR z
  change S.map (originalCoinducedFunctional σ (TwoLayerDual.unitMap σ IR C η z)) =
    (U.mapDerivedCategorySingleFunctor 0).inv.app (ModuleCat.of A A) ≫
      U.mapDerivedCategory.map η ≫ P.inv ≫ D z ≫ q ≫ t.inv at hu
  have hunit : S.map (originalCoinducedFunctional σ (TwoLayerDual.unitMap σ IR C η z)) =
      (U.mapDerivedCategorySingleFunctor 0).inv.app (ModuleCat.of A A) ≫
        U.mapDerivedCategory.map η ≫ γ :=
    hu.trans (congrArg (fun w =>
      (U.mapDerivedCategorySingleFunctor 0).inv.app (ModuleCat.of A A) ≫
        U.mapDerivedCategory.map η ≫ w) hc)
  apply (ModuleCat.CoextendScalars.equiv σ (ModuleCat.of R R)).injective
  ext a
  have htrace := normalSurfaceSectionsTraceCoinduced_eq_original_unit
    R ι i hX hXdim n e hfin σ g hg a s
  change ModuleCat.CoextendScalars.equiv σ (ModuleCat.of R R)
      (normalSurfaceSectionsTraceCoinduced R ι i hX hXdim n e hfin σ g hg s) a =
    (S.preimage ((U.mapDerivedCategorySingleFunctor 0).inv.app (ModuleCat.of A A) ≫
      U.mapDerivedCategory.map η ≫ γ)) a at htrace
  let ψ : U.obj (ModuleCat.of A A) ⟶ ModuleCat.of R R :=
    originalCoinducedFunctional σ (TwoLayerDual.unitMap σ IR C η z)
  have hpre : S.preimage ((U.mapDerivedCategorySingleFunctor 0).inv.app (ModuleCat.of A A) ≫
      U.mapDerivedCategory.map η ≫ γ) = ψ :=
    (congrArg (fun f : S.obj (U.obj (ModuleCat.of A A)) ⟶ S.obj (ModuleCat.of R R) =>
      S.preimage f) hunit.symm).trans (S.preimage_map ψ)
  exact (htrace.trans (ConcreteCategory.congr_hom hpre a)).symm

/-- Evaluating the original dual unit at a is the unchanged base trace of a times
its literal canonical section, with the native coinduction A-action. -/
theorem normalSurfaceCohomologyDual_unit_trace_evaluation (a : A)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf X (normalSurfaceCanonicalModule R ι i n)) 0) :
    letI : Module.Projective R ((ModuleCat.restrictScalars σ).obj (ModuleCat.of A A)) :=
      restrictedProjective_of_finite_normal_dimension_two σ hσ hσinj hR hA
    letI := moduleCategoryLinearOfHom X (normalSurfaceTraceScalar g)
    letI : Module A Γ(normalSurfaceCanonicalModule R ι i n, ⊤) :=
      Module.compHom _ (normalSurfaceTraceScalar g)
    ModuleCat.CoextendScalars.equiv σ (ModuleCat.of R R)
        (TwoLayerDual.unitMap σ IR
          (DerivedCategory.Plus.ι.obj (moduleDerivedStructure X (normalSurfaceTraceScalar g)))
          (DerivedCategory.Plus.ι.map
            (moduleDerivedStructureUnit X (normalSurfaceTraceScalar g)))
          (normalSurfaceCohomologyDualLinearEquiv R ι i hX hXdim n e hfin σ g hg IX IR 0 x)) a =
      normalSurfaceSectionsTraceBase R ι i hX hXdim n e hfin
        (a • (show Γ(normalSurfaceCanonicalModule R ι i n, ⊤) from
          Sheaf.H.equiv₀ (moduleAddSheaf X (normalSurfaceCanonicalModule R ι i n))
            isTerminalTop x)) := by
  let : Module.Projective R ((ModuleCat.restrictScalars σ).obj (ModuleCat.of A A)) :=
    restrictedProjective_of_finite_normal_dimension_two σ hσ hσinj hR hA
  let := moduleCategoryLinearOfHom X (normalSurfaceTraceScalar g)
  let : Module A Γ(normalSurfaceCanonicalModule R ι i n, ⊤) :=
    Module.compHom _ (normalSurfaceTraceScalar g)
  rw [normalSurfaceCohomologyDual_unit_trace R ι i hX hXdim n e hfin
    σ g hg IX IR hσ hσinj hR hA x]
  exact normalSurfaceSectionsTraceCoinduced_evaluation
    R ι i hX hXdim n e hfin σ g hg a _

end AlgebraicGeometry.Scheme.Cohomology
