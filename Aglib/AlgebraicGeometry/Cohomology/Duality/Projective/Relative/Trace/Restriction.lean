/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.AffineTrace
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Restriction.Composition
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Affine.Locality

/-!
# Original restriction pasting for the relative projective trace

The native differential-coefficient and higher-image restrictions paste on
Cartesian open squares, including the actual identity-restriction comparisons.
This internal support retains the original maps without projective or finiteness
hypotheses.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Differentials
universe u
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory

namespace AlgebraicGeometry.Scheme.Cohomology.RelativeProjectiveTrace
section RestrictionPasting
variable
    {X₀ X₁ X₂ Y₀ Y₁ Y₂ : Scheme.{u}}
    (p₀ : X₀ ⟶ Y₀) (p₁ : X₁ ⟶ Y₁) (p₂ : X₂ ⟶ Y₂)
    (i : X₁ ⟶ X₀) (j : Y₁ ⟶ Y₀) (k : X₂ ⟶ X₁) (l : Y₂ ⟶ Y₁)
    [IsOpenImmersion i] [IsOpenImmersion j]
    [IsOpenImmersion k] [IsOpenImmersion l]
    (h : i ≫ p₀ = p₁ ≫ j) (h' : k ≫ p₁ = p₂ ≫ l)
    (H : (k ≫ i) ≫ p₀ = p₂ ≫ (l ≫ j))
theorem relativeDifferentialOpenSquareIso_comp_inv :
    (relativeDifferentialOpenSquareIso p₀ (k ≫ i) p₂ (l ≫ j) H).inv =
      (relativeDifferentialOpenSquareIso p₁ k p₂ l h').inv ≫
        (Modules.restrictFunctor k).map
          (relativeDifferentialOpenSquareIso p₀ i p₁ j h).inv ≫
        (restrictFunctorComp k i).inv.app (relativeDifferentialSheaf p₀) := by
  let O₀ : X₀.Modules := SheafOfModules.unit X₀.ringCatSheaf
  have hu : (restrictFunctorComp k i).app O₀ ≪≫
      (Modules.restrictFunctor k).mapIso (restrictUnitIso i) ≪≫ restrictUnitIso k =
        restrictUnitIso (k ≫ i) := Iso.ext (restrictUnitIso_comp k i)
  apply relativeDifferentialSheaf_hom_ext p₂ _
  intro U a
  let V := U.unop
  let rc := (restrictFunctorComp k i).inv.app (relativeDifferentialSheaf p₀)
  let ρ := (restrictFunctorComp k i).inv.app O₀
  have hs := congrArg (fun t : O₀.restrict (k ≫ i) ≅
      (SheafOfModules.unit X₂.ringCatSheaf : X₂.Modules) =>
    Scheme.Modules.Hom.app t.inv V a) hu
  change ρ.app V ((i.appIso (k ''ᵁ V)).inv ((k.appIso V).inv a)) =
    ((k ≫ i).appIso V).inv a at hs
  have h₀ := relativeDifferentialOpenSquareIso_inv_d p₀ (k ≫ i) p₂ (l ≫ j) H V a
  have h₂ := relativeDifferentialOpenSquareIso_inv_d p₁ k p₂ l h' V a
  have h₁ := relativeDifferentialOpenSquareIso_inv_d p₀ i p₁ j h (k ''ᵁ V)
    ((k.appIso V).inv a)
  have ht₂ := congrArg (fun z => rc.app V (((Modules.restrictFunctor k).map
        (relativeDifferentialOpenSquareIso p₀ i p₁ j h).inv).app V z)) h₂
  have ht₁ := congrArg (fun z => rc.app V z) h₁
  have hr : rc.app V
      ((relativeDifferentialDerivation p₀).d ((i.appIso (k ''ᵁ V)).inv ((k.appIso V).inv a))) =
      (relativeDifferentialDerivation p₀).d
        (ρ.app V ((i.appIso (k ''ᵁ V)).inv ((k.appIso V).inv a))) := by
    have eV : (k ≫ i) ''ᵁ V = i ''ᵁ (k ''ᵁ V) := by simp
    let z : Γ(X₀, i ''ᵁ (k ''ᵁ V)) :=
      (i.appIso (k ''ᵁ V)).inv ((k.appIso V).inv a)
    change (relativeDifferentialSheaf p₀).val.map (eqToHom eV).op
      ((relativeDifferentialDerivation p₀).d z) =
        (relativeDifferentialDerivation p₀).d (X₀.presheaf.map (eqToHom eV).op z)
    exact (relativeDifferentialDerivation_restrict p₀ (eqToHom eV).op z).symm
  have ht := ht₂.trans (ht₁.trans (hr.trans
    (congrArg (fun z => (relativeDifferentialDerivation p₀).d z) hs)))
  exact h₀.trans ht.symm
private theorem exteriorRestriction_comp {X₀ X₁ X₂ : Scheme.{u}}
    (i : X₁ ⟶ X₀) (k : X₂ ⟶ X₁) [IsOpenImmersion i] [IsOpenImmersion k]
    (M : X₀.Modules) (n : ℕ) :
    (moduleExteriorPowerRestrictionIso (k ≫ i) M n).hom ≫
      (restrictFunctorComp k i).hom.app (moduleExteriorPower X₀ M n) =
    (moduleExteriorPowerFunctor X₂ n).map
        ((restrictFunctorComp k i).hom.app M) ≫
      (moduleExteriorPowerRestrictionIso k (M.restrict i) n).hom ≫
        (Modules.restrictFunctor k).map (moduleExteriorPowerRestrictionIso i M n).hom := by
  apply SheafOfModulesOfCommRing.exteriorPower_hom_ext X₂.sheaf (M.restrict (k ≫ i)) _ n
  intro U s
  let rcM := (restrictFunctorComp k i).hom.app M
  let rcE := (restrictFunctorComp k i).hom.app (moduleExteriorPower X₀ M n)
  let a := (moduleExteriorPowerRestrictionIso i M n).hom
  let b := (moduleExteriorPowerRestrictionIso k (M.restrict i) n).hom
  let a' := (Modules.restrictFunctor k).map a
  let s' := fun z => rcM.val.app U (s z)
  have hL := congrArg (fun z => rcE.val.app U z)
    (moduleExteriorPowerRestrictionIso_hom_mk (k ≫ i) M n U.unop s)
  have hR₀ := congrArg (fun z => a'.val.app U (b.val.app U z))
    (SheafOfModulesOfCommRing.exteriorPowerFunctor_map_mk X₂.sheaf rcM n U s)
  have hR₁ := congrArg (fun z => a'.val.app U z)
    (moduleExteriorPowerRestrictionIso_hom_mk k (M.restrict i) n U.unop s')
  have hR₂ := moduleExteriorPowerRestrictionIso_hom_mk i M n (k ''ᵁ U.unop) s'
  have hn := SheafOfModulesOfCommRing.exteriorPowerMk_naturality X₀.sheaf M n
    (eqToHom (show i ''ᵁ (k ''ᵁ U.unop) = (k ≫ i) ''ᵁ U.unop by simp)).op s
  exact hL.trans (hn.trans (hR₀.trans (hR₁.trans hR₂)).symm)
theorem relativeTopDifferentialRestrictionIso_comp_inv (n : ℕ) :
    (relativeTopDifferentialRestrictionIso p₀ (k ≫ i) p₂ (l ≫ j) H n).inv =
      (relativeTopDifferentialRestrictionIso p₁ k p₂ l h' n).inv ≫
        (Modules.restrictFunctor k).map
          (relativeTopDifferentialRestrictionIso p₀ i p₁ j h n).inv ≫
        (restrictFunctorComp k i).inv.app
          (moduleExteriorPower X₀ (relativeDifferentialSheaf p₀) n) := by
  let F := moduleExteriorPowerFunctor X₂ n
  let D := relativeDifferentialSheaf p₀
  let rD := (restrictFunctorComp k i).app D
  let rE := (restrictFunctorComp k i).app (moduleExteriorPower X₀ D n)
  have he : (moduleExteriorPowerRestrictionIso k (D.restrict i) n).hom ≫
      (Modules.restrictFunctor k).map (moduleExteriorPowerRestrictionIso i D n).hom ≫
        rE.inv = F.map rD.inv ≫ (moduleExteriorPowerRestrictionIso (k ≫ i) D n).hom := by
    apply (cancel_mono rE.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have hc := exteriorRestriction_comp i k D n
    change (moduleExteriorPowerRestrictionIso (k ≫ i) D n).hom ≫ rE.hom =
      F.map rD.hom ≫ (moduleExteriorPowerRestrictionIso k (D.restrict i) n).hom ≫
        (Modules.restrictFunctor k).map (moduleExteriorPowerRestrictionIso i D n).hom at hc
    rw [hc, ← Category.assoc, ← Functor.map_comp]
    rw [Iso.inv_hom_id]
    erw [F.map_id, Category.id_comp]
  dsimp only [relativeTopDifferentialRestrictionIso, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_inv, Iso.app_inv]
  rw [relativeDifferentialOpenSquareIso_comp_inv p₀ p₁ p₂ i j k l h h' H,
    Functor.map_comp, Functor.map_comp, Functor.map_comp]
  have hn := moduleExteriorPowerRestrictionIso_naturality k
    (relativeDifferentialOpenSquareIso p₀ i p₁ j h).inv n
  simp only [Category.assoc]
  rw [← Category.assoc (moduleExteriorPowerRestrictionIso k
    (relativeDifferentialSheaf p₁) n).hom, ← hn]
  simp only [Category.assoc]
  exact congrArg (fun t =>
    F.map (relativeDifferentialOpenSquareIso p₁ k p₂ l h').inv ≫
      F.map ((Modules.restrictFunctor k).map
        (relativeDifferentialOpenSquareIso p₀ i p₁ j h).inv) ≫ t) he.symm
open AlgebraicGeometry.Scheme.Modules.BaseChange.Affine.Square
private theorem conjugate_restrictComp {X₀ X₁ X₂ : Scheme.{u}}
    (i : X₁ ⟶ X₀) (k : X₂ ⟶ X₁) [IsOpenImmersion i] [IsOpenImmersion k] :
    conjugateEquiv ((restrictAdjunction i).comp (restrictAdjunction k)) (restrictAdjunction (k ≫ i))
      (restrictFunctorComp k i).hom =
        (Scheme.Modules.pushforwardComp k i).hom := by
  ext M U x
  simp only [conjugateEquiv_apply_app, Adjunction.comp_counit_app,
    Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    restrictFunctor_map_app, restrictAdjunction_unit_app_app,
    restrictAdjunction_counit_app_app,
    restrictFunctorComp_hom_app_app,
    Scheme.Modules.pushforwardComp_hom_app_app]
  simp only [Functor.comp_obj, Scheme.Modules.pushforward_obj_presheaf_map, ← Functor.map_comp]
  change (M.presheaf.map (𝟙 _) : _ ⟶ _) x = x
  rw [M.presheaf.map_id]; rfl
private theorem conjugate_openSquare
    {X₀ X₁ Y₀ Y₁ : Scheme.{u}}
    (p₀ : X₀ ⟶ Y₀) (p₁ : X₁ ⟶ Y₁) (i : X₁ ⟶ X₀) (j : Y₁ ⟶ Y₀)
    [IsOpenImmersion i] [IsOpenImmersion j] (h : i ≫ p₀ = p₁ ≫ j) :
    conjugateEquiv ((restrictAdjunction j).comp (Scheme.Modules.pullbackPushforwardAdjunction p₁))
      ((Scheme.Modules.pullbackPushforwardAdjunction p₀).comp (restrictAdjunction i))
      (Scheme.Modules.pullbackOpenSquare i p₁ p₀ j h).hom =
        (pushforwardSquareIso i p₁ p₀ j h).inv := by
  unfold Scheme.Modules.pullbackOpenSquare
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, ← Category.assoc]
  rw [← conjugateEquiv_comp _ ((Scheme.Modules.pullbackPushforwardAdjunction j).comp
      (Scheme.Modules.pullbackPushforwardAdjunction p₁)) _]
  rw [← conjugateEquiv_comp _ (Scheme.Modules.pullbackPushforwardAdjunction (p₁ ≫ j)) _]
  rw [← conjugateEquiv_comp _ (Scheme.Modules.pullbackPushforwardAdjunction (i ≫ p₀)) _]
  rw [← conjugateEquiv_comp _ ((Scheme.Modules.pullbackPushforwardAdjunction p₀).comp
      (Scheme.Modules.pullbackPushforwardAdjunction i)) _]
  rw [conjugateEquiv_whiskerRight, conjugateEquiv_whiskerLeft,
    conjugateEquiv_restrictFunctorIsoPullback_inv,
    conjugateEquiv_restrictFunctorIsoPullback_hom,
    Scheme.Modules.conjugateEquiv_pullbackComp_inv,
    conjugateEquiv_pullbackComp_hom, conjugateEquiv_pullbackCongr]
  ext M U x
  simp only [pushforwardSquareIso, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.id_app]
  simp only [CategoryTheory.Functor.map_id]
  erw [Category.id_comp, Category.comp_id]; rfl
private theorem conjugate_restrictComp_inv {X₀ X₁ X₂ : Scheme.{u}}
    (i : X₁ ⟶ X₀) (k : X₂ ⟶ X₁) [IsOpenImmersion i] [IsOpenImmersion k] :
    conjugateEquiv (restrictAdjunction (k ≫ i))
      ((restrictAdjunction i).comp (restrictAdjunction k))
      (restrictFunctorComp k i).inv =
        (Scheme.Modules.pushforwardComp k i).inv := by
  apply (cancel_mono (Scheme.Modules.pushforwardComp k i).hom).mp
  rw [← conjugate_restrictComp i k]
  rw [conjugateEquiv_comm _ _ (Iso.hom_inv_id (restrictFunctorComp k i)),
    conjugate_restrictComp i k]
  exact (Iso.inv_hom_id _).symm
private theorem pullbackOpenSquare_comp :
    (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (Scheme.Modules.pullback p₀)
        (restrictFunctorComp k i).inv ≫
      (Scheme.Modules.pullbackOpenSquare (k ≫ i) p₂ p₀ (l ≫ j) H).hom ≫
      Functor.whiskerRight (restrictFunctorComp l j).hom
        (Scheme.Modules.pullback p₂) ≫ (Functor.associator _ _ _).hom =
    Functor.whiskerRight (Scheme.Modules.pullbackOpenSquare i p₁ p₀ j h).hom
        (Modules.restrictFunctor k) ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (Modules.restrictFunctor j)
        (Scheme.Modules.pullbackOpenSquare k p₂ p₁ l h').hom := by
  let P := Scheme.Modules.pullbackPushforwardAdjunction p₀
  let Q := Scheme.Modules.pullbackPushforwardAdjunction p₁
  let S := Scheme.Modules.pullbackPushforwardAdjunction p₂
  let I := restrictAdjunction i
  let J := restrictAdjunction j
  let K := restrictAdjunction k
  let L := restrictAdjunction l
  let KI := restrictAdjunction (k ≫ i)
  let LJ := restrictAdjunction (l ≫ j)
  apply (conjugateEquiv (J.comp (L.comp S)) ((P.comp I).comp K)).injective
  simp only [← Category.assoc]
  rw [← conjugateEquiv_comp _ ((J.comp L).comp S) _]
  rw [← conjugateEquiv_comp _ (LJ.comp S) _]
  rw [← conjugateEquiv_comp _ (P.comp KI) _]
  rw [← conjugateEquiv_comp _ (P.comp (I.comp K)) _]
  rw [← conjugateEquiv_comp _ (J.comp (Q.comp K)) _]
  rw [← conjugateEquiv_comp _ ((J.comp Q).comp K) _]
  rw [conjugateEquiv_associator_hom, conjugateEquiv_whiskerRight,
    conjugateEquiv_whiskerLeft, conjugateEquiv_associator_hom,
    conjugateEquiv_whiskerLeft, conjugateEquiv_associator_hom,
    conjugateEquiv_whiskerRight]
  rw [conjugate_restrictComp j l, conjugate_restrictComp_inv i k,
    conjugate_openSquare p₀ p₂ (k ≫ i) (l ≫ j) H,
    conjugate_openSquare p₁ p₂ k l h', conjugate_openSquare p₀ p₁ i j h]
  ext M U x
  simp only [pushforwardSquareIso, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Category.id_comp, Category.comp_id,
    Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    Scheme.Modules.pushforwardComp_hom_app_app, Scheme.Modules.pushforwardComp_inv_app_app,
    Scheme.Modules.pushforwardCongr_inv_app_app, Functor.comp_obj,
    Scheme.Modules.pushforward_obj_presheaf_map, ← Functor.map_comp]
  congr 2
private theorem pullbackOpenSquare_comp_inv (N : Y₀.Modules) :
    (Scheme.Modules.pullback p₂).map ((restrictFunctorComp l j).inv.app N) ≫
        (Scheme.Modules.pullbackOpenSquare (k ≫ i) p₂ p₀ (l ≫ j) H).inv.app N =
      (Scheme.Modules.pullbackOpenSquare k p₂ p₁ l h').inv.app (N.restrict j) ≫
        (Modules.restrictFunctor k).map
          ((Scheme.Modules.pullbackOpenSquare i p₁ p₀ j h).inv.app N) ≫
        (restrictFunctorComp k i).inv.app
          ((Scheme.Modules.pullback p₀).obj N) := by
  let r := (restrictFunctorComp k i).app
    ((Scheme.Modules.pullback p₀).obj N)
  let c := (Scheme.Modules.pullbackOpenSquare (k ≫ i) p₂ p₀ (l ≫ j) H).app N
  let t := (Scheme.Modules.pullback p₂).mapIso
    ((restrictFunctorComp l j).app N)
  let b := (Modules.restrictFunctor k).mapIso
    ((Scheme.Modules.pullbackOpenSquare i p₁ p₀ j h).app N)
  let d := (Scheme.Modules.pullbackOpenSquare k p₂ p₁ l h').app (N.restrict j)
  have he : c ≪≫ t = r ≪≫ b ≪≫ d := by
    apply Iso.ext
    apply (cancel_epi r.inv).mp
    simp only [Iso.trans_hom, Iso.inv_hom_id_assoc]
    have hc := congrArg (fun η => η.app N)
      (pullbackOpenSquare_comp p₀ p₁ p₂ i j k l h h' H)
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Category.id_comp, Category.comp_id] at hc
    change r.inv ≫ c.hom ≫ t.hom = b.hom ≫ d.hom at hc
    exact hc
  exact congrArg Iso.inv he
private theorem relativeCoefficientsRestriction_inv_section
    {W X Z Y : Scheme.{u}} (p : X ⟶ Y) (i : W ⟶ X) (q : W ⟶ Z) (j : Z ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion j] (h : i ≫ p = q ≫ j)
    (n : ℕ) (N : Y.Modules) (U : W.Opens)
    (s : Γ(moduleExteriorPower W (relativeDifferentialSheaf q) n, U))
    (t : Γ((Scheme.Modules.pullback q).obj (N.restrict j), U)) :
    ((relativeTopDifferentialCoefficientsRestrictionIso p i q j h n).inv.app N).app U
      (moduleTensorSection W (moduleExteriorPower W (relativeDifferentialSheaf q) n)
        ((Scheme.Modules.pullback q).obj (N.restrict j)) U s t) =
      moduleTensorSection X (moduleExteriorPower X (relativeDifferentialSheaf p) n)
        ((Scheme.Modules.pullback p).obj N) (i ''ᵁ U)
        ((relativeTopDifferentialRestrictionIso p i q j h n).inv.app U s)
        (((Scheme.Modules.pullbackOpenSquare i q p j h).inv.app N).app U t) := by
  change (tensorRestrictionIso i _ _).hom.app U
    (((moduleTensorLeftFunctor W _).map
      ((Scheme.Modules.pullbackOpenSquare i q p j h).inv.app N)).app U
        (((moduleTensorCoefficientMap W
          (relativeTopDifferentialRestrictionIso p i q j h n).inv).app _).app U
            (moduleTensorSection W _ _ U s t))) = _
  rw [moduleTensorCoefficientMap_section, moduleTensorLeftFunctor_map_section]
  exact tensorRestrictionIso_section i
    (moduleExteriorPower X (relativeDifferentialSheaf p) n) ((Scheme.Modules.pullback p).obj N) U
      ((relativeTopDifferentialRestrictionIso p i q j h n).inv.app U s)
      (((Scheme.Modules.pullbackOpenSquare i q p j h).inv.app N).app U t)
set_option maxRecDepth 2000 in set_option maxHeartbeats 400000 in
-- The native composed sheaf maps exceeded the default conversion budget in the full leaf.
private theorem relativeCoefficientsRestriction_comp_inv (n : ℕ) (N : Y₀.Modules) :
    (relativeTopDifferentialCoefficientsFunctor p₂ n).map
        ((restrictFunctorComp l j).inv.app N) ≫
      (relativeTopDifferentialCoefficientsRestrictionIso p₀ (k ≫ i) p₂ (l ≫ j) H n).inv.app N =
    (relativeTopDifferentialCoefficientsRestrictionIso p₁ k p₂ l h' n).inv.app (N.restrict j) ≫
      (Modules.restrictFunctor k).map
        ((relativeTopDifferentialCoefficientsRestrictionIso p₀ i p₁ j h n).inv.app N) ≫
      (restrictFunctorComp k i).inv.app
        ((relativeTopDifferentialCoefficientsFunctor p₀ n).obj N) := by
  let E₀ := moduleExteriorPower X₀ (relativeDifferentialSheaf p₀) n
  let E₂ := moduleExteriorPower X₂ (relativeDifferentialSheaf p₂) n
  let Q₀ := (Scheme.Modules.pullback p₀).obj N
  let rE := (restrictFunctorComp k i).inv.app E₀
  let rQ := (restrictFunctorComp k i).inv.app Q₀
  let rT := (restrictFunctorComp k i).inv.app
    ((relativeTopDifferentialCoefficientsFunctor p₀ n).obj N)
  let a₁ := (relativeTopDifferentialRestrictionIso p₀ i p₁ j h n).inv
  let a₂ := (relativeTopDifferentialRestrictionIso p₁ k p₂ l h' n).inv
  let b₁ := (Scheme.Modules.pullbackOpenSquare i p₁ p₀ j h).inv.app N
  let b₂ := (Scheme.Modules.pullbackOpenSquare k p₂ p₁ l h').inv.app (N.restrict j)
  apply moduleTensor_hom_ext
  intro U s t
  let t' := ((Scheme.Modules.pullback p₂).map ((restrictFunctorComp l j).inv.app N)).app U t
  have hL := congrArg (fun z =>
    ((relativeTopDifferentialCoefficientsRestrictionIso p₀ (k ≫ i) p₂ (l ≫ j) H n).inv.app N).app
      U z)
      (moduleTensorLeftFunctor_map_section E₂ ((Scheme.Modules.pullback p₂).map
          ((restrictFunctorComp l j).inv.app N)) U s t)
  have hC := relativeCoefficientsRestriction_inv_section p₀ (k ≫ i) p₂ (l ≫ j) H n N U s t'
  have hR₂ := congrArg (fun z => rT.app U (((Modules.restrictFunctor k).map
      ((relativeTopDifferentialCoefficientsRestrictionIso p₀ i p₁ j h n).inv.app N)).app U z))
        (relativeCoefficientsRestriction_inv_section p₁ k p₂ l h' n (N.restrict j) U s t)
  have hR₁ := congrArg (fun z => rT.app U z)
    (relativeCoefficientsRestriction_inv_section p₀ i p₁ j h n N (k ''ᵁ U)
      (a₂.app U s) (b₂.app U t))
  have hR : rT.app U (moduleTensorSection X₀ E₀ Q₀ (i ''ᵁ (k ''ᵁ U))
      (a₁.app (k ''ᵁ U) (a₂.app U s)) (b₁.app (k ''ᵁ U) (b₂.app U t))) =
    moduleTensorSection X₀ E₀ Q₀ ((k ≫ i) ''ᵁ U)
      (rE.app U (a₁.app (k ''ᵁ U) (a₂.app U s)))
      (rQ.app U (b₁.app (k ''ᵁ U) (b₂.app U t))) :=
    moduleTensorSection_restrict E₀ Q₀
      (eqToHom (show (k ≫ i) ''ᵁ U = i ''ᵁ (k ''ᵁ U) by simp)) _ _
  have hE := congrArg (fun z => Scheme.Modules.Hom.app z U s)
    (relativeTopDifferentialRestrictionIso_comp_inv p₀ p₁ p₂ i j k l h h' H n)
  have hQ := congrArg (fun z => Scheme.Modules.Hom.app z U t)
    (pullbackOpenSquare_comp_inv p₀ p₁ p₂ i j k l h h' H N)
  exact hL.trans (hC.trans ((congrArg₂ (moduleTensorSection X₀ E₀ Q₀ ((k ≫ i) ''ᵁ U)) hE hQ).trans
      (hR₂.trans (hR₁.trans hR)).symm))
private theorem relativeCoefficientsRestriction_comp (n : ℕ) (N : Y₀.Modules) :
    (restrictFunctorComp k i).inv.app
        ((relativeTopDifferentialCoefficientsFunctor p₀ n).obj N) ≫
      (relativeTopDifferentialCoefficientsRestrictionIso p₀ (k ≫ i) p₂ (l ≫ j) H n).hom.app N ≫
      (relativeTopDifferentialCoefficientsFunctor p₂ n).map
        ((restrictFunctorComp l j).hom.app N) =
    (Modules.restrictFunctor k).map
        ((relativeTopDifferentialCoefficientsRestrictionIso p₀ i p₁ j h n).hom.app N) ≫
      (relativeTopDifferentialCoefficientsRestrictionIso p₁ k p₂ l h' n).hom.app
        (N.restrict j) := by
  let r := (restrictFunctorComp k i).app
    ((relativeTopDifferentialCoefficientsFunctor p₀ n).obj N)
  let c := (relativeTopDifferentialCoefficientsRestrictionIso p₀ (k ≫ i) p₂ (l ≫ j) H n).app N
  let t := (relativeTopDifferentialCoefficientsFunctor p₂ n).mapIso
    ((restrictFunctorComp l j).app N)
  let b := (Modules.restrictFunctor k).mapIso
    ((relativeTopDifferentialCoefficientsRestrictionIso p₀ i p₁ j h n).app N)
  let d := (relativeTopDifferentialCoefficientsRestrictionIso p₁ k p₂ l h' n).app (N.restrict j)
  have he : c ≪≫ t = r ≪≫ b ≪≫ d :=
    Iso.ext_inv (relativeCoefficientsRestriction_comp_inv p₀ p₁ p₂ i j k l h h' H n N)
  have hh := congrArg Iso.hom he
  have ht := congrArg (fun z => r.inv ≫ z) hh
  simp only [Iso.trans_hom, Iso.inv_hom_id_assoc] at ht
  exact ht
end RestrictionPasting
/-- The relative top differential coefficient functor followed by the `n`th higher direct image. -/
abbrev relativeHigherFunctor {X Y : Scheme.{u}} (p : X ⟶ Y) (n : ℕ) :=
  relativeTopDifferentialCoefficientsFunctor p n ⋙ (Scheme.Modules.pushforward p).rightDerived n
/-- Open restriction for the coefficient-valued higher direct image along the given pullback
square. -/
def relativeHigherRestrictionIso
    {W X Z Y : Scheme.{u}} (p : X ⟶ Y) (i : W ⟶ X) (q : W ⟶ Z) (j : Z ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion j] (h : IsPullback i q p j) (n : ℕ) :
    relativeHigherFunctor p n ⋙ Modules.restrictFunctor j ≅
      Modules.restrictFunctor j ⋙ relativeHigherFunctor q n :=
  Functor.isoWhiskerLeft (relativeTopDifferentialCoefficientsFunctor p n)
      (Scheme.Modules.higherDirectImageOpenRestrictionIso i q p j h n) ≪≫
    Functor.isoWhiskerRight
      (relativeTopDifferentialCoefficientsRestrictionIso p i q j h.w n)
      ((Scheme.Modules.pushforward q).rightDerived n)
-- Fix the original component's module-arrow type before composing native components.
/-- The component at `N` of `relativeHigherRestrictionIso`. -/
def relativeHigherRestrictionHom
    {W X Z Y : Scheme.{u}} (p : X ⟶ Y) (i : W ⟶ X) (q : W ⟶ Z) (j : Z ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion j] (h : IsPullback i q p j) (n : ℕ) (N : Y.Modules) :
    ((relativeHigherFunctor p n).obj N).restrict j ⟶
      (relativeHigherFunctor q n).obj (N.restrict j) :=
  (relativeHigherRestrictionIso p i q j h n).hom.app N
theorem relativeHigherRestrictionIso_hom
    {W X Z Y : Scheme.{u}} (p : X ⟶ Y) (i : W ⟶ X) (q : W ⟶ Z) (j : Z ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion j] (h : IsPullback i q p j) (n : ℕ) (N : Y.Modules) :
    (relativeHigherRestrictionIso p i q j h n).hom.app N =
      (Scheme.Modules.higherDirectImageOpenRestrictionIso i q p j h n).hom.app
        ((relativeTopDifferentialCoefficientsFunctor p n).obj N) ≫
      ((Scheme.Modules.pushforward q).rightDerived n).map
        ((relativeTopDifferentialCoefficientsRestrictionIso p i q j h.w n).hom.app N) := rfl
theorem relativeHigherRestrictionIso_comp
    {X₀ X₁ X₂ Y₀ Y₁ Y₂ : Scheme.{u}}
    (p₀ : X₀ ⟶ Y₀) (p₁ : X₁ ⟶ Y₁) (p₂ : X₂ ⟶ Y₂)
    (i : X₁ ⟶ X₀) (j : Y₁ ⟶ Y₀) (k : X₂ ⟶ X₁) (l : Y₂ ⟶ Y₁)
    [IsOpenImmersion i] [IsOpenImmersion j]
    [IsOpenImmersion k] [IsOpenImmersion l]
    (h : IsPullback i p₁ p₀ j) (h' : IsPullback k p₂ p₁ l)
    (H : IsPullback (k ≫ i) p₂ p₀ (l ≫ j)) (n : ℕ) (N : Y₀.Modules) :
    (restrictFunctorComp l j).inv.app ((relativeHigherFunctor p₀ n).obj N) ≫
      (relativeHigherRestrictionIso p₀ (k ≫ i) p₂ (l ≫ j) H n).hom.app N ≫
      (relativeHigherFunctor p₂ n).map ((restrictFunctorComp l j).hom.app N) =
    (Modules.restrictFunctor l).map
        ((relativeHigherRestrictionIso p₀ i p₁ j h n).hom.app N) ≫
      (relativeHigherRestrictionIso p₁ k p₂ l h' n).hom.app (N.restrict j) := by
  let M := (relativeTopDifferentialCoefficientsFunctor p₀ n).obj N
  let A := (relativeTopDifferentialCoefficientsRestrictionIso p₀ i p₁ j h.w n).hom.app N
  let B := (relativeTopDifferentialCoefficientsRestrictionIso p₁ k p₂ l h'.w n).hom.app
    (N.restrict j)
  let C := (relativeTopDifferentialCoefficientsRestrictionIso p₀ (k ≫ i) p₂ (l ≫ j) H.w n).hom.app N
  let F := (Scheme.Modules.pushforward p₂).rightDerived n
  have hc : C ≫ (relativeTopDifferentialCoefficientsFunctor p₂ n).map
      ((restrictFunctorComp l j).hom.app N) =
    (restrictFunctorComp k i).hom.app M ≫
      (Modules.restrictFunctor k).map A ≫ B := by
    let r := (restrictFunctorComp k i).app M
    have hh := relativeCoefficientsRestriction_comp p₀ p₁ p₂ i j k l h.w h'.w H.w n N
    change r.inv ≫ C ≫ (relativeTopDifferentialCoefficientsFunctor p₂ n).map
      ((restrictFunctorComp l j).hom.app N) =
        (Modules.restrictFunctor k).map A ≫ B at hh
    have ht := congrArg (fun z => r.hom ≫ z) hh
    simp only [Iso.hom_inv_id_assoc] at ht
    exact ht
  have hn := (Scheme.Modules.higherDirectImageOpenRestrictionIso k p₂ p₁ l h' n).hom.naturality A
  let D := (relativeTopDifferentialCoefficientsFunctor p₂ n).map
    ((restrictFunctorComp l j).hom.app N)
  change (restrictFunctorComp l j).inv.app _ ≫
      ((Scheme.Modules.higherDirectImageOpenRestrictionIso (k ≫ i) p₂ p₀ (l ≫ j) H n).hom.app M ≫
        F.map C) ≫ F.map D =
    (Modules.restrictFunctor l).map
      ((Scheme.Modules.higherDirectImageOpenRestrictionIso i p₁ p₀ j h n).hom.app M ≫
        ((Scheme.Modules.pushforward p₁).rightDerived n).map A) ≫
      (Scheme.Modules.higherDirectImageOpenRestrictionIso k p₂ p₁ l h' n).hom.app _ ≫ F.map B
  simp only [Functor.map_comp, Category.assoc]
  rw [← F.map_comp C D, hc, F.map_comp, F.map_comp]
  rw [Scheme.Modules.higherDirectImageOpenRestrictionIso_comp_assoc i p₁ p₀ j k p₂ l h h' H M n]
  rw [← reassoc_of% hn]; rfl
@[reassoc]
theorem restrictCompLeftUnit_hom {U V : Scheme.{u}} (j : U ⟶ V)
    [IsOpenImmersion j] (M : V.Modules) :
    (restrictFunctorComp (𝟙 U) j).inv.app M ≫
      (restrictFunctorCongr (Category.id_comp j)).hom.app M =
        restrictFunctorId.hom.app (M.restrict j) := by
  ext W x
  simp only [Scheme.Modules.Hom.comp_app, restrictFunctorComp_inv_app_app,
    restrictFunctorCongr_hom_app_app,
    restrictFunctorId_hom_app_app]
  change (M.presheaf.map _ ≫ M.presheaf.map _) x = M.presheaf.map _ x
  rw [← Functor.map_comp]
  congr 2
theorem restrictCompLeftUnit_inv {U V : Scheme.{u}} (j : U ⟶ V)
    [IsOpenImmersion j] (M : V.Modules) :
    (restrictFunctorCongr (Category.id_comp j)).inv.app M ≫
      (restrictFunctorComp (𝟙 U) j).hom.app M =
        restrictFunctorId.inv.app (M.restrict j) := by
  have he : ((restrictFunctorComp (𝟙 U) j).app M).symm ≪≫
      (restrictFunctorCongr (Category.id_comp j)).app M =
        restrictFunctorId.app (M.restrict j) :=
    Iso.ext (restrictCompLeftUnit_hom j M)
  exact congrArg Iso.inv he
@[reassoc]
theorem restrictCompRightUnit_hom {U V : Scheme.{u}} (j : U ⟶ V)
    [IsOpenImmersion j] (M : V.Modules) :
    (restrictFunctorComp j (𝟙 V)).inv.app M ≫
      (restrictFunctorCongr (Category.comp_id j)).hom.app M =
        (Modules.restrictFunctor j).map (restrictFunctorId.hom.app M) := by
  ext W x
  change Γ(M, (𝟙 V) ''ᵁ (j ''ᵁ W)) at x
  simp only [Scheme.Modules.Hom.comp_app, restrictFunctorComp_inv_app_app,
    restrictFunctorCongr_hom_app_app, restrictFunctor_map_app,
    restrictFunctorId_hom_app_app]
  change (M.presheaf.map _ ≫ M.presheaf.map _) x = M.presheaf.map _ x
  rw [← Functor.map_comp]
  congr 2
theorem restrictCompRightUnit_inv {U V : Scheme.{u}} (j : U ⟶ V)
    [IsOpenImmersion j] (M : V.Modules) :
    (restrictFunctorCongr (Category.comp_id j)).inv.app M ≫
      (restrictFunctorComp j (𝟙 V)).hom.app M =
        (Modules.restrictFunctor j).map (restrictFunctorId.inv.app M) := by
  have he : ((restrictFunctorComp j (𝟙 V)).app M).symm ≪≫
      (restrictFunctorCongr (Category.comp_id j)).app M =
        (Modules.restrictFunctor j).mapIso (restrictFunctorId.app M) :=
    Iso.ext (restrictCompRightUnit_hom j M)
  exact congrArg Iso.inv he
theorem relativeHigherRestrictionIso_congr
    {W X Z Y : Scheme.{u}} (p : X ⟶ Y) (q : W ⟶ Z)
    (i i' : W ⟶ X) (j j' : Z ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion i'] [IsOpenImmersion j] [IsOpenImmersion j']
    (H : IsPullback i q p j) (H' : IsPullback i' q p j')
    (wi : i = i') (wj : j = j') (n : ℕ) (N : Y.Modules) :
    (relativeHigherRestrictionIso p i q j H n).hom.app N =
      (restrictFunctorCongr wj).hom.app ((relativeHigherFunctor p n).obj N) ≫
      (relativeHigherRestrictionIso p i' q j' H' n).hom.app N ≫
      (relativeHigherFunctor q n).map ((restrictFunctorCongr wj).inv.app N) := by
  subst i'; subst j'
  have hid (M : Y.Modules) : (restrictFunctorCongr (rfl : j = j)).app M =
      Iso.refl (M.restrict j) := by
    apply Iso.ext
    ext U x
    change M.presheaf.map (𝟙 _) x = x
    rw [M.presheaf.map_id]; rfl
  have hh (M : Y.Modules) : (restrictFunctorCongr (rfl : j = j)).hom.app M =
      𝟙 _ := congrArg Iso.hom (hid M)
  have hi (M : Y.Modules) : (restrictFunctorCongr (rfl : j = j)).inv.app M =
      𝟙 _ := congrArg Iso.inv (hid M)
  rw [hh, hi]
  erw [(relativeHigherFunctor q n).map_id, Category.id_comp, Category.comp_id]
end AlgebraicGeometry.Scheme.Cohomology.RelativeProjectiveTrace
