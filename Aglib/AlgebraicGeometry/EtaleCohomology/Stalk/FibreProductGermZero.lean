/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.FibreProductCohomology
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.OriginalCohomologyZero
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ChartHomSections

/-! # Degree-zero normalization of original fibre-product cohomology germs

The original degree-zero equivalence and actual chart evaluation send the germ
to the ordinary direct-image germ followed by the native degree-zero derived
unit. This fixes the original map, not just its isomorphism class.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe u w s e

namespace CategoryTheory.Sheaf.ModuleCoefficients

private theorem derived_postcomp_zero_unit
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Abelian C] [EnoughInjectives C] [Abelian D] [Abelian E]
    (P : C ⥤ D) (L : D ⥤ E) (Q : C ⥤ E)
    [P.Additive] [L.Additive] [L.PreservesHomology] [Q.Additive]
    (α : P ⋙ L ≅ Q) (M : C) :
    L.map (P.toRightDerivedZero.app M) ≫
        ((rightDerivedPostcompIso P L 0).symm ≪≫ rightDerivedNatIso α 0).hom.app M =
      α.hom.app M ≫ Q.toRightDerivedZero.app M := by
  let d := (rightDerivedPostcompIso P L 0).app M
  have hp : (P ⋙ L).toRightDerivedZero.app M ≫ d.hom =
      L.map (P.toRightDerivedZero.app M) := toRightDerivedZero_postcomp P L M
  change L.map (P.toRightDerivedZero.app M) ≫
    d.inv ≫ (NatTrans.rightDerived α.hom 0).app M = _
  have hc : ((P ⋙ L).toRightDerivedZero.app M ≫ d.hom) ≫
      d.inv ≫ (NatTrans.rightDerived α.hom 0).app M =
      (P ⋙ L).toRightDerivedZero.app M ≫ (NatTrans.rightDerived α.hom 0).app M :=
    (Category.assoc _ _ _).trans
      (congrArg (fun k => (P ⋙ L).toRightDerivedZero.app M ≫ k)
        (d.hom_inv_id_assoc ((NatTrans.rightDerived α.hom 0).app M)))
  exact (congrArg (fun k => k ≫ d.inv ≫ (NatTrans.rightDerived α.hom 0).app M)
    hp.symm).trans (hc.trans (toRightDerivedZero_naturality α.hom M))

private theorem adjunction_unit_paste
    {C D : Type*} [Category* C] [Category* D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    {A B : C} {Y Z : D} (g : A ⟶ B) (h : L.obj B ⟶ Z)
    (a : L.obj A ⟶ Y) (b : Y ⟶ Z) (hab : L.map g ≫ h = a ≫ b) :
    g ≫ adj.unit.app B ≫ R.map h =
      adj.unit.app A ≫ R.map a ≫ R.map b := by
  rw [← Category.assoc, ← adj.unit_naturality, Category.assoc,
    ← R.map_comp, hab, R.map_comp]

private theorem source_ext_map_mk₀
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasExt.{w} C] [HasExt.{e} D]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    {P F : C} {Q : D} (b : Q ⟶ L.obj P) (a : P ⟶ F) :
    (Ext.mk₀ b).comp ((Ext.mk₀ a).mapExactFunctor L) (Nat.zero_add 0) =
      Ext.mk₀ (b ≫ L.map a) := by
  rw [Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]

end CategoryTheory.Sheaf.ModuleCoefficients

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The original sheafification comparison cancels the original sheafification unit. -/
theorem directImagePresheafSheafificationIso_unit
    (F : AbelianSheaf.{u, u + 1} X) :
    toSheafify (Scheme.smallEtaleTopology S) ((directImage f).obj F).obj ≫
        ((directImagePresheafSheafificationIso f).hom.app F).hom = 𝟙 _ := by
  change toSheafify (Scheme.smallEtaleTopology S) ((directImage f).obj F).obj ≫
    (isoSheafify (Scheme.smallEtaleTopology S) ((directImage f).obj F).property).inv = _
  rw [← isoSheafify_hom]
  exact Iso.hom_inv_id _

/-- Exact sheafification preserves the native original degree-zero derived unit. -/
theorem resolutionCohomologySheafificationIso_zero_unit
    (F : AbelianSheaf.{u, u + 1} X) :
    (presheafToSheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1}).map
        ((directImagePresheaf f).toRightDerivedZero.app F) ≫
        (resolutionCohomologySheafificationIso f 0).hom.app F =
      (directImagePresheafSheafificationIso f).hom.app F ≫
        (directImage f).toRightDerivedZero.app F :=
  Sheaf.ModuleCoefficients.derived_postcomp_zero_unit
    (directImagePresheaf f)
    (presheafToSheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1})
    (directImage f) (directImagePresheafSheafificationIso f) F

/-- The map from resolution degree zero is the original direct-image derived unit. -/
theorem resolutionCohomologyToHigherDirectImage_zero_unit
    (F : AbelianSheaf.{u, u + 1} X) :
    (directImagePresheaf f).toRightDerivedZero.app F ≫
        (resolutionCohomologyToHigherDirectImage f 0).app F =
      ((directImage f).toRightDerivedZero.app F).hom := by
  have h := Sheaf.ModuleCoefficients.adjunction_unit_paste
    (sheafificationAdjunction (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1})
    ((directImagePresheaf f).toRightDerivedZero.app F)
    ((resolutionCohomologySheafificationIso f 0).hom.app F)
    ((directImagePresheafSheafificationIso f).hom.app F)
    ((directImage f).toRightDerivedZero.app F)
    (resolutionCohomologySheafificationIso_zero_unit f F)
  change _ = toSheafify (Scheme.smallEtaleTopology S) ((directImage f).obj F).obj ≫
    ((directImagePresheafSheafificationIso f).hom.app F).hom ≫
    ((directImage f).toRightDerivedZero.app F).hom at h
  exact h.trans (by
    rw [← Category.assoc, directImagePresheafSheafificationIso_unit, Category.id_comp])

variable [hFibreProductGermZeroBaseExt : HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- A represented degree-zero class has the literal original derived-unit germ. -/
theorem originalCohomologyGerm_mk₀ (U : S.Etale)
    (F : AbelianSheaf.{u, u + 1} X)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (η : Spec (.of Ω) ⟶ S)
    (p : (pointSmallEtale η).fiber.obj U)
    (a : Sheaf.Hypercohomology.freeAbelianSheaf.{u + 1}
      (Scheme.smallEtaleTopology X) ((siteBaseChange f).obj U) ⟶ F) :
    originalCohomologyGerm f F 0 η U p (Ext.mk₀ a) =
      (pointSmallEtale η).toPresheafFiber U p ((higherDirectImage f 0).obj F).obj
        ((((directImage f).toRightDerivedZero.app F).hom.app (op U))
          (Sheaf.Hypercohomology.sectionsAddEquiv
            (Scheme.smallEtaleTopology X) ((siteBaseChange f).obj U) F a)) := by
  change (pointSmallEtale η).toPresheafFiber U p ((higherDirectImage f 0).obj F).obj
    ((((resolutionCohomologyToHigherDirectImage f 0).app F).app (op U))
      (originalCohomologyResolutionEquiv f U F 0 (Ext.mk₀ a))) = _
  rw [originalCohomologyResolutionEquiv_mk₀]
  exact congrArg
    ((pointSmallEtale η).toPresheafFiber U p ((higherDirectImage f 0).obj F).obj)
    (ConcreteCategory.congr_hom
      (NatTrans.congr_app (resolutionCohomologyToHigherDirectImage_zero_unit f F) (op U))
      (Sheaf.Hypercohomology.sectionsAddEquiv
        (Scheme.smallEtaleTopology X) ((siteBaseChange f).obj U) F a))

section Chart

variable (V : X.Etale)
  [HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over V) AddCommGrpCat.{u + 1})]
  [hGermZeroChartExt : HasExt.{e} (AbelianSheaf.{u, u + 1} V.left)]

local instance fibreProductGermZeroConstantBaseExt : HasExt.{w}
    (AbelianSheaf.{u, u + 1} ((Functor.fromPUnit X).obj V.right)) :=
  hFibreProductGermZeroBaseExt

local instance fibreProductGermZeroIdentityChartExt : HasExt.{e}
    (Sheaf ((𝟭 Scheme.{u}).obj V.left).smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  hGermZeroChartExt

/-- The original chart equivalence in degree zero retains the actual chart section. -/
theorem originalCohomologyChartEquiv_equiv₀
    (F : AbelianSheaf.{u, u + 1} X)
    (x : Sheaf.LargeCohomology.H.{w, u + 1, u, u + 1}
      (Scheme.smallEtaleTopology X) F 0 V) :
    (Continuity.pullbackSectionsEtaleEvaluationIso F V).hom
        (Sheaf.H.equiv₀ ((inverseImage V.hom).obj F) (etaleTerminalIsTerminal V.left)
          (originalCohomologyChartEquiv V F 0 x)) =
      Sheaf.Hypercohomology.sectionsAddEquiv (Scheme.smallEtaleTopology X) V F
        (Ext.addEquiv₀ x) := by
  obtain ⟨a, rfl⟩ := (Ext.mk₀_bijective _ _).surjective x
  have hchart := (originalCohomologyChartEquiv_apply V F 0 (Ext.mk₀ a)).trans
    (Sheaf.ModuleCoefficients.source_ext_map_mk₀
      (inverseImage V.hom) (chartComparisonSource V) a)
  have heval := congrArg (fun z =>
    (Continuity.pullbackSectionsEtaleEvaluationIso F V).hom
      (Sheaf.H.equiv₀ ((inverseImage V.hom).obj F)
        (etaleTerminalIsTerminal V.left) z)) hchart
  have hHom := congrArg (chartHomSectionsEquiv V F)
    (Ext.addEquiv₀.apply_symm_apply
      (chartComparisonSource V ≫ (inverseImage V.hom).map a))
  have hcoefficient := chartHomSectionsEquiv_naturality V a (chartComparisonSource V)
  have hsource := congrArg (a.hom.app (op V)) (chartHomSectionsEquiv_source V)
  have hrepresented := (Sheaf.Hypercohomology.sectionsEquiv_naturality
    (Scheme.smallEtaleTopology X) V (𝟙 _) a).symm.trans
      (congrArg (Sheaf.Hypercohomology.sectionsAddEquiv
        (Scheme.smallEtaleTopology X) V F) (Category.id_comp a))
  have hzero := congrArg
    (Sheaf.Hypercohomology.sectionsAddEquiv (Scheme.smallEtaleTopology X) V F)
    (Ext.addEquiv₀.apply_symm_apply a)
  exact heval.trans
    (hHom.trans (hcoefficient.trans (hsource.trans (hrepresented.trans hzero.symm))))

end Chart

variable (U : S.Etale)
  [HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange f).obj U)) AddCommGrpCat.{u + 1})]
  [hFibreProductGermZeroExt : HasExt.{e}
    (AbelianSheaf.{u, u + 1} (pullback U.hom f))]

local instance fibreProductGermZeroChartExt : HasExt.{e}
    (AbelianSheaf.{u, u + 1} ((siteBaseChange f).obj U).left) :=
  hFibreProductGermZeroExt

/-- The original fibre-product germ in degree zero is ordinary evaluation followed
by the actual degree-zero derived unit on the native direct-image stalk. -/
theorem fibreProductCohomologyGerm_equiv₀
    (F : AbelianSheaf.{u, u + 1} X)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (η : Spec (.of Ω) ⟶ S)
    (p : (pointSmallEtale η).fiber.obj U)
    (x : Sheaf.H.{e} ((inverseImage (pullback.snd U.hom f)).obj F) 0) :
    fibreProductCohomologyGerm f U F 0 η p x =
      ((pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})).map
        ((directImage f).toRightDerivedZero.app F)
        ((pointSmallEtale η).toPresheafFiber U p ((directImage f).obj F).obj
          ((Continuity.pullbackSectionsEtaleEvaluationIso F ((siteBaseChange f).obj U)).hom
            (Sheaf.H.equiv₀ ((inverseImage (pullback.snd U.hom f)).obj F)
              (etaleTerminalIsTerminal (pullback U.hom f)) x))) := by
  obtain ⟨y, rfl⟩ := (fibreProductCohomologyEquiv f U F 0).surjective x
  obtain ⟨a, rfl⟩ := (Ext.mk₀_bijective _ _).surjective y
  have hchart := originalCohomologyChartEquiv_equiv₀ ((siteBaseChange f).obj U) F
    (Ext.mk₀ a)
  have h₀ : Ext.addEquiv₀ (Ext.mk₀ a) = a := Ext.addEquiv₀.apply_symm_apply a
  rw [h₀] at hchart
  have hsource : fibreProductCohomologyGerm f U F 0 η p
      (fibreProductCohomologyEquiv f U F 0 (Ext.mk₀ a)) =
      originalCohomologyGerm f F 0 η U p (Ext.mk₀ a) :=
    congrArg (originalCohomologyGerm f F 0 η U p)
      ((fibreProductCohomologyEquiv f U F 0).symm_apply_apply (Ext.mk₀ a))
  have hgerm := ConcreteCategory.congr_hom
    ((pointSmallEtale η).toPresheafFiber_naturality
      (((directImage f).toRightDerivedZero.app F).hom) U p)
    (Sheaf.Hypercohomology.sectionsAddEquiv
      (Scheme.smallEtaleTopology X) ((siteBaseChange f).obj U) F a)
  exact hsource.trans ((originalCohomologyGerm_mk₀ f U F η p a).trans
    (hgerm.symm.trans (congrArg
    (fun z => ((pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})).map
      ((directImage f).toRightDerivedZero.app F)
      ((pointSmallEtale η).toPresheafFiber U p ((directImage f).obj F).obj z))
    hchart.symm)))

/-- Section form of the original degree-zero germ normalization. -/
theorem fibreProductCohomologyGerm_equiv₀_symm
    (F : AbelianSheaf.{u, u + 1} X)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (η : Spec (.of Ω) ⟶ S)
    (p : (pointSmallEtale η).fiber.obj U)
    (z : (globalSections (pullback U.hom f)).obj
      ((inverseImage (pullback.snd U.hom f)).obj F)) :
    fibreProductCohomologyGerm f U F 0 η p
        ((Sheaf.H.equiv₀ ((inverseImage (pullback.snd U.hom f)).obj F)
          (etaleTerminalIsTerminal (pullback U.hom f))).symm z) =
      ((pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})).map
        ((directImage f).toRightDerivedZero.app F)
        ((pointSmallEtale η).toPresheafFiber U p ((directImage f).obj F).obj
          ((Continuity.pullbackSectionsEtaleEvaluationIso F
            ((siteBaseChange f).obj U)).hom z)) := by
  simpa only [AddEquiv.apply_symm_apply] using
    fibreProductCohomologyGerm_equiv₀ f U F η p
      ((Sheaf.H.equiv₀ ((inverseImage (pullback.snd U.hom f)).obj F)
        (etaleTerminalIsTerminal (pullback U.hom f))).symm z)

end AlgebraicGeometry.Scheme.EtaleCohomology
