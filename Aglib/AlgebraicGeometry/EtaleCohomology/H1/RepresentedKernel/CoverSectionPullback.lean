/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.DegreeZeroPullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.MarkedCoefficients
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.RepresentedKernel.BaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.RepresentedKernel.CoverClass
public import Aglib.CategoryTheory.Over.RelativeTests

/-! The literal pullback of the original target diagonal is the graph section. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Group.BaseChange
open AlgebraicGeometry.Scheme.Torsors.Restriction

universe u wX wZ

namespace AlgebraicGeometry.Scheme.EtaleCohomology.RepresentedKernel

open SchemeTorsorBaseChange

attribute [local instance] Over.cartesianMonoidalCategory hasSheafifyLarge
  groupSchemeBaseChange_isCommMonObj

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section IntegerSections

variable {X Z : Scheme.{u}} (f : Z ⟶ X)

/-- The original integer-one correspondence applied to a represented terminal section. -/
def representedIntegerSection (A : Grp (Over X)) [IsCommMonObj A.X]
    (s : Over.mk (𝟙 X) ⟶ A.X) : constantIntegerSheaf X ⟶ representedSheaf A :=
  (CategoryTheory.Sheaf.constantIntegerHomGlobalPointEquiv (representedSheaf A)).symm
    (globalSectionSetMap (representedSheaf A) (ULift.up (Additive.ofMul s)))

/-- Under the constant-sheaf adjunction, the represented integer section takes one to the
given terminal section. -/
theorem representedIntegerSection_one (A : Grp (Over X)) [IsCommMonObj A.X]
    (s : Over.mk (𝟙 X) ⟶ A.X) :
    (constantAdjunction X).homEquiv (AddCommGrpCat.of (ULift.{u + 1} ℤ)) _
      (representedIntegerSection A s) (ULift.up (1 : ℤ)) = ULift.up (Additive.ofMul s) := by
  let B := representedSheaf A
  let E := CategoryTheory.Sheaf.constantIntegerHomGlobalPointEquiv B
  let D := Topos.globalPointTerminalEquiv (etaleTerminalIsTerminal X) (underlyingSetSheaf B)
  let z : B.obj.obj (op (etaleTerminal X)) := ULift.up (Additive.ofMul s)
  have hz : D (E (representedIntegerSection A s)) = z :=
    (congrArg D (E.apply_symm_apply (D.symm z))).trans (D.apply_symm_apply z)
  rw [Adjunction.homEquiv_unit]
  exact hz

private theorem representedSectionsPullback (A : Grp (Over X)) [IsCommMonObj A.X]
    (s : Over.mk (𝟙 X) ⟶ A.X) :
    (globalSections Z).map (representedCoefficientPullback f A)
      (globalSectionsPullback f (representedSheaf A) (ULift.up (Additive.ofMul s))) =
      ULift.up (Additive.ofMul
        ((Scheme.Etale.forget Z).map (siteBaseChangeTerminalIso f).inv ≫
          (Over.pullback f).map s)) := by
  let A' := representedSheaf (EtaleCohomology.baseChangedGroup f A)
  let t := representedCoefficientPullback f A
  have hu : (inverseImageAdjunction f).unit.app (representedSheaf A) ≫
      (directImage f).map t = representedCoefficientUnit f A := by
    let adj := inverseImageAdjunction f
    exact (adj.homEquiv_unit _ _ t).symm.trans ((adj.homEquiv _ _).apply_symm_apply _)
  have h : globalSectionsPullback f (representedSheaf A) ≫ (globalSections Z).map t =
      (globalSections X).map (representedCoefficientUnit f A) ≫
        (directImageGlobalSectionsIso f).hom.app A' := by
    dsimp only [globalSectionsPullback]
    rw [Category.assoc, ← (directImageGlobalSectionsIso f).hom.naturality,
      ← Category.assoc, Functor.comp_map, ← Functor.map_comp, hu]
  exact ConcreteCategory.congr_hom h (ULift.up (Additive.ofMul s))

/-- The original integer-section transport pulls back the actual represented section. -/
theorem representedIntegerSection_pullback (A : Grp (Over X)) [IsCommMonObj A.X]
    (s : Over.mk (𝟙 X) ⟶ A.X) :
    (inverseImageIntegerIso f).inv ≫ (inverseImage f).map (representedIntegerSection A s) ≫
      representedCoefficientPullback f A =
    representedIntegerSection (EtaleCohomology.baseChangedGroup f A)
      ((Scheme.Etale.forget Z).map (siteBaseChangeTerminalIso f).inv ≫
        (Over.pullback f).map s) := by
  let I := AddCommGrpCat.of (ULift.{u + 1} ℤ)
  let B := representedSheaf (EtaleCohomology.baseChangedGroup f A)
  let t := representedCoefficientPullback f A
  let a := representedIntegerSection A s
  let e := (inverseImageIntegerIso f).inv
  let z := (Scheme.Etale.forget Z).map (siteBaseChangeTerminalIso f).inv ≫
    (Over.pullback f).map s
  apply ((constantAdjunction Z).homEquiv I B).injective
  apply (AddCommGrpCat.uliftZMultiplesAddEquiv ((globalSections Z).obj B)).injective
  change ((constantAdjunction Z).homEquiv I B (e ≫ (inverseImage f).map a ≫ t))
      (ULift.up (1 : ℤ)) = _
  rw [← Category.assoc, Adjunction.homEquiv_naturality_right]
  have h := constantTransport_homEquiv f I a
  change (constantAdjunction Z).homEquiv I _ (e ≫ (inverseImage f).map a) = _ at h
  rw [h]
  change (globalSections Z).map t
      (globalSectionsPullback f (representedSheaf A)
        ((constantAdjunction X).homEquiv I _ a (ULift.up (1 : ℤ)))) =
    (constantAdjunction Z).homEquiv I B
      (representedIntegerSection (EtaleCohomology.baseChangedGroup f A) z)
        (ULift.up (1 : ℤ))
  rw [representedIntegerSection_one, representedIntegerSection_one]
  exact representedSectionsPullback f A s

/-- Represented integer sections are natural in the original coefficient group. -/
theorem representedIntegerSection_map {A B : Grp (Over X)}
    [IsCommMonObj A.X] [IsCommMonObj B.X] (p : A ⟶ B)
    (s : Over.mk (𝟙 X) ⟶ A.X) :
    representedIntegerSection A s ≫ representedSheafMap p =
      representedIntegerSection B (s ≫ p.hom.hom) := by
  let I := AddCommGrpCat.of (ULift.{u + 1} ℤ)
  let L := representedSheaf B
  apply ((constantAdjunction X).homEquiv I L).injective
  apply (AddCommGrpCat.uliftZMultiplesAddEquiv ((globalSections X).obj L)).injective
  change ((constantAdjunction X).homEquiv I L
      (representedIntegerSection A s ≫ representedSheafMap p)) (ULift.up (1 : ℤ)) = _
  rw [Adjunction.homEquiv_naturality_right]
  change (globalSections X).map (representedSheafMap p)
      ((constantAdjunction X).homEquiv I _ (representedIntegerSection A s)
        (ULift.up (1 : ℤ))) = _
  rw [representedIntegerSection_one]
  exact (representedIntegerSection_one B (s ≫ p.hom.hom)).symm

end IntegerSections

section Graph

variable {S Z : Scheme.{u}} {H : Grp (Over S)} [IsCommMonObj H.X]
  (f : Z ⟶ H.X.left)

omit [IsCommMonObj H.X] in
private theorem diagonal_pullback_graph :
    ((Scheme.Etale.forget Z).map (siteBaseChangeTerminalIso f).inv ≫
      (Over.pullback f).map (relativeTargetDiagonal H.X)) ≫
        ((groupSchemeBaseChangeComp f H.X.hom).inv.app H).hom.hom =
      (Over.mapPullbackAdj (f ≫ H.X.hom)).homEquiv (Over.mk (𝟙 Z)) H.X
        (Over.homMk f (by simp)) := by
  let g := H.X.hom
  let X := H.X.left
  let t : Over.mk (𝟙 Z) ⟶ (Over.pullback f).obj (Over.mk (𝟙 X)) :=
    (Scheme.Etale.forget Z).map (siteBaseChangeTerminalIso f).inv
  let δ := relativeTargetDiagonal H.X
  let c := ((groupSchemeBaseChangeComp f g).inv.app H).hom.hom
  have ht : t.left ≫ pullback.snd (𝟙 X) f = 𝟙 Z := Over.w t
  have ht' : t.left ≫ pullback.fst (𝟙 X) f = f := by
    calc
      _ = t.left ≫ pullback.fst (𝟙 X) f ≫ 𝟙 X := (Category.comp_id _).symm
      _ = t.left ≫ pullback.snd (𝟙 X) f ≫ f := by rw [pullback.condition]
      _ = _ := (Category.assoc _ _ _).symm.trans
        ((congrArg (fun b : Z ⟶ Z => b ≫ f) ht).trans (Category.id_comp f))
  have hg : ((Over.mapPullbackAdj (f ≫ H.X.hom)).homEquiv (Over.mk (𝟙 Z)) H.X
      (Over.homMk f (by simp))).left = pullback.lift f (𝟙 Z) (by simp) := by
    simp only [Over.mapPullbackAdj, Adjunction.mkOfHomEquiv_homEquiv]
    rfl
  let d := (Over.pullback f).map δ
  let ρ := pullback.snd H.X.hom g
  have hdFst : d.left ≫ pullback.fst ρ f = pullback.fst (𝟙 X) f ≫ δ.left :=
    Over.RelativeTests.pullback_map_fst f δ
  have hdSnd : d.left ≫ pullback.snd ρ f = pullback.snd (𝟙 X) f :=
    Over.RelativeTests.pullback_map_snd f δ
  have hδ : δ.left ≫ pullback.fst H.X.hom g = 𝟙 X :=
    pullback.lift_fst _ _ _
  apply Over.OverMorphism.ext
  rw [hg]
  change ((t ≫ d) ≫ c).left = pullback.lift f (𝟙 Z) (by simp [g])
  apply pullback.hom_ext
  · rw [pullback.lift_fst]
    simp only [Over.comp_left, Category.assoc]
    rw [groupSchemeBaseChangeComp_inv_left_fst]
    calc
      _ = t.left ≫ (d.left ≫ pullback.fst ρ f) ≫ pullback.fst H.X.hom g := by
        simp only [Category.assoc, ρ]
      _ = t.left ≫ pullback.fst (𝟙 X) f ≫ (δ.left ≫ pullback.fst H.X.hom g) := by
        rw [hdFst]
        simp only [Category.assoc]
      _ = f := by rw [hδ, Category.comp_id]; exact ht'
  · rw [pullback.lift_snd]
    simp only [Over.comp_left, Category.assoc]
    rw [groupSchemeBaseChangeComp_inv_left_snd]
    exact (congrArg (fun b : pullback (𝟙 X) f ⟶ Z => t.left ≫ b) hdSnd).trans ht

/-- The transported diagonal is the original graph of the given map into the target. -/
theorem representedTargetDiagonal_pullback :
    (inverseImageIntegerIso f).inv ≫
      (inverseImage f).map (representedTargetDiagonal (H := H)) ≫
      representedCoefficientPullback f (Group.BaseChange.baseChangedGroup H.X.hom H) ≫
      representedSheafMap ((groupSchemeBaseChangeComp f H.X.hom).inv.app H) =
    representedIntegerSection (Group.BaseChange.baseChangedGroup (f ≫ H.X.hom) H)
      ((Over.mapPullbackAdj (f ≫ H.X.hom)).homEquiv (Over.mk (𝟙 Z)) H.X
        (Over.homMk f (by simp))) := by
  let A := Group.BaseChange.baseChangedGroup H.X.hom H
  let δ := relativeTargetDiagonal H.X
  let c := (groupSchemeBaseChangeComp f H.X.hom).inv.app H
  change (inverseImageIntegerIso f).inv ≫
      (inverseImage f).map (representedIntegerSection A δ) ≫
      representedCoefficientPullback f A ≫ representedSheafMap c = _
  rw [← Category.assoc ((inverseImage f).map (representedIntegerSection A δ))
    (representedCoefficientPullback f A), ← Category.assoc (inverseImageIntegerIso f).inv]
  rw [representedIntegerSection_pullback, representedIntegerSection_map]
  rw [diagonal_pullback_graph]

end Graph

section Row

variable {S X Z : Scheme.{u}} (f : Z ⟶ X) (g : X ⟶ S)
  {K G H : Grp (Over S)} {q : G ⟶ H}
  [IsCommMonObj K.X] [IsCommMonObj G.X] [IsCommMonObj H.X]
  (m : KernelMarking K G H q)

/-- The original group is commutative after the two base changes. -/
local instance successiveBaseChangeComm (A : Grp (Over S)) [IsCommMonObj A.X] :
    IsCommMonObj (((groupSchemeBaseChange g).functor ⋙
      (groupSchemeBaseChange f).functor).obj A).X := by
  let B := (groupSchemeBaseChange g).functor.obj A
  let : IsCommMonObj B.X := groupSchemeBaseChange_isCommMonObj g A
  exact groupSchemeBaseChange_isCommMonObj f B

/-- The original group composition comparison gives the same represented marked row after
successive or direct pullback. -/
def markedKernelBaseChangeCompIso :
    markedKernelSequence (Group.BaseChange.kernelMarking (f ≫ g) m) ≅
      markedKernelSequence (Group.BaseChange.kernelMarking f
        (Group.BaseChange.kernelMarking g m)) := by
  have square {A B C D : Grp (Over Z)}
      [IsCommMonObj A.X] [IsCommMonObj B.X] [IsCommMonObj C.X] [IsCommMonObj D.X]
      (a : A ⟶ B) (b : C ⟶ D) (c : A ⟶ C) (d : B ⟶ D) (h : c ≫ b = a ≫ d) :
      representedSheafMap c ≫ representedSheafMap b =
        representedSheafMap a ≫ representedSheafMap d := by
    rw [← representedSheafMap_comp, ← representedSheafMap_comp, h]
  let c := groupSchemeBaseChangeComp f g
  refine ShortComplex.isoMk
    (MarkedCoefficients.representedSheafIso (c.app K))
    (MarkedCoefficients.representedSheafIso (c.app G))
    (MarkedCoefficients.representedSheafIso (c.app H)) ?_ ?_
  · exact square _ _ _ _
      (groupSchemeBaseChangeComp_hom_naturality f g m.inclusion).symm
  · exact square _ _ _ _
      (groupSchemeBaseChangeComp_hom_naturality f g q).symm

end Row


section CoverClass

open CategoryTheory.Abelian

attribute [local instance] successiveBaseChangeComm

variable {S Z : Scheme.{u}} {K G H : Grp (Over S)} {q : G ⟶ H}
  [IsCommMonObj K.X] [IsCommMonObj G.X] [IsCommMonObj H.X]
  (m : KernelMarking K G H q)

/-- An étale surjective original quotient makes its pulled-back marked row short exact. -/
theorem markedKernelSequence_baseChange_shortExact (b : Z ⟶ S)
    [Etale q.hom.hom.left] [Surjective q.hom.hom.left] :
    (markedKernelSequence (Group.BaseChange.kernelMarking b m)).ShortExact := by
  let r := (groupSchemeBaseChange b).functor.map q
  let : Etale r.hom.hom.left := Group.BaseChange.map_etale b q inferInstance
  let : Surjective r.hom.hom.left := Group.BaseChange.map_surjective b q inferInstance
  let : Epi (representedSheafMap r) := representedSheafMap_epi_of_etale_surjective r
  exact markedKernelSequence_shortExact (Group.BaseChange.kernelMarking b m)

private theorem boundary_of_section_comp
    {C : Type*} [Category C] [Abelian C] [HasExt.{wZ} C]
    {R R' : ShortComplex C} (hR : R.ShortExact) (hR' : R'.ShortExact)
    (φ : R ⟶ R') {P : C} (a : P ⟶ R.X₃) :
    ((Ext.mk₀ a).comp hR.extClass (zero_add 1)).comp (Ext.mk₀ φ.τ₁) (add_zero 1) =
      (Ext.mk₀ (a ≫ φ.τ₃)).comp hR'.extClass (zero_add 1) := by
  rw [Ext.comp_assoc_of_third_deg_zero, hR.extClass_naturality hR' φ, Ext.mk₀_comp_mk₀_assoc]

variable (f : Z ⟶ H.X.left)
  [Etale K.X.hom] [IsFinite q.hom.hom.left] [Etale q.hom.hom.left] [Surjective q.hom.hom.left]
  [HasExt.{wX} (AbelianSheaf.{u, u + 1} H.X.left)]
  [HasExt.{wZ} (AbelianSheaf.{u, u + 1} Z)]

/-- The original kernel is étale after pullback to the cover target. -/
local instance targetBaseChangedKernelEtale :
    Etale (Group.BaseChange.baseChangedGroup H.X.hom K).X.hom :=
  baseChangedGroup_etale H.X.hom K

/-- The original relative-cover class pulls back to the unsigned boundary of the graph section
in the original direct marked row. -/
theorem relativeCoverH1Pullback_graph :
    let hD := markedKernelSequence_baseChange_shortExact m (f ≫ H.X.hom)
    coefficientMap (representedSheafMap ((groupSchemeBaseChangeComp f H.X.hom).inv.app K))
        (representedH1Pullback.{u, wX, wZ} f (Group.BaseChange.baseChangedGroup H.X.hom K)
          (torsorExtClass (relativeCoverTorsor m))) =
      (Ext.mk₀ (representedIntegerSection (Group.BaseChange.baseChangedGroup (f ≫ H.X.hom) H)
        ((Over.mapPullbackAdj (f ≫ H.X.hom)).homEquiv (Over.mk (𝟙 Z)) H.X
          (Over.homMk f (by simp))))).comp hD.extClass (zero_add 1) := by
  intro hD
  let g := H.X.hom
  let Kₓ := Group.BaseChange.baseChangedGroup g K
  let mₓ := Group.BaseChange.kernelMarking g m
  let hG := relativeMarkedKernelSequence_shortExact m
  let e := markedKernelBaseChangeCompIso f g m
  let hS := ShortComplex.shortExact_of_iso e hD
  let φ := markedKernelBaseChange f mₓ
  let a := representedTargetDiagonal (H := H)
  let aF := (inverseImageIntegerIso f).inv ≫ (inverseImage f).map a ≫ φ.τ₃
  let b := representedIntegerSection (Group.BaseChange.baseChangedGroup (f ≫ g) H)
    ((Over.mapPullbackAdj (f ≫ g)).homEquiv (Over.mk (𝟙 Z)) H.X (Over.homMk f (by simp [g])))
  let x := torsorExtClass (relativeCoverTorsor m)
  have hOrig : x = (Ext.mk₀ a).comp hG.extClass (zero_add 1) := relativeCoverExtClass_eq m
  have hLift := markedKernelBaseChange_boundary f mₓ hG hS a
  have hCoeff := markedKernelBaseChange_τ₁ f mₓ
  have hP : representedH1Pullback.{u, wX, wZ} f Kₓ x =
      (Ext.mk₀ aF).comp hS.extClass (zero_add 1) := by
    change coefficientMap (representedSheafBaseChangeIso f Kₓ).hom
      (h1Pullback f (representedSheaf Kₓ) x) = _
    rw [← hCoeff, hOrig]
    exact hLift
  have hSect : aF ≫ e.inv.τ₃ = b := by
    dsimp only [aF]
    simp only [Category.assoc]
    exact representedTargetDiagonal_pullback f
  change coefficientMap e.inv.τ₁ (representedH1Pullback.{u, wX, wZ} f Kₓ x) =
    (Ext.mk₀ b).comp hD.extClass (zero_add 1)
  rw [hP]
  change ((Ext.mk₀ aF).comp hS.extClass (zero_add 1)).comp (Ext.mk₀ e.inv.τ₁) (add_zero 1) =
    (Ext.mk₀ b).comp hD.extClass (zero_add 1)
  rw [boundary_of_section_comp hS hD e.inv aF, hSect]

end CoverClass

end AlgebraicGeometry.Scheme.EtaleCohomology.RepresentedKernel
