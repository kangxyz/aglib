/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.RepresentedKernel.Marked
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.RepresentedBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.TorsorPullback
public import Aglib.AlgebraicGeometry.Group.BaseChange.MarkedKernel

/-! Base change of the original represented marked kernel sequence and its boundary. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
universe u wT wS

namespace AlgebraicGeometry.Scheme.EtaleCohomology.RepresentedKernel

open SchemeTorsorBaseChange

attribute [local instance] Over.cartesianMonoidalCategory hasSheafifyLarge

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S T : Scheme.{u}} (f : S ⟶ T)

/-- The adjoint of the original pullback of sections of a represented coefficient. -/
def representedCoefficientPullback (A : Grp (Over T)) [IsCommMonObj A.X] :
    (inverseImage f).obj (representedSheaf A) ⟶ representedSheaf (baseChangedGroup f A) :=
  ((inverseImageAdjunction f).homEquiv _ _).symm (representedCoefficientUnit f A)

/-- The original coefficient adjoints commute with the pulled-back group morphism. -/
theorem representedCoefficientPullback_naturality {A B : Grp (Over T)}
    [IsCommMonObj A.X] [IsCommMonObj B.X] (r : A ⟶ B) :
    representedCoefficientPullback f A ≫
        representedSheafMap ((Over.pullback f).mapGrp.map r) =
      (inverseImage f).map (representedSheafMap r) ≫ representedCoefficientPullback f B := by
  let adj := inverseImageAdjunction f
  let a := representedCoefficientUnit f A
  let b := representedCoefficientUnit f B
  let s := representedSheafMap r
  let t := representedSheafMap ((Over.pullback f).mapGrp.map r)
  have h : s ≫ b = a ≫ (directImage f).map t := by
    apply Sheaf.hom_ext
    exact representedBaseChangeUnit_naturality f r
  change (adj.homEquiv _ _).symm a ≫ t =
    (inverseImage f).map s ≫ (adj.homEquiv _ _).symm b
  exact (adj.homEquiv_naturality_right_symm a t).symm.trans
    ((congrArg (adj.homEquiv (representedSheaf A)
      (representedSheaf (baseChangedGroup f B))).symm h.symm).trans
        (adj.homEquiv_naturality_left_symm s b))

/-- The original commutative group structure after base change. -/
local instance markedGroupBaseChangeComm (A : Grp (Over T)) [IsCommMonObj A.X] :
    IsCommMonObj (Group.BaseChange.baseChangedGroup f A).X :=
  baseChangedGroup_comm f A

variable {K G H : Grp (Over T)} {q : G ⟶ H}
  [IsCommMonObj K.X] [IsCommMonObj G.X] [IsCommMonObj H.X]
  (m : KernelMarking K G H q)

/-- The three original coefficient adjoints give the base-change morphism of marked rows. -/
def markedKernelBaseChange :
    (markedKernelSequence m).map (inverseImage f) ⟶
      markedKernelSequence (Group.BaseChange.kernelMarking f m) where
  τ₁ := representedCoefficientPullback f K
  τ₂ := representedCoefficientPullback f G
  τ₃ := representedCoefficientPullback f H
  comm₁₂ := representedCoefficientPullback_naturality f m.inclusion
  comm₂₃ := representedCoefficientPullback_naturality f q

/-- For the étale kernel, the first component is the original coefficient isomorphism. -/
theorem markedKernelBaseChange_τ₁ [Etale K.X.hom] :
    (markedKernelBaseChange f m).τ₁ = (representedSheafBaseChangeIso f K).hom :=
  representedCoefficientUnit_adjoint f K

private theorem map_boundary_of_section
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasExt.{wT} C] [HasExt.{wS} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {R : ShortComplex C} {R' : ShortComplex D} (hR : R.ShortExact) (hR' : R'.ShortExact)
    (φ : R.map F ⟶ R') {P : C} {P' : D} (i : P' ⟶ F.obj P) (a : P ⟶ R.X₃) :
    ((Ext.mk₀ i).comp (((Ext.mk₀ a).comp hR.extClass (zero_add 1)).mapExactFunctor F)
        (zero_add 1)).comp (Ext.mk₀ φ.τ₁) (add_zero 1) =
      (Ext.mk₀ (i ≫ F.map a ≫ φ.τ₃)).comp hR'.extClass (zero_add 1) := by
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.mapExactFunctor_extClass]
  have h := (hR.map_of_exact F).extClass_naturality hR' φ
  rw [Ext.mk₀_comp_mk₀_assoc, Ext.comp_assoc_of_third_deg_zero, h,
    Ext.mk₀_comp_mk₀_assoc, Category.assoc]

variable [HasExt.{wT} (AbelianSheaf.{u, u + 1} T)]
  [HasExt.{wS} (AbelianSheaf.{u, u + 1} S)]

/-- Pullback and coefficient transport take the original section boundary to the original
boundary of the pulled-back section. -/
theorem markedKernelBaseChange_boundary
    (h : (markedKernelSequence m).ShortExact)
    (h' : (markedKernelSequence (Group.BaseChange.kernelMarking f m)).ShortExact)
    (a : constantIntegerSheaf T ⟶ representedSheaf H) :
    coefficientMap (markedKernelBaseChange f m).τ₁
        (h1Pullback.{u, wT, wS} f (representedSheaf K)
          ((Ext.mk₀ a).comp h.extClass (zero_add 1))) =
      (Ext.mk₀ ((inverseImageIntegerIso f).inv ≫ (inverseImage f).map a ≫
        (markedKernelBaseChange f m).τ₃)).comp h'.extClass (zero_add 1) := by
  let F := inverseImage f
  let φ := markedKernelBaseChange f m
  let i := (inverseImageIntegerIso f).inv
  change ((Ext.mk₀ i).comp (((Ext.mk₀ a).comp h.extClass (zero_add 1)).mapExactFunctor F)
      (zero_add 1)).comp (Ext.mk₀ φ.τ₁) (add_zero 1) =
    (Ext.mk₀ (i ≫ F.map a ≫ φ.τ₃)).comp h'.extClass (zero_add 1)
  exact map_boundary_of_section F h h' φ i a

end AlgebraicGeometry.Scheme.EtaleCohomology.RepresentedKernel
