/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.RepresentedKernel.CoverSectionPullback

/-! The graph boundary after removing the identity pullback of the original marking. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry
open Scheme.Group Scheme.Group.BaseChange
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.EtaleCohomology.RepresentedKernel

universe u wX wZ

attribute [local instance] Over.cartesianMonoidalCategory hasSheafifyLarge
  groupSchemeBaseChange_isCommMonObj successiveBaseChangeComm

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section TerminalComparison

variable {S Z : Scheme.{u}} {b d : Z ⟶ S}

/-- The canonical comparison from the pullback of the terminal-base family to the actual
direct base change. -/
def terminalGroupComparison (h : b = d) :
    (groupSchemeBaseChange (𝟙 S)).functor ⋙ (groupSchemeBaseChange b).functor ≅
      (groupSchemeBaseChange d).functor :=
  (Functor.isoWhiskerRight groupSchemeBaseChangeId (groupSchemeBaseChange b).functor ≪≫
    Functor.leftUnitor _) ≪≫ groupSchemeBaseChangeCongr h

private theorem terminalGroupComparison_hom_app (h : b = d) (A : Grp (Over S)) :
    (terminalGroupComparison h).hom.app A =
      (groupSchemeBaseChange b).functor.map (groupSchemeBaseChangeId.hom.app A) ≫
        (groupSchemeBaseChangeCongr h).hom.app A := by
  simp only [terminalGroupComparison, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.leftUnitor_hom_app]
  exact congrArg (fun p => p ≫ (groupSchemeBaseChangeCongr h).hom.app A)
    (Category.comp_id ((groupSchemeBaseChange b).functor.map (groupSchemeBaseChangeId.hom.app A)))

variable {K A B : Grp (Over S)} {q : A ⟶ B}
  [IsCommMonObj K.X] [IsCommMonObj A.X] [IsCommMonObj B.X]

/-- The canonical terminal comparison on the three groups of the original marked row. -/
def terminalMarkedKernelRowIso (h : b = d) (m : KernelMarking K A B q) :
    markedKernelSequence (Group.BaseChange.kernelMarking b
      (Group.BaseChange.kernelMarking (𝟙 S) m)) ≅
    markedKernelSequence (Group.BaseChange.kernelMarking d m) := by
  have square {A B C D : Grp (Over Z)}
      [IsCommMonObj A.X] [IsCommMonObj B.X] [IsCommMonObj C.X] [IsCommMonObj D.X]
      (a : A ⟶ B) (b : C ⟶ D) (c : A ⟶ C) (d : B ⟶ D) (h : c ≫ b = a ≫ d) :
      representedSheafMap c ≫ representedSheafMap b =
        representedSheafMap a ≫ representedSheafMap d := by
    rw [← representedSheafMap_comp, ← representedSheafMap_comp, h]
  let c := terminalGroupComparison h
  refine ShortComplex.isoMk
    (MarkedCoefficients.representedSheafIso (c.app K))
    (MarkedCoefficients.representedSheafIso (c.app A))
    (MarkedCoefficients.representedSheafIso (c.app B)) ?_ ?_
  · exact square _ _ _ _ (c.hom.naturality m.inclusion).symm
  · exact square _ _ _ _ (c.hom.naturality q).symm

/-- The terminal row comparison uses the original comparison on the kernel. -/
theorem terminalMarkedKernelRowIso_hom_τ₁ (h : b = d) (m : KernelMarking K A B q) :
    (terminalMarkedKernelRowIso h m).hom.τ₁ =
      representedSheafMap ((terminalGroupComparison h).hom.app K) := rfl

/-- The terminal row comparison uses the original comparison on the source. -/
theorem terminalMarkedKernelRowIso_hom_τ₂ (h : b = d) (m : KernelMarking K A B q) :
    (terminalMarkedKernelRowIso h m).hom.τ₂ =
      representedSheafMap ((terminalGroupComparison h).hom.app A) := rfl

/-- The terminal row comparison uses the original comparison on the target. -/
theorem terminalMarkedKernelRowIso_hom_τ₃ (h : b = d) (m : KernelMarking K A B q) :
    (terminalMarkedKernelRowIso h m).hom.τ₃ =
      representedSheafMap ((terminalGroupComparison h).hom.app B) := rfl

private theorem terminalGraph_comp (h : b = d) (B : Grp (Over S))
    (a₀ : Z ⟶ (Group.BaseChange.baseChangedGroup (𝟙 S) B).X.left)
    (a : Z ⟶ B.X.left)
    (h₀ : a₀ ≫ (Group.BaseChange.baseChangedGroup (𝟙 S) B).X.hom = b)
    (h₁ : a ≫ B.X.hom = d) (hp : a₀ ≫ pullback.fst B.X.hom (𝟙 S) = a) :
    ((Over.mapPullbackAdj b).homEquiv (Over.mk (𝟙 Z))
      (Group.BaseChange.baseChangedGroup (𝟙 S) B).X
      (Over.homMk a₀ (h₀.trans (Category.id_comp b).symm))) ≫
      ((terminalGroupComparison h).hom.app B).hom.hom =
    (Over.mapPullbackAdj d).homEquiv (Over.mk (𝟙 Z)) B.X
      (Over.homMk a (h₁.trans (Category.id_comp d).symm)) := by
  subst d
  let adj := Over.mapPullbackAdj b
  let j := (groupSchemeBaseChangeId.hom.app B).hom.hom
  let s : (Over.map b).obj (Over.mk (𝟙 Z)) ⟶
      (Group.BaseChange.baseChangedGroup (𝟙 S) B).X := Over.homMk a₀ (by simpa using h₀)
  let t : (Over.map b).obj (Over.mk (𝟙 Z)) ⟶ B.X := Over.homMk a (by simpa using h₁)
  have hs : s ≫ j = t := by
    apply Over.OverMorphism.ext
    change a₀ ≫ j.left = a
    exact (congrArg (fun p => a₀ ≫ p) (groupSchemeBaseChangeId_hom_app_left B)).trans hp
  have hc : (terminalGroupComparison (rfl : b = b)).hom.app B =
      (groupSchemeBaseChange b).functor.map (groupSchemeBaseChangeId.hom.app B) := by
    rw [terminalGroupComparison_hom_app]
    simp only [groupSchemeBaseChangeCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app]
    exact Category.comp_id _
  rw [hc, groupSchemeBaseChange_map_hom_hom]
  change (adj.homEquiv _ _ s) ≫ (Over.pullback b).map j = adj.homEquiv _ _ t
  exact (adj.homEquiv_naturality_right s j).symm.trans
    (congrArg (adj.homEquiv (Over.mk (𝟙 Z)) B.X) hs)

private theorem terminalMarkedIntegerSection_map (h : b = d) (m : KernelMarking K A B q)
    (p₀ : Over.mk (𝟙 Z) ⟶
      (Group.BaseChange.baseChangedGroup b (Group.BaseChange.baseChangedGroup (𝟙 S) B)).X)
    (p : Over.mk (𝟙 Z) ⟶ (Group.BaseChange.baseChangedGroup d B).X)
    (hp : p₀ ≫ ((terminalGroupComparison h).hom.app B).hom.hom = p) :
    representedIntegerSection _ p₀ ≫ (terminalMarkedKernelRowIso h m).hom.τ₃ =
      representedIntegerSection _ p := by
  rw [terminalMarkedKernelRowIso_hom_τ₃, representedIntegerSection_map, hp]

/-- Transport the unsigned boundary along the original terminal marked-row comparison. -/
theorem terminalMarkedGraphBoundary_transport (h : b = d) (m : KernelMarking K A B q)
    [HasExt.{wZ} (AbelianSheaf.{u, u + 1} Z)]
    (hB : (markedKernelSequence (Group.BaseChange.kernelMarking b
      (Group.BaseChange.kernelMarking (𝟙 S) m))).ShortExact)
    (hD : (markedKernelSequence (Group.BaseChange.kernelMarking d m)).ShortExact)
    (a₀ : Z ⟶ (Group.BaseChange.baseChangedGroup (𝟙 S) B).X.left)
    (a : Z ⟶ B.X.left)
    (h₀ : a₀ ≫ (Group.BaseChange.baseChangedGroup (𝟙 S) B).X.hom = b)
    (h₁ : a ≫ B.X.hom = d) (hp : a₀ ≫ pullback.fst B.X.hom (𝟙 S) = a) :
    let p₀ := (Over.mapPullbackAdj b).homEquiv (Over.mk (𝟙 Z))
      (Group.BaseChange.baseChangedGroup (𝟙 S) B).X
      (Over.homMk a₀ (h₀.trans (Category.id_comp b).symm))
    let p := (Over.mapPullbackAdj d).homEquiv (Over.mk (𝟙 Z)) B.X
      (Over.homMk a (h₁.trans (Category.id_comp d).symm))
    coefficientMap (representedSheafMap ((terminalGroupComparison h).hom.app K))
        ((Ext.mk₀ (representedIntegerSection _ p₀)).comp hB.extClass (zero_add 1)) =
      (Ext.mk₀ (representedIntegerSection _ p)).comp hD.extClass (zero_add 1) := by
  intro p₀ p
  let e := terminalMarkedKernelRowIso h m
  let s₀ := representedIntegerSection
    (Group.BaseChange.baseChangedGroup b (Group.BaseChange.baseChangedGroup (𝟙 S) B)) p₀
  let s := representedIntegerSection (Group.BaseChange.baseChangedGroup d B) p
  have hs : s₀ ≫ e.hom.τ₃ = s :=
    terminalMarkedIntegerSection_map h m p₀ p (terminalGraph_comp h B a₀ a h₀ h₁ hp)
  have he : e.hom.τ₁ = representedSheafMap ((terminalGroupComparison h).hom.app K) :=
    terminalMarkedKernelRowIso_hom_τ₁ h m
  rw [← he]
  change ((Ext.mk₀ s₀).comp hB.extClass (zero_add 1)).comp (Ext.mk₀ e.hom.τ₁) (add_zero 1) =
    (Ext.mk₀ s).comp hD.extClass (zero_add 1)
  rw [Ext.comp_assoc_of_third_deg_zero, hB.extClass_naturality hD e.hom,
    Ext.mk₀_comp_mk₀_assoc, hs]

end TerminalComparison

section CoverClass

variable {S Z : Scheme.{u}} {K A B : Grp (Over S)} {q : A ⟶ B}
  [IsCommMonObj K.X] [IsCommMonObj A.X] [IsCommMonObj B.X]
  (m : KernelMarking K A B q)
  [Etale K.X.hom] [IsFinite q.hom.hom.left] [Etale q.hom.hom.left] [Surjective q.hom.hom.left]

set_option hygiene false in
local notation "B₀" => Group.BaseChange.baseChangedGroup (𝟙 S) B
set_option hygiene false in
local notation "K₀" => Group.BaseChange.baseChangedGroup (𝟙 S) K
set_option hygiene false in
local notation "q₀" => (groupSchemeBaseChange (𝟙 S)).functor.map q
set_option hygiene false in
local notation "m₀" => Group.BaseChange.kernelMarking (𝟙 S) m

/-- The original quotient is finite after terminal base change. -/
local instance terminalQuotientFinite : IsFinite (q₀).hom.hom.left :=
  Group.BaseChange.map_finite (𝟙 S) q inferInstance

/-- The original quotient is étale after terminal base change. -/
local instance terminalQuotientEtale : Etale (q₀).hom.hom.left :=
  Group.BaseChange.map_etale (𝟙 S) q inferInstance

/-- The original quotient is surjective after terminal base change. -/
local instance terminalQuotientSurjective : Surjective (q₀).hom.hom.left :=
  Group.BaseChange.map_surjective (𝟙 S) q inferInstance

/-- The original kernel is étale after terminal base change. -/
local instance terminalKernelEtale : Etale (K₀).X.hom :=
  Scheme.EtaleCohomology.baseChangedGroup_etale (𝟙 S) K

/-- The original coefficient kernel is étale over the cover target. -/
local instance terminalCoverCoefficientEtale :
    Etale (Group.BaseChange.baseChangedGroup (B₀).X.hom (K₀)).X.hom :=
  Scheme.EtaleCohomology.baseChangedGroup_etale (B₀).X.hom (K₀)

variable [HasExt.{wX} (AbelianSheaf.{u, u + 1} (B₀).X.left)]
  [HasExt.{wZ} (AbelianSheaf.{u, u + 1} Z)]

/-- The original cover on the terminal family gives the graph boundary on the direct marked row.
The identification of the cover and the first projection fix the original torsor and section. -/
theorem relativeCoverH1Pullback_terminal_of_eq
    (f : Z ⟶ (B₀).X.left) (a : Z ⟶ B.X.left) (d : Z ⟶ S)
    (hb : f ≫ (B₀).X.hom = d) (ha : a ≫ B.X.hom = d)
    (hf : f ≫ pullback.fst B.X.hom (𝟙 S) = a)
    (P : CategoryTheory.Sheaf.Torsor
      (representedSheaf (Group.BaseChange.baseChangedGroup (B₀).X.hom (K₀))))
    (hP : P = relativeCoverTorsor (m₀)) :
    let hD := markedKernelSequence_baseChange_shortExact m d
    let c := terminalGroupComparison hb
    let p := (Over.mapPullbackAdj d).homEquiv (Over.mk (𝟙 Z)) B.X
      (Over.homMk a (ha.trans (Category.id_comp d).symm))
    coefficientMap (representedSheafMap (c.hom.app K))
        (coefficientMap (representedSheafMap ((groupSchemeBaseChangeComp f (B₀).X.hom).inv.app
          (K₀)))
          (representedH1Pullback.{u, wX, wZ} f
            (Group.BaseChange.baseChangedGroup (B₀).X.hom (K₀)) (torsorExtClass P))) =
      (Ext.mk₀ (representedIntegerSection _ p)).comp hD.extClass (zero_add 1) := by
  intro hD c p
  subst P
  let g := (B₀).X.hom
  let hB := markedKernelSequence_baseChange_shortExact (m₀) (f ≫ g)
  let t := coefficientMap (representedSheafMap (c.hom.app K))
  have hG := relativeCoverH1Pullback_graph (m := m₀) (f := f)
  have hT := terminalMarkedGraphBoundary_transport hb m hB hD f a rfl ha hf
  exact (congrArg t hG).trans hT

end CoverClass

end AlgebraicGeometry.Scheme.EtaleCohomology.RepresentedKernel
