/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.FiniteActionLocalSplit
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.TrivialCoverSheafFunctor
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.CoverSheafBaseChangeNat
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.FiniteSetLocalCharts
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.Limits.FintypeCat

/-! The actual sheaf colimit of a finite action is locally a finite constant
sheaf. Colimits are taken after sheafification, in the sheaf category. -/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.FiniteEtale.SheafDescent

noncomputable section
set_option autoImplicit false

open _root_.CategoryTheory _root_.CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCohomology

namespace AlgebraicGeometry.Scheme.FiniteEtale
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (Fiber baseChange fiberToFinite)

universe u

instance setInverseImage_isLeftAdjoint {X S : Scheme.{u}} (f : S ⟶ X) :
    (setInverseImage f).IsLeftAdjoint :=
  (setInverseImageAdjunction f).isLeftAdjoint

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
instance constantSetSheaf_isLeftAdjoint (X : Scheme.{u}) :
    (constantSheaf (Scheme.smallEtaleTopology X) (Type (u + 1))).IsLeftAdjoint :=
  (constantSheafAdj (Scheme.smallEtaleTopology X) (Type (u + 1))
    (MorphismProperty.Over.mkIdTerminal (@Etale : MorphismProperty Scheme.{u}) X)).isLeftAdjoint

variable {G : Type} [Group G] [Fintype G]

/-- This is the finite orbit type expressed as a categorical colimit in Types. -/
abbrev finiteActionOrbitType (E : SingleObj G ⥤ FintypeCat.{u}) : Type (u + 1) :=
  colimit (E ⋙ FintypeCat.incl ⋙ uliftFunctor.{u + 1})

set_option linter.unusedFintypeInType false in
-- Preserve the original supplied hypotheses and binder order.
instance finiteActionOrbitType_finite (E : SingleObj G ⥤ FintypeCat.{u}) :
    Finite (finiteActionOrbitType E) := by
  let : ∀ j, Finite ((E ⋙ FintypeCat.incl ⋙ uliftFunctor.{u + 1}).obj j) :=
    fun j => inferInstanceAs (Finite (ULift.{u + 1} (E.obj j)))
  exact inferInstanceAs (Finite (colimit (E ⋙ FintypeCat.incl ⋙ uliftFunctor.{u + 1})))

/-- The isomorphism from the colimit of constant sheaves of a finite action to the constant
sheaf of its orbit type. -/
def finiteConstantActionColimitIso (X : Scheme.{u}) (E : SingleObj G ⥤ FintypeCat.{u}) :
    colimit (E ⋙ FintypeCat.incl ⋙ uliftFunctor.{u + 1} ⋙
      constantSheaf (Scheme.smallEtaleTopology X) (Type (u + 1))) ≅
      (constantSheaf (Scheme.smallEtaleTopology X) (Type (u + 1))).obj (finiteActionOrbitType E) :=
  (preservesColimitIso (constantSheaf (Scheme.smallEtaleTopology X) (Type (u + 1)))
    (E ⋙ FintypeCat.incl ⋙ uliftFunctor.{u + 1})).symm

/-- Inverse image carries the actual sheaf colimit to the sheaf colimit of
actual base-changed covers, naturally in all action maps. -/
def coverDiagramSheafColimitBaseChangeIso {X S : Scheme.{u}}
    (f : S ⟶ X) [Etale f] (D : SingleObj G ⥤ Scheme.FiniteEtale X) :
    (setInverseImage f).obj (coverDiagramSheafColimit D) ≅
      coverDiagramSheafColimit (D ⋙ baseChange f) :=
  preservesColimitIso (setInverseImage f) (D ⋙ finiteCoverSectionSheafFunctor X) ≪≫
    HasColimit.isoOfNatIso
      (Functor.isoWhiskerLeft D (finiteCoverSectionSheafBaseChangeNatIso f))

/-- After an equivariant cover comparison, the sheaf diagram is constant
with exactly the finite fibre action that was normalized at the point. -/
def constantActionBaseChangeSheafIso {X S : Scheme.{u}} (f : S ⟶ X) [Etale f]
    (E : SingleObj G ⥤ FintypeCat.{u}) :
    (E ⋙ trivialCoverFunctor X) ⋙ baseChange f ⋙ finiteCoverSectionSheafFunctor S ≅
      E ⋙ FintypeCat.incl ⋙ uliftFunctor.{u + 1} ⋙
        constantSheaf (Scheme.smallEtaleTopology S) (Type (u + 1)) :=
  Functor.isoWhiskerLeft (E ⋙ trivialCoverFunctor X)
      (finiteCoverSectionSheafBaseChangeNatIso f).symm ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft E (trivialCoverConstantNatIso X))
      (setInverseImage f) ≪≫
    Functor.isoWhiskerLeft (E ⋙ FintypeCat.incl ⋙ uliftFunctor.{u + 1})
      (setInverseImageConstantIso f)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option linter.unusedFintypeInType false in
-- Preserve the original supplied hypotheses and binder order.
theorem exists_etale_constant_action_colimit_at_geometric_point
    {X : Scheme.{u}} {K : Type u} [Field K] [IsSepClosed K]
    (s : Spec (CommRingCat.of K) ⟶ X) (D : SingleObj G ⥤ Scheme.FiniteEtale X) :
    ∃ (U : X.Etale) (q : Spec (CommRingCat.of K) ⟶ U.left), q ≫ U.hom = s ∧
      ∃ A : Type (u + 1), Finite A ∧
        Nonempty ((setInverseImage U.hom).obj (coverDiagramSheafColimit D) ≅
          (constantSheaf (Scheme.smallEtaleTopology U.left) (Type (u + 1))).obj A) := by
  obtain ⟨S, q, hq, ⟨e⟩, _⟩ := exists_etale_trivialization_at_geometric_point
    (D.obj (SingleObj.star G)) (Fiber s (D.obj (SingleObj.star G))) s (Equiv.refl _)
  let D' := D ⋙ baseChange S.hom
  obtain ⟨W, hw, ⟨ew⟩⟩ := exists_open_action_trivialization q D'
    (A := FintypeCat.of (Fiber s (D.obj (SingleObj.star G)))) e
  let U : X.Etale := Scheme.Etale.mk (W.ι ≫ S.hom)
  have hrange : Set.range q ⊆ Set.range W.ι := by
    rintro _ ⟨z, rfl⟩
    refine ⟨⟨q z, ?_⟩, rfl⟩
    rw [Subsingleton.elim z (default : Spec (CommRingCat.of K))]
    exact hw
  let qW := IsOpenImmersion.lift W.ι q hrange
  have hqW : qW ≫ U.hom = s := by
    change qW ≫ W.ι ≫ S.hom = s
    rw [← Category.assoc, IsOpenImmersion.lift_fac]
    exact hq
  let E := D' ⋙ fiberToFinite q
  refine ⟨U, qW, hqW, finiteActionOrbitType E, inferInstance, ⟨?_⟩⟩
  exact (setInverseImageComp S.hom W.ι).app (coverDiagramSheafColimit D) ≪≫
    (setInverseImage W.ι).mapIso (coverDiagramSheafColimitBaseChangeIso S.hom D) ≪≫
    coverDiagramSheafColimitBaseChangeIso W.ι D' ≪≫
    HasColimit.isoOfNatIso (Functor.isoWhiskerRight ew.symm
      (finiteCoverSectionSheafFunctor W.toScheme)) ≪≫
    HasColimit.isoOfNatIso (constantActionBaseChangeSheafIso W.ι E) ≪≫
    finiteConstantActionColimitIso W.toScheme E

set_option linter.unusedFintypeInType false in
-- Preserve the original supplied hypotheses and binder order.
/-- The actual sheaf colimit of an arbitrary finite group action is finite
locally constant. No freeness or connectedness hypothesis occurs. -/
theorem finiteActionSheafColimit_isFiniteLocallyConstant
    {X : Scheme.{u}} (D : SingleObj G ⥤ Scheme.FiniteEtale X) :
    IsFiniteLocallyConstantSet (coverDiagramSheafColimit D) := by
  classical
  have hex (x : X) := exists_etale_constant_action_colimit_at_geometric_point
    (algebraicClosureResiduePoint X x) D
  choose U q hq A hA e using hex
  exact ⟨{
    index := X
    chart := U
    covers := fun x => ⟨x, q x default,
      (congrArg (fun f : Spec (CommRingCat.of (AlgebraicClosure (X.residueField x))) ⟶ X =>
        f default) (hq x)).trans (algebraicClosureResiduePoint_image X x default)⟩
    value := A
    finite_value := hA
    trivialization := fun x => (e x).some }⟩

end AlgebraicGeometry.Scheme.FiniteEtale

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 79663373fb4ce1663836cc5952ad554c45eecd26c8b6a358173ea6a7f6f2e927.
Definitions, hypotheses and universes are retained modulo native names. -/
