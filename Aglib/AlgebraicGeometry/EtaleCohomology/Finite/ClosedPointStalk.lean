/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ComponentSections
public import Mathlib.Algebra.Category.Grp.FilteredColimits

/-! # Original germs at the closed point of a strictly local scheme -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite

universe u

variable (B : Type u) [CommRing B] [HenselianLocalRing B]
  [IsSepClosed (IsLocalRing.ResidueField B)]

/-- The original geometric point given by the native separably closed residue field. -/
abbrev closedPoint := pointSmallEtale (LocalRing.residueSpecMap B)

/-- The actual residue point of the identity etale object. -/
def closedTerminalPoint : (closedPoint B).fiber.obj (StrictlyLocal.terminalObject B) :=
  Over.homMk (LocalRing.residueSpecMap B) (Category.comp_id _)

/-- Every residue-pointed neighborhood admits a section preserving that point. -/
theorem exists_pointed_section (U : (Spec (.of B)).Etale)
    (t : (closedPoint B).fiber.obj U) :
    ∃ s : StrictlyLocal.terminalObject B ⟶ U,
      (closedPoint B).fiber.map s (closedTerminalPoint B) = t := by
  obtain ⟨t, ht, rfl⟩ := Over.homMk_surjective t
  have : Etale U.hom := U.prop
  obtain ⟨σ, hσ, hred⟩ := StrictlyLocal.exists_section_lift_of_residue_point B U.hom t ht
  let s : StrictlyLocal.terminalObject B ⟶ U := MorphismProperty.Over.homMk σ hσ
  refine ⟨s, ?_⟩
  apply Over.OverMorphism.ext
  exact hred

/-- The original germ at the closed point is bijective for any abelian-valued
presheaf. In particular, no locally constant coefficient hypothesis is used. -/
theorem closedPoint_germ_bijective
    (P : (Spec (.of B)).Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    Function.Bijective ((closedPoint B).toPresheafFiber
      (StrictlyLocal.terminalObject B) (closedTerminalPoint B) P) := by
  let : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} _
  constructor
  · intro a b hab
    obtain ⟨U, f, t, _, h⟩ := ((closedPoint B).toPresheafFiber_eq_iff'
      (StrictlyLocal.terminalObject B) (closedTerminalPoint B) a b).mp hab
    obtain ⟨s, _⟩ := exists_pointed_section B U t
    have hsf : s ≫ f = 𝟙 _ := (StrictlyLocal.terminalIsTerminal B).hom_ext _ _
    have hm : P.map f.op ≫ P.map s.op = 𝟙 _ := by
      rw [← P.map_comp, ← op_comp, hsf, op_id, P.map_id]
    have hval (z : P.obj (op (StrictlyLocal.terminalObject B))) :
        P.map s.op (P.map f.op z) = z := ConcreteCategory.congr_hom hm z
    exact (hval a).symm.trans ((congrArg (fun z => P.map s.op z) h).trans (hval b))
  · intro z
    obtain ⟨U, t, a, rfl⟩ := (closedPoint B).toPresheafFiber_jointly_surjective z
    obtain ⟨s, hs⟩ := exists_pointed_section B U t
    refine ⟨P.map s.op a, ?_⟩
    have h := (closedPoint B).toPresheafFiber_w s (closedTerminalPoint B) P
    rw [hs] at h
    exact ConcreteCategory.congr_hom h a

/-- The literal original closed-point germ is an isomorphism. -/
theorem closedPoint_germ_isIso
    (P : (Spec (.of B)).Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    IsIso ((closedPoint B).toPresheafFiber
      (StrictlyLocal.terminalObject B) (closedTerminalPoint B) P) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr (closedPoint_germ_bijective B P)

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
