/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ClosedPointStalk

/-! # Original ambient germs on strictly local open components -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite

universe u

variable {X : Scheme.{u}} (B : Type u) [CommRing B] [HenselianLocalRing B]
  [IsSepClosed (IsLocalRing.ResidueField B)] (p : Spec (.of B) ⟶ X)

omit [IsSepClosed (IsLocalRing.ResidueField B)] in
/-- A specified residue-field lift to an étale scheme extends over a strictly
local scheme, for an arbitrary map from that scheme to the base. -/
theorem exists_strictLocal_pointed_lift {Y : Scheme.{u}} (f : Y ⟶ X) [Etale f]
    (t : Spec (.of (IsLocalRing.ResidueField B)) ⟶ Y)
    (ht : t ≫ f = LocalRing.residueSpecMap B ≫ p) :
    ∃ s : Spec (.of B) ⟶ Y,
      s ≫ f = p ∧ LocalRing.residueSpecMap B ≫ s = t := by
  let t' : Spec (.of (IsLocalRing.ResidueField B)) ⟶ pullback f p :=
    pullback.lift t (LocalRing.residueSpecMap B) ht
  obtain ⟨σ, hσ, hred⟩ := StrictlyLocal.exists_section_lift_of_residue_point B
    (pullback.snd f p) t' (pullback.lift_snd _ _ _)
  refine ⟨σ ≫ pullback.fst f p, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hσ, Category.id_comp]
  · exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ pullback.fst f p) hred).trans
        (pullback.lift_fst _ _ _))

variable [IsOpenImmersion p]

/-- The original ambient point determined by the component's native residue field. -/
abbrev openComponentPoint := pointSmallEtale (LocalRing.residueSpecMap B ≫ p)

/-- The actual point of the strict local open object in the ambient site. -/
def openComponentFiberPoint : (openComponentPoint B p).fiber.obj (Scheme.Etale.mk p) :=
  Over.homMk (LocalRing.residueSpecMap B) rfl

/-- An ambient geometric neighborhood admits a map from the component,
preserving its specified residue point. -/
theorem exists_openComponent_pointed_map (U : X.Etale)
    (t : (openComponentPoint B p).fiber.obj U) :
    ∃ s : Scheme.Etale.mk p ⟶ U,
      (openComponentPoint B p).fiber.map s (openComponentFiberPoint B p) = t := by
  obtain ⟨t, ht, rfl⟩ := Over.homMk_surjective t
  have : Etale U.hom := U.prop
  obtain ⟨s, hs, hred⟩ := exists_strictLocal_pointed_lift B p U.hom t ht
  let s' : Scheme.Etale.mk p ⟶ U := MorphismProperty.Over.homMk s hs
  refine ⟨s', ?_⟩
  apply Over.OverMorphism.ext
  exact hred

/-- The literal original ambient germ at an open strict local component is
bijective for every abelian-valued presheaf. -/
theorem openComponent_germ_bijective (P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    Function.Bijective ((openComponentPoint B p).toPresheafFiber
      (Scheme.Etale.mk p) (openComponentFiberPoint B p) P) := by
  have hT : IsSubterminal (Scheme.Etale.mk p) := by
    intro Z f g
    apply MorphismProperty.Over.Hom.ext
    apply (cancel_mono p).mp
    exact f.w.trans g.w.symm
  exact (ConcreteCategory.isIso_iff_bijective _).mp
    ((openComponentPoint B p).isIso_toPresheafFiber_of_subterminal
      (Scheme.Etale.mk p) (openComponentFiberPoint B p) hT
      (exists_openComponent_pointed_map B p) P)

/-- The literal ambient germ is an isomorphism, with no coefficient replacement. -/
theorem openComponent_germ_isIso (P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    IsIso ((openComponentPoint B p).toPresheafFiber
      (Scheme.Etale.mk p) (openComponentFiberPoint B p) P) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr (openComponent_germ_bijective B p P)

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
