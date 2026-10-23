/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H0.ProperHenselian.Sections
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.ConstantFinite.Basic
public import Aglib.AlgebraicGeometry.EtaleCohomology.Pullback
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.ProperHenselian.General

/-! # Finite constant H0 over a proper henselian local base -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u w w'

attribute [local instance] hasSheafifyLarge

namespace ProperHenselianH0

variable {X S : Scheme.{u}} (f : S ⟶ X)

/-- Full faithfulness gives actual section bijectivity for the displayed finite representation. -/
theorem globalSectionsPullback_bijective_of_representation
    [(Scheme.FiniteEtale.baseChange f).Full]
    [(Scheme.FiniteEtale.baseChange f).Faithful]
    (L : AbelianSheaf.{u, u + 1} X) (D : CoefficientRepresentation L) :
    Function.Bijective (globalSectionsPullback f L) := by
  have hD := represented_globalSectionsPullback_bijective f D.group
  have : Mono (globalSectionsPullback f (representedSheaf D.group)) :=
    (AddCommGrpCat.mono_iff_injective _).mpr hD.injective
  have : Epi (globalSectionsPullback f (representedSheaf D.group)) :=
    (AddCommGrpCat.epi_iff_surjective _).mpr hD.surjective
  have h : IsIso (globalSectionsPullback f (representedSheaf D.group)) :=
    isIso_of_mono_of_epi _
  have heq : globalSectionsPullback f L =
      (globalSections X).map D.iso.inv ≫
        globalSectionsPullback f (representedSheaf D.group) ≫
          (globalSections S).map ((inverseImage f).map D.iso.hom) := by
    rw [← globalSectionsPullback_naturality, ← Category.assoc, ← Functor.map_comp,
      D.iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  have : IsIso (globalSectionsPullback f L) := by
    rw [heq]
    infer_instance
  exact (asIso (globalSectionsPullback f L)).addCommGroupIsoToAddEquiv.bijective

/-- Full faithfulness of finite-cover restriction gives actual section
bijectivity for every finite locally constant abelian sheaf. -/
theorem globalSectionsPullback_bijective_of_full_faithful
    [(Scheme.FiniteEtale.baseChange f).Full]
    [(Scheme.FiniteEtale.baseChange f).Faithful]
    (L : AbelianSheaf.{u, u + 1} X) (hL : IsFiniteLocallyConstant L) :
    Function.Bijective (globalSectionsPullback f L) :=
  globalSectionsPullback_bijective_of_representation f L
    (CoefficientRepresentation.ofFiniteLocallyConstant L (stacks03RV X) hL)

variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)]

/-- The original degree-zero Ext map is bijective whenever its actual
global-section pullback is bijective. -/
theorem h0Pullback_bijective_of_sections (L : AbelianSheaf.{u, u + 1} X)
    (h : Function.Bijective (globalSectionsPullback f L)) :
    Function.Bijective (h0Pullback f L) := by
  constructor
  · intro a b hab
    apply (Sheaf.H.equiv₀ L (etaleTerminalIsTerminal X)).injective
    apply h.injective
    rw [← h0Pullback_equiv₀, ← h0Pullback_equiv₀, hab]
  · intro b
    obtain ⟨a, ha⟩ := h.surjective
      (Sheaf.H.equiv₀ ((inverseImage f).obj L) (etaleTerminalIsTerminal S) b)
    refine ⟨(Sheaf.H.equiv₀ L (etaleTerminalIsTerminal X)).symm a, ?_⟩
    apply (Sheaf.H.equiv₀ ((inverseImage f).obj L) (etaleTerminalIsTerminal S)).injective
    rw [h0Pullback_equiv₀, AddEquiv.apply_symm_apply, ha]

end ProperHenselianH0

namespace ConstantFinite

variable (A : Type u) [AddCommGroup A]
  {X S : Scheme.{u}} (f : S ⟶ X)

/-- Original pullback of sections followed by the canonical constant-coefficient transport. -/
def pullbackSections : (globalSections X).obj (coefficient A X) ⟶
    (globalSections S).obj (coefficient A S) :=
  globalSectionsPullback f (coefficient A X) ≫
    (globalSections S).map ((inverseImageConstantIso f).app (value A)).hom

variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)]

/-- The actual original H0 map with the canonical inverse-image constant identification. -/
def pullbackH0 : Sheaf.H.{w} (coefficient A X) 0 →+
    Sheaf.H.{w'} (coefficient A S) 0 :=
  (Sheaf.H.map ((inverseImageConstantIso f).app (value A)).hom 0).comp
    (h0Pullback f (coefficient A X))

/-- The coefficient transport in finite constant H0 remains the literal native map. -/
theorem pullbackH0_apply (c : Sheaf.H.{w} (coefficient A X) 0) :
    pullbackH0 A f c = Sheaf.H.map ((inverseImageConstantIso f).app (value A)).hom 0
      (h0Pullback f (coefficient A X) c) := rfl

end ConstantFinite

section ProperLocal

variable {R : Type u} [CommRing R] [HenselianLocalRing R]
  {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) [IsProper p]

/-- Actual finite locally constant sections over a proper henselian local
base restrict bijectively to the original closed residue fibre. -/
theorem properHenselian_globalSectionsPullback_bijective
    (L : AbelianSheaf.{u, u + 1} X) (hL : IsFiniteLocallyConstant L) :
    Function.Bijective
      (globalSectionsPullback (pullback.fst p (LocalRing.residueSpecMap R)) L) := by
  let := Scheme.FiniteEtale.properHenselian_baseChange_isEquivalence p
  exact ProperHenselianH0.globalSectionsPullback_bijective_of_full_faithful _ L hL

namespace ConstantFinite

variable (A : Type u) [AddCommGroup A] [Finite A]

/-- Actual constant sections restrict bijectively by full faithfulness on the literal cover. -/
theorem properHenselian_originalSections_bijective :
    Function.Bijective (globalSectionsPullback
      (pullback.fst p (LocalRing.residueSpecMap R)) (coefficient A X)) := by
  let := Scheme.FiniteEtale.properHenselian_baseChange_isEquivalence p
  exact ProperHenselianH0.globalSectionsPullback_bijective_of_representation _ _
    (representation A X)

/-- Finite constant sections have an actual closed-residue restriction bijection. -/
theorem properHenselian_pullbackSections_bijective :
    Function.Bijective
      (pullbackSections A (pullback.fst p (LocalRing.residueSpecMap R))) := by
  have h := properHenselian_originalSections_bijective p A
  exact ((globalSections _).mapIso
    ((inverseImageConstantIso (pullback.fst p (LocalRing.residueSpecMap R))).app
      (value A))).addCommGroupIsoToAddEquiv.bijective.comp h

variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{w'} (AbelianSheaf.{u, u + 1}
    (pullback p (LocalRing.residueSpecMap R)))]

/-- Original finite constant H0 restricts bijectively to the closed residue
fibre over every henselian local ring, with both Ext universes displayed. -/
theorem properHenselian_pullbackH0_bijective :
    Function.Bijective
      (pullbackH0 A (pullback.fst p (LocalRing.residueSpecMap R))) := by
  let f := pullback.fst p (LocalRing.residueSpecMap R)
  have h := ProperHenselianH0.h0Pullback_bijective_of_sections f (coefficient A X)
    (properHenselian_originalSections_bijective p A)
  have he : Function.Bijective
      (Sheaf.H.map ((inverseImageConstantIso f).app (value A)).hom 0) := by
    refine ⟨?_, ?_⟩
    · intro a b hab
      have h' := congrArg (Sheaf.H.map ((inverseImageConstantIso f).app (value A)).inv 0) hab
      simpa only [← Sheaf.H.map_comp_apply, Iso.hom_inv_id, Sheaf.H.map_id_apply] using h'
    · intro a
      refine ⟨Sheaf.H.map ((inverseImageConstantIso f).app (value A)).inv 0 a, ?_⟩
      rw [← Sheaf.H.map_comp_apply, Iso.inv_hom_id, Sheaf.H.map_id_apply]
  exact he.comp h

end ConstantFinite
end ProperLocal
end AlgebraicGeometry.Scheme.EtaleCohomology
