/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Proper.AffineStein.Basic
public import Aglib.AlgebraicGeometry.Cohomology.Proper.Finiteness
public import Aglib.AlgebraicGeometry.Cohomology.Proper.StructureSheaf.Coefficient
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# The actual affine Stein factor of a proper morphism

The ring is the original section ring on the actual inverse image of an affine
target open. Its structural coefficient map is finite by proper coherent H⁰
finiteness. The original affinization map preserves the actual structure sheaf
by the native qcqs localization theorem on the principal-open basis.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open AlgebraicGeometry.Scheme.Cohomology

universe u

namespace AlgebraicGeometry.Scheme

namespace AffineStein

/-- Proper H⁰ finiteness applies to the literal structural coefficient ring map. -/
theorem finite_structuralCoefficients
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {W : Scheme.{u}} (p : W ⟶ Spec (CommRingCat.of R)) [IsProper p] :
    (p.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom).Finite := by
  let α := p.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let O : W.Modules := SheafOfModules.unit W.ringCatSheaf
  let := α.toAlgebra
  let := moduleCohomologyModuleOfHom W α O 0
  let : Module.Finite R (Sheaf.H.{u + 1} (moduleAddSheaf W O) 0) :=
    moduleCohomology_finite_of_proper R p O (affineLocallyFiniteType_unit W) 0
  exact Module.Finite.equiv (moduleH0EquivOfHom W α O)

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) (hV : IsAffineOpen V)

include hV in
/-- The actual original affine-open coefficient map is finite under properness. -/
theorem finite_coefficient [IsLocallyNoetherian Y] [IsProper f] : (f.app V).hom.Finite := by
  let : IsAffine V.toScheme := hV
  let : IsNoetherianRing Γ(Y, V) :=
    IsLocallyNoetherian.component_noetherian (X := Y) ⟨V, hV⟩
  let p := (f ∣_ V) ≫ V.toSpecΓ
  have : IsProper p := by
    change IsProper ((f ∣_ V) ≫ hV.isoSpec.hom)
    infer_instance
  have hb := finite_structuralCoefficients Γ(Y, V) p
  have hs : ((Scheme.ΓSpecIso Γ(Y, V)).inv ≫ p.appTop) ≫
      (f ⁻¹ᵁ V).topIso.hom = f.app V := by
    rw [structuralCoefficient_square f V, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  have hi : (f ⁻¹ᵁ V).topIso.hom.hom.Finite :=
    RingHom.Finite.of_surjective _
      (f ⁻¹ᵁ V).topIso.commRingCatIsoToRingEquiv.surjective
  have hc := hi.comp hb
  change (((Scheme.ΓSpecIso Γ(Y, V)).inv ≫ p.appTop) ≫
    (f ⁻¹ᵁ V).topIso.hom).hom.Finite at hc
  rw [hs] at hc
  exact hc

/-- The actual second map of the affine factor is finite. -/
instance finiteMap_isFinite [IsLocallyNoetherian Y] [IsProper f] :
    IsFinite (finiteMap f V hV) := by
  let : IsFinite (Spec.map (f.app V)) :=
    (IsFinite.SpecMap_iff (f.app V)).mpr (finite_coefficient f V hV)
  dsimp only [finiteMap]
  infer_instance

include hV in
/-- The first map is proper, by the actual factorization and separatedness of the second. -/
theorem first_isProper [IsLocallyNoetherian Y] [IsProper f] :
    IsProper (first f V) := by
  have : IsProper (first f V ≫ finiteMap f V hV) := by
    rw [factorization]
    infer_instance
  exact IsProper.of_comp (first f V) (finiteMap f V hV)

end AffineStein

end AlgebraicGeometry.Scheme
