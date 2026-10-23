/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.Basic
public import Aglib.AlgebraicGeometry.Sites.Etale
public import Aglib.AlgebraicGeometry.Sites.GlobalSections
public import Mathlib.Algebra.Category.Grp.Ulift

/-!
# The actual etale structure sheaf

On an etale test scheme `U`, the ring-valued sheaf has value the original
`Γ(U, ⊤)`. Its additive coefficient sheaf uses the actual native universe lift
to `AddCommGrpCat.{u+1}`, retaining the original restriction homomorphisms.
There is no characteristic, finiteness or Noetherian hypothesis.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

attribute [local instance] etaleSubcanonical

/-- The original rings of global sections on actual small-etale test schemes. -/
def structurePresheaf (X : Scheme.{u}) : X.Etaleᵒᵖ ⥤ CommRingCat.{u} :=
  (Scheme.Etale.forget X).op ⋙ (Over.forget X).op ⋙ Scheme.Γ

/-- The original global-section rings satisfy etale descent. -/
theorem structurePresheaf_isSheaf (X : Scheme.{u}) :
    Presheaf.IsSheaf (Scheme.smallEtaleTopology X) (structurePresheaf X) := by
  apply (Scheme.Etale.forget X).op_comp_isSheaf_of_isSheaf
    (Scheme.smallEtaleTopology X) (Scheme.etaleTopology.over X)
  apply (Over.forget X).op_comp_isSheaf_of_isSheaf
    (Scheme.etaleTopology.over X) Scheme.etaleTopology
  exact Scheme.globalSections_isSheaf _

/-- The actual ring-valued small-etale structure sheaf. -/
def structureSheaf (X : Scheme.{u}) :
    Sheaf (Scheme.smallEtaleTopology X) CommRingCat.{u} :=
  ⟨structurePresheaf X, structurePresheaf_isSheaf X⟩

/-- The additive groups of original sections in the standard coefficient universe. -/
def additiveStructurePresheaf (X : Scheme.{u}) : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  structurePresheaf X ⋙ forget₂ CommRingCat.{u} RingCat.{u} ⋙
    forget₂ RingCat.{u} AddCommGrpCat.{u} ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}

/-- The original additive sections, with their explicit universe lift, form a sheaf. -/
theorem additiveStructurePresheaf_isSheaf (X : Scheme.{u}) :
    Presheaf.IsSheaf (Scheme.smallEtaleTopology X) (additiveStructurePresheaf X) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _
    (CategoryTheory.forget AddCommGrpCat.{u + 1})]
  change Presheaf.IsSheaf (Scheme.smallEtaleTopology X)
    ((Scheme.Etale.forget X).op ⋙ (Over.forget X).op ⋙
      (Scheme.Γ ⋙ CategoryTheory.forget CommRingCat.{u}) ⋙ uliftFunctor.{u + 1})
  apply (Scheme.Etale.forget X).op_comp_isSheaf_of_isSheaf
    (Scheme.smallEtaleTopology X) (Scheme.etaleTopology.over X)
  apply (Over.forget X).op_comp_isSheaf_of_isSheaf
    (Scheme.etaleTopology.over X) Scheme.etaleTopology
  apply Presheaf.isSheaf_comp_of_isSheaf
  rw [isSheaf_iff_isSheaf_of_type]
  exact Scheme.globalSectionsUnderlying_isSheaf _

/-- The actual additive etale structure sheaf, usable by original `Sheaf.H`. -/
def additiveStructureSheaf (X : Scheme.{u}) : AbelianSheaf.{u, u + 1} X :=
  ⟨additiveStructurePresheaf X, additiveStructurePresheaf_isSheaf X⟩

end AlgebraicGeometry.Scheme.EtaleCohomology
