/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.ShortComplex.MapHomology.Components
public import Mathlib.Algebra.Homology.SingleHomology

/-!
# The original degree-zero homology embedding

For a cochain complex indexed by the natural numbers, the original homology
in degree zero embeds canonically into its degree-zero term. The embedding
commutes with complex maps and with the native homology comparison for an
exact additive functor. An actual augmentation retains its degree-zero
component under this embedding.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CochainComplex

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]

/-- The canonical embedding of actual degree-zero homology in the original zero term. -/
def homologyZeroι (K : CochainComplex C ℕ) : K.homology 0 ⟶ K.X 0 :=
  K.homologyι 0 ≫ inv (K.pOpcycles 0)

instance homologyZeroι_mono (K : CochainComplex C ℕ) : Mono (homologyZeroι K) := by
  unfold homologyZeroι
  infer_instance

/-- The original cycle quotient followed by the canonical zero-degree embedding is exactly
its original inclusion into the zero term. -/
@[reassoc (attr := simp)]
theorem homologyπ_homologyZeroι (K : CochainComplex C ℕ) :
    K.homologyπ 0 ≫ homologyZeroι K = K.iCycles 0 := by
  dsimp only [homologyZeroι]
  rw [← Category.assoc, HomologicalComplex.homology_π_ι]
  simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- The canonical zero-degree embedding retains the original component of a complex map. -/
@[reassoc]
theorem homologyZeroι_naturality {K L : CochainComplex C ℕ} (f : K ⟶ L) :
    homologyMap f 0 ≫ homologyZeroι L = homologyZeroι K ≫ f.f 0 := by
  dsimp only [homologyZeroι]
  rw [← Category.assoc, homologyι_naturality]
  simp only [Category.assoc]
  apply congrArg (fun t : K.opcycles 0 ⟶ L.X 0 => K.homologyι 0 ≫ t)
  apply (cancel_mono (L.pOpcycles 0)).mp
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← p_opcyclesMap, IsIso.inv_hom_id_assoc]

/-- The canonical homology of a single is the identity under the original zero embedding. -/
@[reassoc]
theorem singleObjHomologySelfIso_inv_homologyZeroι (A : C) :
    (singleObjHomologySelfIso (.up ℕ) 0 A).inv ≫
      homologyZeroι ((single₀ C).obj A) = 𝟙 A := by
  dsimp only [homologyZeroι]
  rw [← Category.assoc, singleObjHomologySelfIso_inv_homologyι]
  simp only [singleObjOpcyclesSelfIso_hom, Category.assoc,
    IsIso.hom_inv_id, Category.comp_id]
  rfl

/-- The actual augmentation maps to its original degree-zero component. -/
@[reassoc]
theorem augmentation_homologyZeroι {A : C} {K : CochainComplex C ℕ}
    (a : (single₀ C).obj A ⟶ K) :
    (singleObjHomologySelfIso (.up ℕ) 0 A).inv ≫ homologyMap a 0 ≫
        homologyZeroι K = a.f 0 := by
  rw [homologyZeroι_naturality, ← Category.assoc,
    singleObjHomologySelfIso_inv_homologyZeroι, Category.id_comp]

/-- Exact additive functors preserve the original embedding, through the native comparison. -/
@[reassoc]
theorem mapHomologyIso_hom_homologyZeroι (F : C ⥤ D) [F.Additive]
    [F.PreservesHomology] (K : CochainComplex C ℕ) :
    ((K.sc 0).mapHomologyIso F).hom ≫ F.map (homologyZeroι K) =
      homologyZeroι ((F.mapHomologicalComplex (.up ℕ)).obj K) := by
  dsimp only [homologyZeroι]
  rw [F.map_comp, ← Category.assoc]
  erw [ShortComplex.mapHomologyIso_hom_homologyι]
  rw [Category.assoc]
  congr 1
  apply (cancel_epi (((F.mapHomologicalComplex (.up ℕ)).obj K).pOpcycles 0)).mp
  have hp := ShortComplex.map_pOpcycles_mapOpcyclesIso_inv F (K.sc 0)
  change F.map (K.pOpcycles 0) ≫ ((K.sc 0).mapOpcyclesIso F).inv =
    ((F.mapHomologicalComplex (.up ℕ)).obj K).pOpcycles 0 at hp
  rw [IsIso.hom_inv_id, ← hp]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, ← F.map_comp,
    IsIso.hom_inv_id, F.map_id]
  rfl

end CochainComplex
