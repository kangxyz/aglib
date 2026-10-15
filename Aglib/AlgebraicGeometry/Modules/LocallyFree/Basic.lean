/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.FinitePresentation.Basic

/-!
# Finite locally free module sheaves

One family of finite local bases witnesses the canonical class. The actual
sheaf and morphisms are unchanged when passing to the full subcategory; finite
presentation follows from the same basis family.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v v' w w'
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

open scoped ZeroObject

variable (X : Scheme.{u})

/-- A finite locally free sheaf has a single local generating family which
is both a basis and finite on every member of its cover. -/
class IsFiniteLocallyFree (M : X.Modules) : Prop where
  exists_localBasis : ∃ q : SheafOfModules.LocalGeneratorsData.{u} M,
    q.IsLocallyFreeData ∧ q.IsFiniteType

/-- The property of being finite locally free. -/
abbrev finiteLocallyFree : ObjectProperty X.Modules := IsFiniteLocallyFree X

/-- The full category of finite locally free sheaves on `X`. -/
abbrev FiniteLocallyFree := (finiteLocallyFree X).FullSubcategory


variable {X}

instance finiteLocallyFree_obj (M : FiniteLocallyFree X) :
    IsFiniteLocallyFree X M.obj := M.property

instance isLocallyFree_of_finiteLocallyFree (M : X.Modules)
    [h : IsFiniteLocallyFree X M] : SheafOfModules.IsLocallyFree.{u} M := by
  obtain ⟨q, hq, _⟩ := h.exists_localBasis
  exact q.isLocallyFree

instance isFinitePresentation_of_finiteLocallyFree (M : X.Modules)
    [h : IsFiniteLocallyFree X M] : SheafOfModules.IsFinitePresentation.{u} M := by
  obtain ⟨q, hq, hf⟩ := h.exists_localBasis
  exact finitePresentation_of_localBasis q

/-- The inclusion of finite locally free sheaves among finitely presented
sheaves is justified by the local presentations with no relations. -/
theorem finiteLocallyFree_le_finitePresentation :
    finiteLocallyFree X ≤ finitePresentation X := by
  intro M hM
  exact isFinitePresentation_of_finiteLocallyFree M

/-- The fully faithful inclusion of finite locally free sheaves into sheaves
of finite presentation. -/
abbrev finiteLocallyFreeToFinitePresentation :
    FiniteLocallyFree X ⥤ FinitePresentation X :=
  ObjectProperty.ιOfLE (finiteLocallyFree_le_finitePresentation (X := X))

/-- Forgetting the local bases does not change the underlying sheaf or morphisms. -/
abbrev finiteLocallyFreeForget : FiniteLocallyFree X ⥤ X.Modules :=
  (finiteLocallyFree X).ι

/-- Both ways of forgetting a finite locally free sheaf agree. -/
theorem finiteLocallyFreeToFinitePresentation_comp_forget :
    finiteLocallyFreeToFinitePresentation (X := X) ⋙ finitePresentationForget =
      finiteLocallyFreeForget := rfl

/-- Transport the chosen local bases along an isomorphism. -/
def localBasisOfIso {M N : X.Modules} (e : M ≅ N)
    (q : SheafOfModules.LocalGeneratorsData.{u} M) :
    SheafOfModules.LocalGeneratorsData.{u} N where
  I := q.I
  X := q.X
  coversTop := q.coversTop
  generators i := (q.generators i).ofEpi (e.hom.over (q.X i))

instance localBasisOfIso_isLocallyFreeData {M N : X.Modules} (e : M ≅ N)
    (q : SheafOfModules.LocalGeneratorsData.{u} M) [q.IsLocallyFreeData] :
    (localBasisOfIso e q).IsLocallyFreeData where
  isIso i := by
    dsimp [localBasisOfIso]
    infer_instance

instance localBasisOfIso_isFiniteType {M N : X.Modules} (e : M ≅ N)
    (q : SheafOfModules.LocalGeneratorsData.{u} M) [hq : q.IsFiniteType] :
    (localBasisOfIso e q).IsFiniteType where
  isFiniteType i := ⟨(hq.isFiniteType i).finite⟩

/-- Finite local freeness is invariant under isomorphism. -/
theorem finiteLocallyFree_of_iso {M N : X.Modules} (e : M ≅ N)
    [h : IsFiniteLocallyFree X M] : IsFiniteLocallyFree X N := by
  obtain ⟨q, hq, hf⟩ := h.exists_localBasis
  exact ⟨localBasisOfIso e q, inferInstance, inferInstance⟩

instance finiteLocallyFree_closedUnderIsomorphisms :
    (finiteLocallyFree X).IsClosedUnderIsomorphisms where
  of_iso e _h := finiteLocallyFree_of_iso e

/-- Finite local freeness is equivalent for isomorphic sheaves. -/
theorem finiteLocallyFree_iff_of_iso {M N : X.Modules} (e : M ≅ N) :
    finiteLocallyFree X M ↔ finiteLocallyFree X N :=
  (finiteLocallyFree X).prop_iff_of_iso e

instance finiteLocallyFree_free (I : Type u) [Finite I] :
    IsFiniteLocallyFree X (SheafOfModules.free (R := X.ringCatSheaf) I) := by
  let q := (SheafOfModules.free.generatingSections (R := X.ringCatSheaf) I).localGeneratorsData
  refine ⟨q, inferInstance, ?_⟩
  constructor
  intro i
  constructor
  change Finite I
  infer_instance

/-- Every zero scheme module is finite locally free, of rank zero. -/
theorem finiteLocallyFree_of_isZero {M : X.Modules} (hM : IsZero M) :
    IsFiniteLocallyFree X M :=
  finiteLocallyFree_of_iso ((isZero_free_empty (X := X)).iso hM)

instance finiteLocallyFree_zero : IsFiniteLocallyFree X (0 : X.Modules) :=
  finiteLocallyFree_of_isZero (isZero_zero _)

instance finiteLocallyFree_containsZero : (finiteLocallyFree X).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, inferInstance⟩

/-- The finite free sheaf of a specified rank, as a finite locally free object. -/
def finiteFree (n : ℕ) : FiniteLocallyFree X :=
  ⟨SheafOfModules.free (R := X.ringCatSheaf) (ULift (Fin n)), inferInstance⟩

/-- The finite locally free object associated to a sheaf equipped with finite local bases. -/
def ofFiniteLocallyFree (M : X.Modules) [IsFiniteLocallyFree X M] :
    FiniteLocallyFree X := ⟨M, inferInstance⟩

end AlgebraicGeometry.Scheme.Modules
