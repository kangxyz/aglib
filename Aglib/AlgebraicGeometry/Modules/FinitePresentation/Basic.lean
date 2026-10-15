/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero

/-!
# Finite presentations of actual scheme module sheaves

The predicates and presentation data are Mathlib objects. These wrappers and
transport lemmas work on arbitrary schemes, independently of coherent or
finite locally free categories.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v v' w w'
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

open scoped ZeroObject

section Presentation

variable {C : Type w} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {D : Type w'} [Category.{v'} D] {K : GrothendieckTopology D}
  {S : Sheaf K RingCat.{u}} [HasSheafify K AddCommGrpCat.{u}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Transporting generating sections by an isomorphism preserves the basis condition. -/
instance generatingSections_ofEpi_isIso {M N : SheafOfModules.{u} R}
    (G : M.GeneratingSections) (f : M ⟶ N) [IsIso f] [IsIso G.π] :
    IsIso (G.ofEpi f).π := by
  rw [SheafOfModules.GeneratingSections.ofEpi_π]
  infer_instance

/-- A colimit-preserving functor which preserves the unit carries finite
presentations to finite presentations: the generator and relation index sets
are unchanged. -/
instance finitePresentation_map_isFinite {M : SheafOfModules.{u} R}
    (P : M.Presentation) [P.IsFinite]
    (F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S)
    [PreservesColimitsOfSize.{u, u} F]
    (η : SheafOfModules.unit S ≅ F.obj (SheafOfModules.unit R)) :
    (P.map F η).IsFinite where
  isFiniteType_generators := by
    constructor
    change Finite P.generators.I
    infer_instance
  isFiniteType_relations := by
    constructor
    change Finite P.relations.I
    infer_instance

end Presentation

variable (X : Scheme.{u})

instance hasSheafifyOver :
    ∀ U : TopologicalSpace.Opens X,
      HasSheafify ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u} :=
  fun _ => inferInstance

instance hasWeakSheafifyOver :
    ∀ U : TopologicalSpace.Opens X,
      HasWeakSheafify ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u} :=
  fun U => (hasSheafifyOver X U).isRightAdjoint

instance wEqualsLocallyBijectiveOver :
    ∀ U : TopologicalSpace.Opens X,
      ((Opens.grothendieckTopology X).over U).WEqualsLocallyBijective
        AddCommGrpCat.{u} :=
  fun _ => inferInstance


/-- Sheaves admitting finite local presentations on the Zariski site of `X`. -/
abbrev finitePresentation : ObjectProperty X.Modules :=
  SheafOfModules.isFinitePresentation X.ringCatSheaf

/-- The full category of sheaves of modules of finite presentation on `X`. -/
abbrev FinitePresentation := (finitePresentation X).FullSubcategory


variable {X}

instance finitePresentation_obj (M : FinitePresentation X) :
    SheafOfModules.IsFinitePresentation.{u} M.obj := M.property

/-- A finite global presentation gives a finite presentation on the Zariski site. -/
theorem finitePresentation_of_presentation {M : X.Modules}
    (P : SheafOfModules.Presentation M) [P.IsFinite] : finitePresentation X M := by
  refine SheafOfModules.IsFinitePresentation.mk (M := M) ⟨P.quasicoherentData, ?_⟩
  constructor
  intro U
  dsimp [SheafOfModules.Presentation.quasicoherentData]
  infer_instance

/-- A finite local basis presents the sheaf with an empty family of relations. -/
theorem finitePresentation_of_localBasis {M : X.Modules}
    (q : SheafOfModules.LocalGeneratorsData.{u} M)
    [q.IsLocallyFreeData] [hq : q.IsFiniteType] :
    SheafOfModules.IsFinitePresentation.{u} M := by
  refine SheafOfModules.IsFinitePresentation.mk (M := M) ⟨q.quasiCoherentData, ?_⟩
  constructor
  intro i
  constructor
  · exact hq.isFiniteType i
  · constructor
    change Finite (ULift Empty)
    infer_instance

instance isQuasicoherent_of_finitePresentation (M : X.Modules)
    [SheafOfModules.IsFinitePresentation.{u} M] :
    SheafOfModules.IsQuasicoherent.{u} M :=
  SheafOfModules.instIsQuasicoherentOfIsFinitePresentation M

/-- Forgetting the finiteness condition does not change the underlying sheaf
or any morphisms. -/
abbrev finitePresentationForget : FinitePresentation X ⥤ X.Modules :=
  (finitePresentation X).ι

/-- Finite presentation is invariant under isomorphism of scheme modules. -/
theorem finitePresentation_iff_of_iso {M N : X.Modules} (e : M ≅ N) :
    finitePresentation X M ↔ finitePresentation X N :=
  (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_iff_of_iso e

instance finitePresentation_closedUnderIsomorphisms :
    (finitePresentation X).IsClosedUnderIsomorphisms where
  of_iso e h := (finitePresentation_iff_of_iso e).mp h

/-- A free sheaf on a finite index set admits a finite local presentation. -/
theorem finitePresentation_free (I : Type u) [Finite I] :
    finitePresentation X (SheafOfModules.free (R := X.ringCatSheaf) I) :=
  by
    let q := (SheafOfModules.free.generatingSections (R := X.ringCatSheaf) I).localGeneratorsData
    have : q.IsFiniteType := by
      constructor
      intro i
      constructor
      change Finite I
      infer_instance
    exact finitePresentation_of_localBasis q

/-- The free sheaf on the empty set is a zero sheaf. -/
theorem isZero_free_empty :
    IsZero (SheafOfModules.free (R := X.ringCatSheaf) (ULift Empty)) := by
  apply (IsZero.iff_id_eq_zero _).2
  apply (SheafOfModules.freeHomEquiv _).injective
  funext i
  exact i.down.elim

instance finitePresentation_containsZero : (finitePresentation X).ContainsZero where
  exists_zero := ⟨_, isZero_free_empty, finitePresentation_free (ULift Empty)⟩

/-- In particular every zero module admits a finite local presentation. -/
theorem finitePresentation_of_isZero {M : X.Modules} (hM : IsZero M) :
    finitePresentation X M := (finitePresentation X).prop_of_isZero hM

/-- The finitely presented object associated to a sheaf with finite presentations. -/
def ofFinitePresentation (M : X.Modules) [SheafOfModules.IsFinitePresentation.{u} M] :
    FinitePresentation X := ⟨M, inferInstance⟩

end AlgebraicGeometry.Scheme.Modules
