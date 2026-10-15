/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.ComplexContraction
public import Aglib.AlgebraicGeometry.Cohomology.Godement.Tensor
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.PlusQuasiIso
public import Aglib.CategoryTheory.NatTrans.Unit

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/ProjectiveLine/OriginalLineGodementContractions.lean`
at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: cut_general;
source ranges [[28, 149]]. Actual objects, maps and hypotheses are preserved.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Plus
open CategoryTheory.NatTrans

namespace AlgebraicGeometry.Scheme.Modules.Godement

/-- Apply `F`, tensor on the left by `E`, and take the Godement total complex. -/
def godementContractionPlain (X : Scheme.{u}) (F : X.Modules ⥤ X.Modules)
    [F.Additive] (E : X.Modules) :
    CochainComplex.Plus X.Modules ⥤ CochainComplex.Plus X.Modules :=
  (F.mapCochainComplexPlus ⋙
    (moduleTensorLeftFunctor X E).mapCochainComplexPlus) ⋙ godementTotalPlus X

/-- Apply `F`, take the Godement total complex, tensor on the left by `E`, and totalize again. -/
def godementContractionResolved (X : Scheme.{u}) (F : X.Modules ⥤ X.Modules)
    [F.Additive] (E : X.Modules) :
    CochainComplex.Plus X.Modules ⥤ CochainComplex.Plus X.Modules :=
  ((F.mapCochainComplexPlus ⋙ godementTotalPlus X) ⋙
    (moduleTensorLeftFunctor X E).mapCochainComplexPlus) ⋙ godementTotalPlus X

/-- The supplied contraction of `F` followed by tensoring with `E` identifies the plain
contraction functor with Godement totalization. -/
def godementContractionPlainIso {X : Scheme.{u}} (F : X.Modules ⥤ X.Modules)
    [F.Additive] (E : X.Modules) (e : F ⋙ moduleTensorLeftFunctor X E ≅ 𝟭 X.Modules) :
    godementContractionPlain X F E ≅ godementTotalPlus X :=
  Functor.isoWhiskerRight (plusContractionIso F (moduleTensorLeftFunctor X E) e)
      (godementTotalPlus X) ≪≫ Functor.leftUnitor (godementTotalPlus X)

/-- The Godement total unit evaluated after applying `F` to bounded-below complexes. -/
def godementContractionInputUnit (X : Scheme.{u}) (F : X.Modules ⥤ X.Modules)
    [F.Additive] : F.mapCochainComplexPlus ⟶ F.mapCochainComplexPlus ⋙ godementTotalPlus X :=
  CategoryTheory.NatTrans.unitPrecompose (godementTotalPlus X) F.mapCochainComplexPlus
    (godementTotalPlusUnit X)

theorem godementContractionInputUnit_quasiIso {X : Scheme.{u}}
    (F : X.Modules ⥤ X.Modules) [F.Additive] (K : CochainComplex.Plus X.Modules) :
    QuasiIso ((godementContractionInputUnit X F).app K).hom :=
  Plus.unitPrecompose_quasiIso _ _ _ (godementTotalPlusUnit_quasiIso X) K

/-- The Godement input unit followed by tensoring on the left by `E`, before final totalization. -/
def godementContractionPreTotalMap (X : Scheme.{u}) (F : X.Modules ⥤ X.Modules)
    [F.Additive] (E : X.Modules) :
    F.mapCochainComplexPlus ⋙ (moduleTensorLeftFunctor X E).mapCochainComplexPlus ⟶
      (F.mapCochainComplexPlus ⋙ godementTotalPlus X) ⋙
        (moduleTensorLeftFunctor X E).mapCochainComplexPlus :=
  Functor.whiskerRight (godementContractionInputUnit X F)
    (moduleTensorLeftFunctor X E).mapCochainComplexPlus

theorem godementContractionPreTotalMap_quasiIso {X : Scheme.{u}}
    (F : X.Modules ⥤ X.Modules) [F.Additive] (E : X.Modules)
    [IsFiniteLocallyFree X E] (K : CochainComplex.Plus X.Modules) :
    QuasiIso ((godementContractionPreTotalMap X F E).app K).hom :=
  Plus.plus_nattrans_postcompose_quasiIso _ _ (godementContractionInputUnit_quasiIso F)
    (fun f hf => by
      let := hf
      exact exactPlus_map_quasiIso _ f) K

/-- The comparison from plain to resolved contraction obtained by Godement totalization of the
pre-total map. -/
def godementContractionInsertion (X : Scheme.{u}) (F : X.Modules ⥤ X.Modules)
    [F.Additive] (E : X.Modules) :
    godementContractionPlain X F E ⟶ godementContractionResolved X F E :=
  Functor.whiskerRight (godementContractionPreTotalMap X F E) (godementTotalPlus X)

/- Archive proof transport from
`Quillen/AlgebraicGeometry/Scheme/ProjectiveLine/OriginalLineGodementContractions.lean`,
lines 85–114, source SHA256
`40238a98b43990ae0088d12ec950af27665b095365d6998b3177e82f31540c1b`. -/
private theorem postcompose_quasiIso_of_eq
    {X : Scheme.{u}} {D : Type*} [Category D]
    {F G : D ⥤ CochainComplex.Plus X.Modules} (α : F ⟶ G)
    (T : CochainComplex.Plus X.Modules ⥤ CochainComplex.Plus X.Modules)
    (β : F ⋙ T ⟶ G ⋙ T) (hβ : β = Functor.whiskerRight α T)
    (hα : ∀ K, QuasiIso (α.app K).hom)
    (hT : ∀ {K C : CochainComplex.Plus X.Modules} (f : K ⟶ C),
      QuasiIso f.hom → QuasiIso (T.map f).hom) (K : D) :
    QuasiIso (β.app K).hom := by
  subst β
  exact Plus.plus_nattrans_postcompose_quasiIso α T hα hT K

-- This intentionally reflexive certificate fixes the functor endpoints before specializing
-- the proof below to Godement totalization, preserving the accepted kernel conversion behavior.
@[nolint synTaut]
private theorem natTrans_self_eq {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (α : F ⟶ G) : α = α := rfl

theorem godementContractionInsertion_quasiIso {X : Scheme.{u}}
    (F : X.Modules ⥤ X.Modules) [F.Additive] (E : X.Modules)
    [IsFiniteLocallyFree X E] (K : CochainComplex.Plus X.Modules) :
    QuasiIso ((godementContractionInsertion X F E).app K).hom := by
  exact postcompose_quasiIso_of_eq (godementContractionPreTotalMap X F E)
    (godementTotalPlus X) (godementContractionInsertion X F E)
    (natTrans_self_eq (F := godementContractionPlain X F E)
      (G := godementContractionResolved X F E) (godementContractionInsertion X F E))
    (godementContractionPreTotalMap_quasiIso F E)
    (@godementTotalPlus_map_quasiIso X) K

/-- The map from Godement totalization to resolved contraction formed from `e` and the insertion
map. -/
def godementContractionMap {X : Scheme.{u}} (F : X.Modules ⥤ X.Modules)
    [F.Additive] (E : X.Modules) (e : F ⋙ moduleTensorLeftFunctor X E ≅ 𝟭 X.Modules) :
    godementTotalPlus X ⟶ godementContractionResolved X F E :=
  (godementContractionPlainIso F E e).inv ≫ godementContractionInsertion X F E

lemma godementContractionMap_app {X : Scheme.{u}} (F : X.Modules ⥤ X.Modules)
    [F.Additive] (E : X.Modules) (e : F ⋙ moduleTensorLeftFunctor X E ≅ 𝟭 X.Modules)
    (K : CochainComplex.Plus X.Modules) :
    (godementContractionMap F E e).app K =
      (godementContractionPlainIso F E e).inv.app K ≫
        (godementContractionInsertion X F E).app K := rfl

theorem godementContractionMap_quasiIso {X : Scheme.{u}}
    (F : X.Modules ⥤ X.Modules) [F.Additive] (E : X.Modules)
    [IsFiniteLocallyFree X E] (e : F ⋙ moduleTensorLeftFunctor X E ≅ 𝟭 X.Modules)
    (K : CochainComplex.Plus X.Modules) :
    QuasiIso ((godementContractionMap F E e).app K).hom :=
  Plus.plus_nattrans_comp_quasiIso _ _
    (fun C => Plus.plus_iso_quasiIso ((godementContractionPlainIso F E e).inv.app C))
    (fun C => godementContractionInsertion_quasiIso F E C) K

theorem godementContractionResolved_sameLowerBound {X : Scheme.{u}}
    (F : X.Modules ⥤ X.Modules) [F.Additive] (E : X.Modules)
    (K : CochainComplex.Plus X.Modules) (a : ℤ) [K.obj.IsStrictlyGE a] :
    ((godementContractionResolved X F E).obj K).obj.IsStrictlyGE a := by
  have : (F.mapCochainComplexPlus.obj K).obj.IsStrictlyGE a :=
    inferInstanceAs (CochainComplex.IsStrictlyGE
      ((F.mapHomologicalComplex (.up ℤ)).obj K.obj) a)
  have : ((godementTotalPlus X).obj (F.mapCochainComplexPlus.obj K)).obj.IsStrictlyGE a :=
    godementTotalPlus_sameLowerBound (F.mapCochainComplexPlus.obj K) a
  have : ((moduleTensorLeftFunctor X E).mapCochainComplexPlus.obj
      ((godementTotalPlus X).obj (F.mapCochainComplexPlus.obj K))).obj.IsStrictlyGE a :=
    inferInstanceAs (CochainComplex.IsStrictlyGE
      (((moduleTensorLeftFunctor X E).mapHomologicalComplex (.up ℤ)).obj
        ((godementTotalPlus X).obj (F.mapCochainComplexPlus.obj K)).obj) a)
  let B := ((F.mapCochainComplexPlus ⋙ godementTotalPlus X) ⋙
    (moduleTensorLeftFunctor X E).mapCochainComplexPlus).obj K
  have : B.obj.IsStrictlyGE a := inferInstanceAs
    (((moduleTensorLeftFunctor X E).mapCochainComplexPlus.obj
      ((godementTotalPlus X).obj (F.mapCochainComplexPlus.obj K))).obj.IsStrictlyGE a)
  exact godementTotalPlus_sameLowerBound B a

theorem godementContractionResolved_termwiseFlasque {X : Scheme.{u}}
    (F : X.Modules ⥤ X.Modules) [F.Additive] (E : X.Modules)
    (K : CochainComplex.Plus X.Modules) (n : ℤ) :
    TopCat.Presheaf.IsFlasque
      (((godementContractionResolved X F E).obj K).obj.X n).presheaf :=
  godementTotalPlus_termwiseFlasque
    ((moduleTensorLeftFunctor X E).mapCochainComplexPlus.obj
      ((godementTotalPlus X).obj (F.mapCochainComplexPlus.obj K))) n

end AlgebraicGeometry.Scheme.Modules.Godement
