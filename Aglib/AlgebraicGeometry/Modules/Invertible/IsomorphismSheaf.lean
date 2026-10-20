/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorAssociator
public import Aglib.AlgebraicGeometry.Modules.InternalHom
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback
public import Aglib.AlgebraicGeometry.Descent.Modules.Fppf.LineBundleStack
public import Mathlib.CategoryTheory.Bicategory.Functor.Cat.ObjectProperty
public import Mathlib.CategoryTheory.Sites.Descent.IsStack
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Sites.Subsheaf

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Picard.EtaleDescent` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`3241497c5548af63eb50c30fd5a5442f85f13b2c6e9625e02015cd007d69756f`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.Modules.Invertible
  (IsLocallyRankOne LineBundle lineBundle_isLocallyFree pullback_locallyRankOne)
/-!
Interface migration basis: `46f53465aaf3b0167049e9c8e9e2294111bb4281`.
Accepted object-owner map SHA-256:
`8a638d1a1d17381235478e81285ee940a20aedecb03e9d3ff1ae9878791e1868`.
Imports follow the current object owners; existing R5Lab declaration names and
all construction/proof bodies are preserved. Historical source and validation
receipts below retain their original basis. New-interface validation is pending.
-/
/-!
# Actual rank-one module descent and isomorphism sheaves

Mathematical source revision: `e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Engineering source revision: `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.
Manuscript locator: `K2-018#lem:k2018-geometric-exact-order`.

C4 support for `K2-018#lem:k2018-geometric-exact-order`, frozen source
basis `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.

The pseudofunctor is the native scheme module-sheaf pullback pseudofunctor,
restricted to the full subcategories of our actual locally rank-one sheaves.
It has all O-linear morphisms, with the native identity/composition coherence.
Its objects are proved quasi-coherent using the actual local-free data.

`EtaleLineBundleDescent` retains the fixed actual rank-one stack statement.
The theorem `etaleLineBundleDescent` below realizes it from the native fppf
stack of the same full subpseudofunctor and the explicit etale-to-fppf topology
comparison. Objects, all O-linear morphisms, pullbacks and their coherences
are identified by equality of pseudofunctors.

Native source: Aglib revision
`64374534558c80c2fec996ee06bf7727b6c7f3e4`,
`AlgebraicGeometry/Descent/Modules/Fppf/LineBundleStack.lean`,
`isStack_lineBundlePseudofunctor_fppfTopology`. Quasi-coherent recovery is
proved through the equivalence with extension-of-scalars descent data in
`Algebra/Category/ModuleCat/Descent/FaithfullyFlat.lean`, transported by the
actual `tilde`-pullback comparison. Rank one descends through faithfully flat
invertibility descent. The result applies to every `Scheme.{u}` with the
native module universe, without Noetherian, separatedness or quasi-compactness
assumptions on the base scheme.

From this stack theorem we PROVE that pairs of mutually inverse
actual local module maps form a sheaf, with an equivalence to literal local
module isomorphisms. No torsor, power trivialization, Picard quotient or H1
classification is supplied by the boundary or asserted by this module.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory Opposite Bicategory
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible
namespace AlgebraicGeometry.Scheme.Modules.Invertible.EtaleDescent
universe u

/-- The actual module-sheaf pullback pseudofunctor, with native coherence maps. -/
abbrev modules := Scheme.Modules.pullbackPseudofunctor.{u}

/-- The actual local-rank-one property inside the module-sheaf pseudofunctor. -/
abbrev rankOne := Scheme.Modules.pullbackPseudofunctor.isLocallyRankOne.{u}

instance rankOne_closed : rankOne.{u}.IsClosedUnderMapObj where
  map_obj hM f := pullback_locallyRankOne f.as.unop _ hM

/-- Actual line bundles and all O-linear maps, with genuine scheme pullback. -/
abbrev lineBundles := Scheme.Modules.lineBundlePseudofunctor.{u}

/-- View a line bundle in the pseudofunctor of line bundles and their pullbacks. -/
def ofLineBundle (X : Scheme.{u}) (L : LineBundle X) : lineBundles.obj (.mk (op X)) :=
  ⟨L.val, L.property⟩

/-- Recover a line bundle from an object of the line-bundle pseudofunctor. -/
def toLineBundle (X : Scheme.{u}) (L : lineBundles.obj (.mk (op X))) : LineBundle X :=
  ⟨L.obj, L.property⟩

@[simp] theorem to_ofLineBundle (X : Scheme.{u}) (L : LineBundle X) :
    toLineBundle X (ofLineBundle X L) = L := rfl

@[simp] theorem of_toLineBundle (X : Scheme.{u}) (L : lineBundles.obj (.mk (op X))) :
    ofLineBundle X (toLineBundle X L) = L := rfl

/-- Fully faithful and effective etale descent for the actual locally rank-one
module-sheaf pseudofunctor. The fixed statement is realized by
`etaleLineBundleDescent` below. -/
def EtaleLineBundleDescent : Prop := lineBundles.{u}.IsStack Scheme.etaleTopology

/-- The local and native line-bundle pseudofunctors are equal, including their
actual module morphisms, pullback functors and identity/composition coherence. -/
theorem lineBundles_eq_native :
    lineBundles.{u} = Scheme.Modules.lineBundlePseudofunctor.{u} := rfl

/-- Every etale covering is an fppf covering: an etale morphism is flat and
locally of finite presentation. This compares the actual big scheme topologies. -/
theorem etaleTopology_le_fppfTopology :
    Scheme.etaleTopology.{u} ≤ Scheme.fppfTopology.{u} := by
  change (Scheme.precoverage (@Etale : MorphismProperty Scheme.{u})).toGrothendieck ≤
    (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)).toGrothendieck
  apply CategoryTheory.Precoverage.toGrothendieck_mono
  apply Scheme.precoverage_mono
  intro X Y f hf
  exact ⟨(Etale.iff_flat_and_formallyUnramified.mp hf).1,
    (Etale.iff_flat_and_formallyUnramified.mp hf).2.2⟩

/-- Native fully faithful and effective etale descent for the unchanged actual
rank-one pseudofunctor. Source: Aglib revision
`64374534558c80c2fec996ee06bf7727b6c7f3e4`,
`AlgebraicGeometry/Descent/Modules/Fppf/LineBundleStack.lean`,
`isStack_lineBundlePseudofunctor_fppfTopology`; specialize the fppf stack to
`Scheme.etaleTopology` through `etaleTopology_le_fppfTopology`. -/
theorem etaleLineBundleDescent : EtaleLineBundleDescent.{u} := by
  unfold EtaleLineBundleDescent
  rw [lineBundles_eq_native]
  exact CategoryTheory.Pseudofunctor.IsStack.of_le
    Scheme.Modules.lineBundlePseudofunctor etaleTopology_le_fppfTopology


/-- Every object of the actual rank-one subcategory is quasi-coherent. -/
theorem object_isQuasicoherent (X : Scheme.{u}) (L : lineBundles.obj (.mk (op X))) :
    L.obj.IsQuasicoherent := by
  let : L.obj.IsLocallyFree := lineBundle_isLocallyFree X (toLineBundle X L)
  infer_instance

private theorem presheafHom_map_comp {C : Type*} [Category C]
    (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat) {S : C} (L M N : F.obj (.mk (op S)))
    {U V : (Over S)ᵒᵖ} (f : U ⟶ V)
    (a : (F.presheafHom L M).obj U) (b : (F.presheafHom M N).obj U) :
    (F.presheafHom L N).map f (a ≫ b) =
      (F.presheafHom L M).map f a ≫ (F.presheafHom M N).map f b := by
  dsimp [Pseudofunctor.presheafHom, Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
  simp only [Functor.map_comp, Category.assoc, Cat.Hom.inv_hom_id_toNatTrans_app_assoc]

private theorem presheafHom_map_id {C : Type*} [Category C]
    (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat) {S : C} (L : F.obj (.mk (op S)))
    {U V : (Over S)ᵒᵖ} (f : U ⟶ V) :
    (F.presheafHom L L).map f (𝟙 _) = 𝟙 _ := by
  dsimp [Pseudofunctor.presheafHom, Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
  simp

variable {X : Scheme.{u}}
variable (L M N : lineBundles.obj (.mk (op X)))

/-- Restriction in the actual morphism presheaf preserves composition. -/
theorem homRestriction_comp {U V : (Over X)ᵒᵖ} (f : U ⟶ V)
    (a : (lineBundles.presheafHom L M).obj U)
    (b : (lineBundles.presheafHom M N).obj U) :
    (lineBundles.presheafHom L N).map f (a ≫ b) =
      (lineBundles.presheafHom L M).map f a ≫ (lineBundles.presheafHom M N).map f b := by
  exact presheafHom_map_comp lineBundles L M N f a b

theorem homRestriction_id {U V : (Over X)ᵒᵖ} (f : U ⟶ V) :
    (lineBundles.presheafHom L L).map f (𝟙 _) = 𝟙 _ := by
  exact presheafHom_map_id lineBundles L f

open MonoidalCategory

/-- Pairs of opposite actual homomorphisms. -/
def homPairPresheaf := lineBundles.presheafHom L M ⊗ lineBundles.presheafHom M L

/-- An actual isomorphism is a pair of mutually inverse local module maps. -/
def isoSubfunctor : Subfunctor (homPairPresheaf L M) where
  obj U := {p | p.1 ≫ p.2 = 𝟙 _ ∧ p.2 ≫ p.1 = 𝟙 _}
  map f p hp := by
    constructor
    · change (lineBundles.presheafHom L M).map f p.1 ≫
        (lineBundles.presheafHom M L).map f p.2 = 𝟙 _
      rw [← homRestriction_comp, hp.1, homRestriction_id]
    · change (lineBundles.presheafHom M L).map f p.2 ≫
        (lineBundles.presheafHom L M).map f p.1 = 𝟙 _
      rw [← homRestriction_comp, hp.2, homRestriction_id]

/-- The actual module-isomorphism presheaf is a sheaf by morphism descent. -/
theorem isoSubfunctor_isSheaf (h : EtaleLineBundleDescent.{u}) :
    Presheaf.IsSheaf (Scheme.etaleTopology.over X) (isoSubfunctor L M).toFunctor := by
  let : lineBundles.IsStack Scheme.etaleTopology := h
  rw [isSheaf_iff_isSheaf_of_type]
  apply (Subfunctor.isSheaf_iff (J := Scheme.etaleTopology.over X) (isoSubfunctor L M)
    ((isSheaf_iff_isSheaf_of_type _ _).mp (Sheaf.tensorProd_isSheaf _
      (lineBundles.sheafHom Scheme.etaleTopology L M)
      (lineBundles.sheafHom Scheme.etaleTopology M L)))).2
  intro U p hp
  constructor
  · apply (((isSheaf_iff_isSheaf_of_type _ _).mp
      (lineBundles.sheafHom Scheme.etaleTopology L L).property).isSeparated _ hp).ext
    intro V f hf
    change (lineBundles.presheafHom L L).map f.op (p.1 ≫ p.2) =
      (lineBundles.presheafHom L L).map f.op (𝟙 _)
    rw [homRestriction_comp, homRestriction_id]
    exact hf.1
  · apply (((isSheaf_iff_isSheaf_of_type _ _).mp
      (lineBundles.sheafHom Scheme.etaleTopology M M).property).isSeparated _ hp).ext
    intro V f hf
    change (lineBundles.presheafHom M M).map f.op (p.2 ≫ p.1) =
      (lineBundles.presheafHom M M).map f.op (𝟙 _)
    rw [homRestriction_comp, homRestriction_id]
    exact hf.2

/-- The actual sheaf of module-sheaf isomorphisms on schemes over X. -/
def isoSheaf (h : EtaleLineBundleDescent.{u}) :
    Sheaf (Scheme.etaleTopology.over X) (Type u) :=
  ⟨(isoSubfunctor L M).toFunctor, isoSubfunctor_isSheaf L M h⟩

/-- Identify sections of the isomorphism sheaf with isomorphisms between the
pulled-back line bundles. -/
def isoSectionsEquiv (h : EtaleLineBundleDescent.{u}) (U : (Over X)ᵒᵖ) :
    (isoSheaf L M h).obj.obj U ≃
      ((lineBundles.map U.unop.hom.op.toLoc).toFunctor.obj L ≅
        (lineBundles.map U.unop.hom.op.toLoc).toFunctor.obj M) where
  toFun p := ⟨p.val.1, p.val.2, p.property.1, p.property.2⟩
  invFun e := ⟨(e.hom, e.inv), e.hom_inv_id, e.inv_hom_id⟩
  left_inv _ := rfl
  right_inv _ := rfl

end AlgebraicGeometry.Scheme.Modules.Invertible.EtaleDescent
