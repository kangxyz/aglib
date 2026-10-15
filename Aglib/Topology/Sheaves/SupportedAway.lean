/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Topology.Sober
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim

/-!
# Subsheaves supported away from open neighborhoods

The kernel of restriction to an open set forms an actual supported-away
subsheaf. Its neighborhood diagram has a canonical monic colimit map. Explicit
stalk-zero and neighborhood-separation conditions make that map an isomorphism;
no Noetherian hypothesis is silently supplied.

Source: `R5Lab.CategoryTheory.Sheaves.NoetherianCohomology` at revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`. Supported-away subsheaves, neighborhood diagrams and
  colimit-map declarations only.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits TopologicalSpace Opposite
namespace TopCat.Sheaf
universe u
variable {X : TopCat.{u}}

/-- Intersection with the open `V`, as a covariant functor on open sets. -/
def openIntersectionFunctor (V : Opens X) : Opens X ⥤ Opens X where
  obj U := U ⊓ V
  map f := homOfLE (inf_le_inf_right V f.le)

/-- The presheaf with sections `F(U ∩ V)` over an open `U`. -/
def openIntersectionPresheaf (F : CategoryTheory.Sheaf
    (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (V : Opens X) :
    (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (openIntersectionFunctor V).op ⋙ F.obj

lemma openIntersectionPresheaf_isSheaf
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (V : Opens X) :
    CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology X)
      (openIntersectionPresheaf F V) := by
  let e : Opens.map V.inclusion' ⋙ V.isOpenEmbedding.functor ≅ openIntersectionFunctor V :=
    NatIso.ofComponents (fun U => eqToIso (Opens.functor_map_eq_inf V U))
      (by intros; subsingleton)
  let G := (TopCat.Sheaf.pushforward AddCommGrpCat.{u} V.inclusion').obj
    ((V.sheafRestrict).obj F)
  let e' : G.obj ≅ openIntersectionPresheaf F V :=
    Functor.isoWhiskerRight (NatIso.op e).symm F.obj
  exact (CategoryTheory.Presheaf.isSheaf_of_iso_iff e').mp G.property

/-- The sheaf on `X` whose sections over `U` are the sections of `F` over `U ∩ V`. -/
def openIntersectionSheaf (F : CategoryTheory.Sheaf
    (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (V : Opens X) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  ⟨openIntersectionPresheaf F V, openIntersectionPresheaf_isSheaf F V⟩

/-- Restriction from `F` to the sheaf with sections `F(U ∩ V)` over `U`. -/
def toOpenIntersection (F : CategoryTheory.Sheaf
    (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (V : Opens X) :
    F ⟶ openIntersectionSheaf F V := ⟨{
  app U := F.obj.map (homOfLE (inf_le_left : U.unop ⊓ V ≤ U.unop)).op
  naturality := by
    intro U W i
    simp only [openIntersectionSheaf, openIntersectionPresheaf, Functor.comp_map,
      Functor.op_map, ← F.obj.map_comp]
    congr 1 }⟩

/-- The kernel of restriction to intersections with `V`; its sections over `U` vanish on `U ∩ V`. -/
def supportedAway (F : CategoryTheory.Sheaf
    (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (V : Opens X) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  kernel (toOpenIntersection F V)

lemma supportedAway_section_lift
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (V U : Opens X) (s : F.obj.obj (op U))
    (hs : F.obj.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op s = 0) :
    ∃ t : (supportedAway F V).obj.obj (op U),
      (kernel.ι (toOpenIntersection F V)).hom.app (op U) t = s := by
  exact TopCat.Sheaf.sections_exact_of_left_exact
    (ShortComplex.exact_kernel (toOpenIntersection F V)) inferInstance s hs

lemma supportedAway_stalk_isZero
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (V : Opens X) (x : X) (hx : x ∈ V) :
    IsZero (TopCat.Presheaf.stalk (supportedAway F V).obj x) := by
  let K := supportedAway F V
  let ι := kernel.ι (toOpenIntersection F V)
  let φ := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map ι.hom
  have : Mono φ :=
    (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map_mono ι
  have hφ : Function.Injective φ := (AddCommGrpCat.mono_iff_injective _).mp inferInstance
  refine @AddCommGrpCat.isZero_of_subsingleton _ ?_
  apply subsingleton_of_forall_eq 0
  intro t
  apply hφ
  obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq K.obj t
  have hs : F.obj.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op
      (ι.hom.app (op U) s) = 0 := by
    have h := congrArg (fun f => f.hom.app (op U)) (kernel.condition (toOpenIntersection F V))
    exact congrArg (fun f => f s) h
  change ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map ι.hom)
    (TopCat.Presheaf.germ K.obj U x hxU s) = φ 0
  rw [map_zero]
  calc
    _ = TopCat.Presheaf.germ F.obj U x hxU (ι.hom.app (op U) s) :=
      TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU ι.hom s
    _ = TopCat.Presheaf.germ F.obj (U ⊓ V) x ⟨hxU, hx⟩
        (F.obj.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op (ι.hom.app (op U) s)) :=
      (TopCat.Presheaf.germ_res_apply F.obj (homOfLE inf_le_left) x ⟨hxU, hx⟩ _).symm
    _ = 0 := by rw [hs, map_zero]

/-- Restriction from intersections with `V` to intersections with `U` when `U ≤ V`. -/
def openIntersectionMap (F : CategoryTheory.Sheaf
    (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    {U V : Opens X} (h : U ≤ V) :
    openIntersectionSheaf F V ⟶ openIntersectionSheaf F U := ⟨{
  app W := F.obj.map (homOfLE (inf_le_inf_left W.unop h)).op
  naturality := by
    intro W T i
    simp only [openIntersectionSheaf, openIntersectionPresheaf, Functor.comp_map,
      Functor.op_map, ← F.obj.map_comp]
    congr 1 }⟩

lemma toOpenIntersection_comp (F : CategoryTheory.Sheaf
    (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    {U V : Opens X} (h : U ≤ V) :
    toOpenIntersection F V ≫ openIntersectionMap F h = toOpenIntersection F U := by
  ext W
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    toOpenIntersection, openIntersectionMap, ← F.obj.map_comp]
  congr 1

/-- The map `supportedAway F V ⟶ supportedAway F U` induced by `U ≤ V`. -/
def supportedAwayMap (F : CategoryTheory.Sheaf
    (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    {U V : Opens X} (h : U ≤ V) : supportedAway F V ⟶ supportedAway F U :=
  kernel.lift (toOpenIntersection F U) (kernel.ι (toOpenIntersection F V)) (by
    rw [← toOpenIntersection_comp F h, ← Category.assoc, kernel.condition, zero_comp])

@[reassoc (attr := simp)]
lemma supportedAwayMap_ι (F : CategoryTheory.Sheaf
    (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    {U V : Opens X} (h : U ≤ V) :
    supportedAwayMap F h ≫ kernel.ι (toOpenIntersection F U) =
      kernel.ι (toOpenIntersection F V) := kernel.lift_ι _ _ _

/-- The open neighborhoods of `G`, ordered by inclusion. -/
abbrev supportNeighborhoods (G : Set X) := {U : Opens X // G ⊆ U}

instance supportNeighborhoods_isCofiltered (G : Set X) :
    IsCofiltered (supportNeighborhoods G) where
  nonempty := ⟨⟨⊤, Set.subset_univ G⟩⟩
  cone_objs U V := by
    let W : supportNeighborhoods G :=
      ⟨U.val ⊓ V.val, fun x hx => ⟨U.property hx, V.property hx⟩⟩
    refine ⟨W, homOfLE ?_, homOfLE ?_, True.intro⟩
    · change U.val ⊓ V.val ≤ U.val
      exact inf_le_left
    · change U.val ⊓ V.val ≤ V.val
      exact inf_le_right
  cone_maps U V f g := ⟨_, 𝟙 _, by subsingleton⟩

/-- The diagram of subsheaves vanishing on open neighborhoods of `G`, indexed by reverse
inclusion. -/
def supportedAwayDiagram (F : CategoryTheory.Sheaf
    (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (G : Set X) :
    (supportNeighborhoods G)ᵒᵖ ⥤
      CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} where
  obj U := supportedAway F U.unop.val
  map i := supportedAwayMap F i.unop.le
  map_id U := by
    apply (cancel_mono (kernel.ι (toOpenIntersection F U.unop.val))).mp
    simp
  map_comp f g := by
    apply (cancel_mono (kernel.ι _)).mp
    simp

/-- The cocone into `F` whose legs include the subsheaves vanishing on open neighborhoods of `G`. -/
def supportedAwayCocone (F : CategoryTheory.Sheaf
    (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (G : Set X) :
    Cocone (supportedAwayDiagram F G) where
  pt := F
  ι := {
    app U := kernel.ι (toOpenIntersection F U.unop.val)
    naturality := by
      intro U V i
      change supportedAwayMap F i.unop.le ≫ _ = _ ≫ 𝟙 _
      simpa only [Category.comp_id] using supportedAwayMap_ι F i.unop.le }

/-- The map to `F` induced by the colimit of subsheaves vanishing on open neighborhoods of `G`. -/
def supportedAwayColimitMap (F : CategoryTheory.Sheaf
    (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (G : Set X) :
    colimit (supportedAwayDiagram F G) ⟶ F :=
  colimit.desc _ (supportedAwayCocone F G)

attribute [local instance] IsFiltered.isConnected

instance supportedAwayColimitMap_mono (F : CategoryTheory.Sheaf
    (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (G : Set X) :
    Mono (supportedAwayColimitMap F G) := by
  let c := supportedAwayCocone F G
  have : ∀ U, Mono (c.ι.app U) := fun U =>
    inferInstanceAs (Mono (kernel.ι (toOpenIntersection F U.unop.val)))
  have : Mono c.ι := NatTrans.mono_of_mono_app _
  exact colim.map_mono' c.ι (colimit.isColimit _) (isColimitConstCocone _ F)
    (supportedAwayColimitMap F G) (by
      intro U
      change colimit.ι _ U ≫ colimit.desc _ c = c.ι.app U ≫ 𝟙 F
      rw [colimit.ι_desc]
      exact (Category.comp_id _).symm)

lemma supportedAwayColimitMap_isIso_of_sections
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (G : Set X)
    (h : ∀ (U : Opens X) (s : F.obj.obj (op U)),
      ∃ V : Opens X, G ⊆ V ∧
        F.obj.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op s = 0) :
    IsIso (supportedAwayColimitMap F G) := by
  have : ∀ U, Epi ((supportedAwayColimitMap F G).hom.app U) := by
    intro U
    apply (AddCommGrpCat.epi_iff_surjective _).mpr
    intro s
    obtain ⟨V, hV, hs⟩ := h U.unop s
    obtain ⟨t, ht⟩ := supportedAway_section_lift F V U.unop s hs
    let j : (supportNeighborhoods G)ᵒᵖ := op ⟨V, hV⟩
    refine ⟨(colimit.ι (supportedAwayDiagram F G) j).hom.app U t, ?_⟩
    change ((colimit.ι (supportedAwayDiagram F G) j ≫
      supportedAwayColimitMap F G).hom.app U) t = s
    rw [supportedAwayColimitMap, colimit.ι_desc]
    exact ht
  have : Epi (supportedAwayColimitMap F G).hom := NatTrans.epi_of_epi_app _
  have : Epi (supportedAwayColimitMap F G) := inferInstance
  exact isIso_of_mono_of_epi _

lemma exists_supportNeighborhood_of_stalks_zero
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (G : Set X)
    (hzero : ∀ x ∈ G, IsZero (TopCat.Presheaf.stalk F.obj x))
    (hsep : ∀ x ∈ G, ∀ U : Opens X, x ∉ U →
      ∃ W : Opens X, x ∈ W ∧ Disjoint U W)
    (U : Opens X) (s : F.obj.obj (op U)) :
    ∃ V : Opens X, G ⊆ V ∧
      F.obj.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op s = 0 := by
  classical
  have hlocal : ∀ x : G, ∃ W : Opens X, x.val ∈ W ∧
      F.obj.map (homOfLE (inf_le_left : U ⊓ W ≤ U)).op s = 0 := by
    intro x
    by_cases hxU : x.val ∈ U
    · obtain ⟨W, hxW, iU, iU', heq⟩ :=
        TopCat.Presheaf.germ_eq F.obj x.val hxU hxU s 0
          (@Subsingleton.elim _ (AddCommGrpCat.subsingleton_of_isZero
            (hzero x.val x.property)) _ _)
      refine ⟨W, hxW, ?_⟩
      calc
        _ = F.obj.map (homOfLE (inf_le_right : U ⊓ W ≤ W)).op
            (F.obj.map iU.op s) := by rw [← Functor.map_comp_apply]; rfl
        _ = 0 := by rw [heq, map_zero, map_zero]
    · obtain ⟨W, hxW, hUW⟩ := hsep x.val x.property U hxU
      refine ⟨W, hxW, ?_⟩
      have hz : IsZero (F.obj.obj (op (U ⊓ W))) :=
        (isZero_zero AddCommGrpCat.{u}).of_iso
          ((TopCat.Sheaf.isTerminalOfEqEmpty
            (show TopCat.Sheaf AddCommGrpCat.{u} X from F) hUW.eq_bot).uniqueUpToIso
              (isZero_zero AddCommGrpCat.{u}).isTerminal)
      have := AddCommGrpCat.subsingleton_of_isZero hz
      exact Subsingleton.elim _ _
  choose W hxW hW using hlocal
  refine ⟨iSup W, fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxW ⟨x, hx⟩⟩, ?_⟩
  apply TopCat.Sheaf.eq_of_locally_eq'
    (show TopCat.Sheaf AddCommGrpCat.{u} X from F)
    (fun x : G => U ⊓ W x) (U ⊓ iSup W)
    (fun x => homOfLE (inf_le_inf_left U (le_iSup W x)))
  · intro x hx
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx.2
    exact Opens.mem_iSup.mpr ⟨i, hx.1, hi⟩
  · intro x
    rw [map_zero, ← Functor.map_comp_apply]
    exact hW x

lemma supportedAwayColimitMap_isIso_of_stalks_zero
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (G : Set X)
    (hzero : ∀ x ∈ G, IsZero (TopCat.Presheaf.stalk F.obj x))
    (hsep : ∀ x ∈ G, ∀ U : Opens X, x ∉ U →
      ∃ W : Opens X, x ∈ W ∧ Disjoint U W) :
    IsIso (supportedAwayColimitMap F G) :=
  supportedAwayColimitMap_isIso_of_sections F G
    (exists_supportNeighborhood_of_stalks_zero F G hzero hsep)

end TopCat.Sheaf
