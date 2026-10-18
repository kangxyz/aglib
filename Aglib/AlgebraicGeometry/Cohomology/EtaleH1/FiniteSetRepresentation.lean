/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.GluedUniversalSection
public import Mathlib.CategoryTheory.Sites.LocalProperties

/-!
# FiniteSetRepresentation

General constructions and comparisons for this native mathematical family.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.FiniteEtale
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (toEtale)
namespace AlgebraicGeometry.Scheme.EtaleH1
universe u
variable {X : Scheme.{u}}

/-- The explicit universe-lifted represented sections are actual small-site morphisms. -/
def finiteSectionSiteEquiv (Y : Scheme.FiniteEtale X) (W : X.Etale) :
    (finiteRepresentedSetSheaf Y).obj.obj (op W) ≃ (W ⟶ (toEtale X).obj Y) where
  toFun q := Scheme.FiniteEtale.SheafDescent.finiteSectionSiteMap Y q.down
  invFun g := ULift.up (Over.homMk g.left (MorphismProperty.Over.w g))
  left_inv q := by apply ULift.ext; apply Over.OverMorphism.ext; rfl
  right_inv g := by apply MorphismProperty.Over.Hom.ext; rfl

end AlgebraicGeometry.Scheme.EtaleH1

namespace AlgebraicGeometry.Scheme.FiniteEtale.SheafDescent.GlobalFiniteRepresentation

universe u
variable {X : Scheme.{u}}
open AlgebraicGeometry.Scheme.EtaleH1
variable {F : Scheme.EtaleH1.SetSheaf X} (t : Scheme.EtaleH1.FiniteSetLocalTrivialization F)

/-- Over an open chart, every section of the global cover factors uniquely through its local
piece. -/
theorem inclusion_bijective (U : GoodOpen (F := F)) (W : X.Etale)
    (a : W.left ⟶ U.1.toScheme) (ha : a ≫ U.1.ι = W.hom) :
    Function.Bijective (fun g : W ⟶ (representative U).site => g ≫ inclusion t U) := by
  have : Mono (inclusion t U).left :=
    inferInstanceAs (Mono ((datum t).cover.f U))
  constructor
  · intro g h heq
    apply MorphismProperty.Over.Hom.ext
    apply (cancel_mono (inclusion t U).left).1
    exact congrArg (fun k => k.left) heq
  · intro g
    obtain ⟨l, hla, hlg⟩ := (inclusion_isPullback t U).exists_lift a g.left
      (by rw [ha]; exact (MorphismProperty.Over.w g).symm)
    let k : W ⟶ (representative U).site := MorphismProperty.Over.homMk l (by
      change l ≫ ((representative U).cover.obj.hom ≫ U.1.ι) = W.hom
      rw [← Category.assoc, hla, ha]) (by trivial)
    refine ⟨k, ?_⟩
    apply MorphismProperty.Over.Hom.ext
    exact hlg

/-- On every test scheme lying in a good open, the global universal section is universal. -/
theorem universalSection_bijective (U : GoodOpen (F := F)) (W : X.Etale)
    (a : W.left ⟶ U.1.toScheme) (ha : a ≫ U.1.ι = W.hom) :
    Function.Bijective (fun g : W ⟶ (toEtale X).obj (cover t) =>
      F.obj.map g.op (universalSection t)) := by
  apply (Function.Bijective.of_comp_iff _ (inclusion_bijective t U W a ha)).1
  have heq :
      ((fun g : W ⟶ (toEtale X).obj (cover t) => F.obj.map g.op (universalSection t)) ∘
        (fun g : W ⟶ (representative U).site => g ≫ inclusion t U)) =
      (fun g : W ⟶ (representative U).site => F.obj.map g.op (representative U).section_) := by
    funext g
    simp [op_comp, Functor.map_comp]
  rw [heq]
  exact (representative U).section_bijective_of_factor W a ha

/-- The exact morphism of set sheaves is an isomorphism on each good open. -/
theorem representingMap_app_bijective (U : GoodOpen (F := F)) (W : X.Etale)
    (a : W.left ⟶ U.1.toScheme) (ha : a ≫ U.1.ι = W.hom) :
    Function.Bijective ((representingMap t).hom.app (op W)) :=
  (universalSection_bijective t U W a ha).comp (Scheme.EtaleH1.finiteSectionSiteEquiv (cover t)
    W).bijective

include t in
/-- Good opens cover the entire small etale site, including empty schemes. -/
theorem goodOpens_coversTop :
    (Scheme.smallEtaleTopology X).CoversTop
      (fun U : GoodOpen (F := F) => Scheme.Etale.mk U.1.ι) := by
  intro W
  change Sieve.ofObjects (fun U : GoodOpen (F := F) => Scheme.Etale.mk U.1.ι) W ∈
    X.smallGrothendieckTopology @Etale W
  rw [Scheme.smallGrothendieckTopology_eq_toGrothendieck_smallPretopology _ le_rfl,
    Scheme.mem_toGrothendieck_smallPretopology]
  intro x
  obtain ⟨U, hU, hxU⟩ := t.exists_goodAffineOpen (W.hom x)
  let y : U.toScheme := ⟨W.hom x, hxU⟩
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := U.ι) (g := W.hom) y x rfl
  let V : X.Etale := Scheme.Etale.mk (pullback.snd U.ι W.hom ≫ W.hom)
  let a : V ⟶ W := MorphismProperty.Over.homMk (pullback.snd U.ι W.hom) rfl (by trivial)
  let b : V ⟶ Scheme.Etale.mk U.ι :=
    MorphismProperty.Over.homMk (pullback.fst U.ι W.hom) pullback.condition (by trivial)
  exact ⟨V, a, z, ⟨⟨U, hU⟩, ⟨b⟩⟩, inferInstance, hz₂⟩

/-- The map produced from the glued universal section is an actual sheaf isomorphism. -/
theorem representingMap_isIso : IsIso (representingMap t) := by
  apply Sheaf.isIso_of_coversTop (goodOpens_coversTop t)
  intro U
  rw [← ObjectProperty.isIso_hom_iff, NatTrans.isIso_iff_isIso_app]
  intro W
  apply (CategoryTheory.isIso_iff_bijective _).2
  exact representingMap_app_bijective t U W.unop.left W.unop.hom.left
    (MorphismProperty.Over.w W.unop.hom)

/-- The global finite etale cover represents the original set sheaf, with its exact universe lift.
-/
def representingIso : Scheme.EtaleH1.finiteRepresentedSetSheaf (cover t) ≅ F := by
  letI := representingMap_isIso t
  exact asIso (representingMap t)

end AlgebraicGeometry.Scheme.FiniteEtale.SheafDescent.GlobalFiniteRepresentation

namespace AlgebraicGeometry.Scheme.EtaleH1

universe u

/-- Constructive producer for the exact existing Stacks 03RV (Lemma 59.64.4,
https://stacks.math.columbia.edu/tag/03RV) existence interface in
`FiniteTorsorRepresentation.lean`, on mathematical snapshot `1e2b2a1a`.
The sole input is the original finite local constancy predicate. The constructed
cover and sheaf isomorphism work for arbitrary schemes and varying finite ranks,
including empty schemes and empty chart values. -/
theorem stacks03RV (X : Scheme.{u}) : Stacks03RV X where
  representable F hF := by
    obtain ⟨t⟩ := hF
    exact ⟨Scheme.FiniteEtale.SheafDescent.GlobalFiniteRepresentation.cover t,
      ⟨Scheme.FiniteEtale.SheafDescent.GlobalFiniteRepresentation.representingIso t⟩⟩

end AlgebraicGeometry.Scheme.EtaleH1

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 717123c8bedcb46568a8c0fb7f446b10cb0acd2c68b899774bd8a9c3e002773a.
Definitions, hypotheses and universes are retained modulo native names. -/
