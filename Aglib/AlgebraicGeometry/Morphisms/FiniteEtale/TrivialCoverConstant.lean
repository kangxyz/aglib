/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.CoverCoproductPreservation
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.LeftExact

/-! A finite constant set sheaf is represented by the actual coproduct of
identity covers. Values are explicitly lifted one universe above schemes.
The constant presheaf maps locally bijectively to the represented sheaf,
including empty indices and empty test schemes. -/

@[expose] public section

noncomputable section
set_option autoImplicit false

open _root_.CategoryTheory _root_.CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.FiniteEtale

universe u

theorem finiteCoverEtaleSubcanonical : Scheme.etaleTopology.{u}.Subcanonical :=
  .of_le Scheme.etaleTopology_le_proetaleTopology

attribute [local instance] finiteCoverEtaleSubcanonical

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem finiteCoverSmallEtaleForgetContinuous (X : Scheme.{u}) :
    (Scheme.Etale.forget X).IsContinuous (Scheme.smallEtaleTopology X)
      (Scheme.etaleTopology.over X) := by
  let := flat_of_preservesFiniteLimits (Scheme.Etale.forget X)
  exact Functor.isContinuous_iff_coverPreserving.mpr
    (Functor.coverPreserving_restrictedTopology
      (MorphismProperty.Over.forget @Etale ⊤ X) (Scheme.etaleTopology.over X))

attribute [local instance] finiteCoverSmallEtaleForgetContinuous

/-- This has the same underlying presheaf and sheaf property as the current
`EtaleH1.finiteRepresentedSetSheaf`; it is a geometry-level construction. -/
def finiteCoverSectionSheaf {X : Scheme.{u}} (Y : Scheme.FiniteEtale X) :
    Sheaf (Scheme.smallEtaleTopology X) (Type (u + 1)) :=
  ⟨(Scheme.Etale.forget X).op ⋙ yoneda.obj Y.obj ⋙ uliftFunctor.{u + 1}, by
    apply (Scheme.Etale.forget X).op_comp_isSheaf_of_isSheaf
      (Scheme.smallEtaleTopology X) (Scheme.etaleTopology.over X)
    apply Presheaf.isSheaf_comp_of_isSheaf
    rw [isSheaf_iff_isSheaf_of_type]
    exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _⟩

variable (X : Scheme.{u}) (A : Type u) [Finite A]

/-- The inclusion of the copy of the terminal cover indexed by `a` into the trivial cover. -/
abbrev trivialCoverι (a : A) : terminalCover X ⟶ trivialCover X A :=
  Sigma.ι (fun _ : A => terminalCover X) a

@[reassoc] theorem trivialCoverι_struct (a : A) :
    (trivialCoverι X A a).hom.left ≫ (trivialCover X A).obj.hom = 𝟙 X :=
  Over.w (trivialCoverι X A a).hom

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The section of the trivial cover on an étale test object with constant label `a` . -/
def trivialCoverSection (U : X.Etale) (a : A) : Over.mk U.hom ⟶ (trivialCover X A).obj :=
  Over.homMk (U.hom ≫ (trivialCoverι X A a).hom.left) (by
    erw [Category.assoc, trivialCoverι_struct, Category.comp_id]
    rfl)

/-- The natural map sending each lifted constant label to its section of the trivial cover. -/
def constantTrivialPresheafMap :
    (Functor.const X.Etaleᵒᵖ).obj (ULift.{u + 1} A) ⟶
      (finiteCoverSectionSheaf (trivialCover X A)).obj where
  app U := ↾fun a => ULift.up (trivialCoverSection X A U.unop a.down)
  naturality {U V} f := by
    ext a
    apply ULift.ext
    apply Over.OverMorphism.ext
    change V.unop.hom ≫ (trivialCoverι X A a.down).hom.left =
      f.unop.left ≫ (U.unop.hom ≫ (trivialCoverι X A a.down).hom.left)
    rw [← MorphismProperty.Over.w f.unop]
    exact Category.assoc _ _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem trivialCoverSection_label (U : X.Etale) (x : U.left) (a b : A)
    (h : trivialCoverSection X A U a = trivialCoverSection X A U b) : a = b := by
  have hpoint := congrArg (fun p : Over.mk U.hom ⟶ (trivialCover X A).obj =>
    (p.left ≫ (trivialCoverSigmaIso X A).hom) x) h
  change ((U.hom ≫ (trivialCoverι X A a).hom.left) ≫ (trivialCoverSigmaIso X A).hom) x =
    ((U.hom ≫ (trivialCoverι X A b).hom.left) ≫ (trivialCoverSigmaIso X A).hom) x at hpoint
  rw [Category.assoc, trivialCoverSigmaIso_ι, Category.assoc, trivialCoverSigmaIso_ι] at hpoint
  have hindices := (sigmaι_eq_iff (g := fun _ : A => X) a b (U.hom x) (U.hom x)).mp hpoint
  exact congrArg (fun p : Σ _ : A, X => p.1) hindices

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
instance constantTrivialPresheafMap_locallyInjective :
    Presheaf.IsLocallyInjective (Scheme.smallEtaleTopology X) (constantTrivialPresheafMap X A) where
  equalizerSieve_mem {U} a b hab := by
    change _ ∈ X.smallGrothendieckTopology @Etale U.unop
    rw [Scheme.smallGrothendieckTopology_eq_toGrothendieck_smallPretopology _ le_rfl,
      Scheme.mem_toGrothendieck_smallPretopology]
    intro x
    have hsection : trivialCoverSection X A U.unop a.down =
        trivialCoverSection X A U.unop b.down := congrArg ULift.down hab
    have hlabel := trivialCoverSection_label X A U.unop x a.down b.down hsection
    have hab' : a = b := by
      apply ULift.ext
      exact hlabel
    refine ⟨U.unop, 𝟙 _, x, ?_, ?_, rfl⟩
    · subst b
      rfl
    · change Etale (𝟙 U.unop.left)
      infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
instance constantTrivialPresheafMap_locallySurjective :
    Presheaf.IsLocallySurjective (Scheme.smallEtaleTopology X) (constantTrivialPresheafMap X A)
      where
  imageSieve_mem {U} t := by
    change _ ∈ X.smallGrothendieckTopology @Etale U
    rw [Scheme.smallGrothendieckTopology_eq_toGrothendieck_smallPretopology _ le_rfl,
      Scheme.mem_toGrothendieck_smallPretopology]
    intro x
    let q : U.left ⟶ ∐ fun _ : A => X := t.down.left ≫ (trivialCoverSigmaIso X A).hom
    obtain ⟨⟨a, z⟩, hz⟩ := (sigmaMk (fun _ : A => X)).surjective (q x)
    have hx : x ∈ q ⁻¹ᵁ (Sigma.ι (fun _ : A => X) a).opensRange := by
      change q x ∈ Set.range (Sigma.ι (fun _ : A => X) a)
      refine ⟨z, ?_⟩
      simpa only [sigmaMk_mk] using hz
    let V : U.left.Opens := q ⁻¹ᵁ (Sigma.ι (fun _ : A => X) a).opensRange
    let UV : X.Etale := Scheme.Etale.mk (V.ι ≫ U.hom)
    let g : UV ⟶ U := MorphismProperty.Over.homMk V.ι rfl (by trivial)
    have hrange : Set.range (V.ι ≫ q) ⊆ Set.range (Sigma.ι (fun _ : A => X) a) := by
      rintro y ⟨v, rfl⟩
      exact v.property
    let r : V.toScheme ⟶ X :=
      IsOpenImmersion.lift (Sigma.ι (fun _ : A => X) a) (V.ι ≫ q) hrange
    have hfac : r ≫ Sigma.ι (fun _ : A => X) a = V.ι ≫ q :=
      IsOpenImmersion.lift_fac _ _ _
    have hsection : V.ι ≫ t.down.left = r ≫ (trivialCoverι X A a).hom.left := by
      apply (cancel_mono (trivialCoverSigmaIso X A).hom).mp
      rw [Category.assoc, Category.assoc, trivialCoverSigmaIso_ι]
      exact hfac.symm
    have hr : r = V.ι ≫ U.hom := by
      have hbase := congrArg (fun f => f ≫ (trivialCover X A).obj.hom) hsection
      simpa only [Category.assoc, trivialCoverι_struct, Category.comp_id, Over.w t.down,
        Scheme.Etale.forget, MorphismProperty.Over.forget, MorphismProperty.Comma.forget,
        Functor.op_obj, unop_op] using hbase.symm
    refine ⟨UV, g, ⟨x, hx⟩, ⟨ULift.up a, ?_⟩, ?_, rfl⟩
    · apply ULift.ext
      apply Over.OverMorphism.ext
      change (V.ι ≫ U.hom) ≫ (trivialCoverι X A a).hom.left = V.ι ≫ t.down.left
      rw [← hr]
      exact hsection.symm
    · change Etale V.ι
      infer_instance

/-- The represented finite cover is exactly the constant lifted set sheaf. -/
def trivialCoverConstantIso :
    finiteCoverSectionSheaf (trivialCover X A) ≅
      (constantSheaf (Scheme.smallEtaleTopology X) (Type (u + 1))).obj (ULift.{u + 1} A) := by
  let J := Scheme.smallEtaleTopology X
  let F := presheafToSheaf J (Type (u + 1))
  let m := constantTrivialPresheafMap X A
  have : Sheaf.IsLocallyInjective (F.map m) :=
    (Presheaf.isLocallyInjective_presheafToSheaf_map_iff J m).mpr inferInstance
  have : Sheaf.IsLocallySurjective (F.map m) :=
    (Presheaf.isLocallySurjective_presheafToSheaf_map_iff J m).mpr inferInstance
  have : IsIso (F.map m) :=
    (Sheaf.isLocallyBijective_iff_isIso (F.map m)).mp ⟨inferInstance, inferInstance⟩
  exact ((asIso (F.map m)) ≪≫
    asIso ((sheafificationAdjunction J (Type (u + 1))).counit.app
      (finiteCoverSectionSheaf (trivialCover X A)))).symm

end AlgebraicGeometry.Scheme.FiniteEtale

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 8eeff4571dbf085c47e70c3c147065018b16463f88c0c86a5a0d47ea7f904f5f.
Definitions, hypotheses and universes are retained modulo native names. -/
