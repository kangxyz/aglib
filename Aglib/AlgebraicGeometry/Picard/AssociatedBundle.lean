/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.UnitInverse

public import Aglib.AlgebraicGeometry.Picard.FrameTorsor
public import Aglib.AlgebraicGeometry.Picard.UnitDescent
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.Coefficients
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.TorsorPullback
public import Aglib.CategoryTheory.Sites.Torsor.Transport
public import Aglib.AlgebraicGeometry.Modules.InternalHom
public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorAssociator
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Picard.AssociatedBundle` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`07bf568a4aa094f8a6d493d503fed718fbb8b5ed6fb1d4e95a9e51d25286a9f7`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.EtaleCohomology
open _root_.AlgebraicGeometry.Scheme.Modules.Invertible (LineBundle LineBundleClass )
open _root_.AlgebraicGeometry.Scheme.Modules (pullbackUnitIso)
/-!
Interface migration basis: `46f53465aaf3b0167049e9c8e9e2294111bb4281`.
Accepted object-owner map SHA-256:
`8a638d1a1d17381235478e81285ee940a20aedecb03e9d3ff1ae9878791e1868`.
Imports follow the current object owners; existing R5Lab declaration names and
all construction/proof bodies are preserved. Historical source and validation
receipts below retain their original basis. New-interface validation is pending.
-/
/-!
# Associated line bundles of characters of actual étale torsors

For an original torsor `P : Torsor A` and character `χ : A ⟶ gm X`,
the single character construction below uses the original section-indexed
cover and its original chosen scheme fibre products. Its literal transition
unit is the image under χ of the positive transporter sending s to t.

The existing native étale line-bundle stack descends these transitions to one
Zariski line bundle. The actual quasi-coherent/rank-one and Scheme descent
input remains geometric; no assertion about descent of arbitrary étale
modules is used. No Ext or derived-category premise enters this producer.

The Gm API specializes χ to the identity. PowerDescent specializes χ to the
original root inclusion, retaining its genuine nth-power independence and
power-trivialization arguments. Legacy stack-proof arguments remain thin
compatibility parameters for existing callers.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory Opposite Limits Bicategory
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Hom
open AlgebraicGeometry.Scheme.Modules.Invertible
namespace AlgebraicGeometry.Scheme.Modules.Invertible.AssociatedBundle
open EtaleDescent UnitDescent
open _root_.AlgebraicGeometry.Scheme.EtaleCohomology
open _root_.GroupCohomology.Kummer.Coefficients
universe u
variable {X : Scheme.{u}}

open Pseudofunctor.LocallyDiscreteOpToCat FrameTorsor

@[simp] theorem site_id_left (U : X.Etale) : (𝟙 U : U ⟶ U).left = 𝟙 U.left := rfl

private theorem presheafHom_map_eq_pullHom {S : Scheme.{u}}
    {M N : lineBundles.obj (.mk (op S))} {U V : S.Etale} (f : V ⟶ U)
    (g : (lineBundles.map U.hom.op.toLoc).toFunctor.obj M ⟶
      (lineBundles.map U.hom.op.toLoc).toFunctor.obj N) :
    (lineBundles.presheafHom M N).map ((Scheme.Etale.forget S).map f).op g =
      pullHom g f.left V.hom V.hom
        (MorphismProperty.Over.w f) (MorphismProperty.Over.w f) := rfl

namespace Construction

universe uC vC uF uG uH

/-- Naturality of one actual section family, with its whole functor heads retained. -/
def NaturalFamily {C : Type uC} [Category.{vC} C]
    (F : C ⥤ Type uF) (G : C ⥤ Type uG)
    (t : ∀ U, F.obj U → G.obj U) : Prop :=
  ∀ {U V : C} (f : U ⟶ V) (s : F.obj U), G.map f (t U s) = t V (F.map f s)

/-- A natural injective view detects naturality of the same original section family. -/
theorem naturalFamily_of_injective {C : Type uC} [Category.{vC} C]
    {F : C ⥤ Type uF} {G : C ⥤ Type uG} {H : C ⥤ Type uH}
    (r : ∀ U, G.obj U → H.obj U)
    (hr : ∀ {U V : C} (f : U ⟶ V) (s : G.obj U),
      r V (G.map f s) = H.map f (r U s))
    (hinj : ∀ U, Function.Injective (r U))
    (t : ∀ U, F.obj U → G.obj U) (b : ∀ U, F.obj U → H.obj U)
    (hb : ∀ U s, r U (t U s) = b U s)
    (hn : NaturalFamily F H b) : NaturalFamily F G t := by
  intro U V f s
  apply hinj V
  calc
    r V (G.map f (t U s)) = H.map f (r U (t U s)) := hr f _
    _ = H.map f (b U s) := congrArg (H.map f) (hb U s)
    _ = b V (F.map f s) := hn f s
    _ = r V (t V (F.map f s)) := (hb V _).symm

/-- The original raw-Hom presheaf at its actual native line-bundle object. -/
abbrev rawPresheaf (X : Scheme.{u}) (M : lineBundles.obj (.mk (op X))) :
    X.Etaleᵒᵖ ⥤ Type u :=
  (Scheme.Etale.forget X).op ⋙ lineBundles.presheafHom M (unitObject X)

/-- The same native frameRawHom, typed at the original pseudofunctor object. -/
abbrev frameRawHomNative (h : EtaleLineBundleDescent.{u}) (X : Scheme.{u})
    (M : lineBundles.obj (.mk (op X))) (U : X.Etaleᵒᵖ) :
    (frameSheaf h X (toLineBundle X M)).obj.obj U → (rawPresheaf X M).obj U :=
  FrameTorsor.frameRawHom h X (toLineBundle X M) U

/-- The native-object view retains the original injective raw-frame map. -/
theorem frameRawHomNative_injective (h : EtaleLineBundleDescent.{u}) (X : Scheme.{u})
    (M : lineBundles.obj (.mk (op X))) (U : X.Etaleᵒᵖ) :
    Function.Injective (frameRawHomNative h X M U) :=
  FrameTorsor.frameRawHom_injective h X (toLineBundle X M) U

/-- Naturality of the same raw-frame map before any descended object is supplied. -/
theorem frameRawHomNative_naturality (h : EtaleLineBundleDescent.{u}) (X : Scheme.{u})
    (M : lineBundles.obj (.mk (op X))) {U V : X.Etaleᵒᵖ} (f : U ⟶ V)
    (s : (frameSheaf h X (toLineBundle X M)).obj.obj U) :
    frameRawHomNative h X M V
        ((frameSheaf h X (toLineBundle X M)).obj.map f s) =
      (rawPresheaf X M).map f (frameRawHomNative h X M U s) :=
  FrameTorsor.frameRawHom_naturality h X (toLineBundle X M) f s

end Construction

section General
variable {A : AbelianSheaf.{u, u + 1} X} (P : Torsor A) (χ : A ⟶ gm X)

section Cover

/-- Every section on every etale test scheme indexes a genuine trivialization. -/
def Index := Σ U : X.Etale, P.carrier.obj.obj (op U)
/-- The etale test scheme underlying a torsor-section index. -/
def coverObject (i : Index P) : Scheme.{u} := i.1.left
/-- The structure map of the etale scheme indexing a torsor section. -/
def coverMap (i : Index P) : coverObject P i ⟶ X := i.1.hom
instance coverMap_etale (i : Index P) : Etale (coverMap P i) := i.1.prop

theorem cover_mem : Sieve.ofArrows (coverObject P) (coverMap P) ∈ Scheme.etaleTopology X := by
  apply Precoverage.generate_mem_toGrothendieck
  rw [Scheme.ofArrows_mem_precoverage_iff]
  refine ⟨?_, fun i => i.1.prop⟩
  intro x
  have h := P.locally_nonempty (etaleTerminal X)
  change _ ∈ X.smallGrothendieckTopology @Etale (etaleTerminal X) at h
  rw [Scheme.smallGrothendieckTopology_eq_toGrothendieck_smallPretopology _ le_rfl,
    Scheme.mem_toGrothendieck_smallPretopology] at h
  obtain ⟨V, f, v, ⟨p⟩, _, hv⟩ := h x
  refine ⟨⟨V, p⟩, v, ?_⟩
  have hf : f.left = V.hom := by simpa using (MorphismProperty.Over.w f)
  change f.left v = x at hv
  rw [hf] at hv
  exact hv

end Cover

namespace Construction

universe uC vC

/-- Keep a whole chart equation shared before specializing its category and maps. -/
def ChartComposition {C : Type uC} [Category.{vC} C] {M N : C}
    (f : M ⟶ N) (t : N ⟶ N) (g : M ⟶ N) : Prop :=
  f ≫ t = g

/-- Cancel the actual identity transition before evaluating the native chart maps. -/
private theorem chartComposition_eq {C : Type uC} [Category.{vC} C] {M N : C}
    {f g : M ⟶ N} {t : N ⟶ N} (h : ChartComposition f t g) (ht : t = 𝟙 N) :
    f = g := by
  subst t
  exact (Category.comp_id f).symm.trans h

/-- Actual raw charts on the original section-indexed cover, with one native object. -/
abbrev RawChartFamily (M : lineBundles.obj (.mk (op X))) :=
  ∀ i : Index P,
    (lineBundles.map (coverMap P i).op.toLoc).toFunctor.obj M ⟶
      (lineBundles.map (coverMap P i).op.toLoc).toFunctor.obj (unitObject X)

/-- Read the indexed raw chart at each original torsor section. -/
abbrev sectionFamily (M : lineBundles.obj (.mk (op X))) (c : RawChartFamily P M) :
    ∀ U : X.Etaleᵒᵖ, P.carrier.obj.obj U → (rawPresheaf X M).obj U :=
  fun U s => c ⟨U.unop, s⟩

/-- The original positive transition equation on one arbitrary refinement. -/
def ChartRelationOn (M : lineBundles.obj (.mk (op X))) (c : RawChartFamily P M)
    (u : ∀ U : X.Etaleᵒᵖ, P.carrier.obj.obj U → P.carrier.obj.obj U → Γ(U.unop.left, ⊤)ˣ)
    {V : X.Etale} (i j : Index P) (a : V ⟶ i.1) (b : V ⟶ j.1) : Prop :=
  ChartComposition
    (pullHom (F := lineBundles) (c i) a.left V.hom V.hom
      (MorphismProperty.Over.w a) (MorphismProperty.Over.w a))
    (AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.transition V.hom V.hom
      ((u (op V) (P.carrier.obj.map a.op i.2) (P.carrier.obj.map b.op j.2) :
        Γ(V.left, ⊤)ˣ) : Γ(V.left, ⊤)))
    (pullHom (F := lineBundles) (c j) b.left V.hom V.hom
      (MorphismProperty.Over.w b) (MorphismProperty.Over.w b))

/-- The same regular transition relation for every original common refinement. -/
def ChartRelations (M : lineBundles.obj (.mk (op X))) (c : RawChartFamily P M)
    (u : ∀ U : X.Etaleᵒᵖ, P.carrier.obj.obj U → P.carrier.obj.obj U → Γ(U.unop.left, ⊤)ˣ) :
    Prop :=
  ∀ {V : X.Etale} (i j : Index P) (a : V ⟶ i.1) (b : V ⟶ j.1),
    ChartRelationOn P M c u i j a b

/-- The proved transition relation and diagonal unit give whole raw-chart naturality. -/
theorem sectionFamily_natural (M : lineBundles.obj (.mk (op X)))
    (c : RawChartFamily P M)
    (u : ∀ U : X.Etaleᵒᵖ, P.carrier.obj.obj U → P.carrier.obj.obj U → Γ(U.unop.left, ⊤)ˣ)
    (hr : ChartRelations P M c u)
    (hu : ∀ U (s : P.carrier.obj.obj U), u U s s = 1) :
    NaturalFamily P.carrier.obj (rawPresheaf X M) (sectionFamily P M c) := by
  intro U V f s
  have hview :
      (rawPresheaf X M).map f (c ⟨U.unop, s⟩) =
        pullHom (F := lineBundles) (M₁ := M) (M₂ := unitObject X)
          (f₁ := U.unop.hom) (f₂ := U.unop.hom) (c ⟨U.unop, s⟩)
          f.unop.left V.unop.hom V.unop.hom
          (MorphismProperty.Over.w f.unop) (MorphismProperty.Over.w f.unop) :=
    presheafHom_map_eq_pullHom (S := X) (M := M) (N := unitObject X)
      f.unop (c ⟨U.unop, s⟩)
  have hh := hr ⟨U.unop, s⟩ ⟨V.unop, P.carrier.obj.map f s⟩ f.unop (𝟙 V.unop)
  have hunit :
      u (op V.unop) (P.carrier.obj.map f.unop.op s)
        (P.carrier.obj.map (𝟙 V.unop).op (P.carrier.obj.map f s)) = 1 :=
    (congrArg (u V (P.carrier.obj.map f s))
      (P.carrier.obj.map_id_apply V (P.carrier.obj.map f s))).trans
        (hu V (P.carrier.obj.map f s))
  have htransition :
      AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.transition
          V.unop.hom V.unop.hom
          ((u (op V.unop) (P.carrier.obj.map f.unop.op s)
            (P.carrier.obj.map (𝟙 V.unop).op (P.carrier.obj.map f s)) :
              Γ(V.unop.left, ⊤)ˣ) : Γ(V.unop.left, ⊤)) = 𝟙 _ :=
    (congrArg
      (fun a : Γ(V.unop.left, ⊤)ˣ =>
        AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.transition
          V.unop.hom V.unop.hom (a : Γ(V.unop.left, ⊤))) hunit).trans
      (AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.transition_self_one V.unop.hom)
  have hid :
      pullHom (F := lineBundles) (M₁ := M) (M₂ := unitObject X)
          (f₁ := V.unop.hom) (f₂ := V.unop.hom)
          (c ⟨V.unop, P.carrier.obj.map f s⟩)
          (𝟙 V.unop : V.unop ⟶ V.unop).left V.unop.hom V.unop.hom
          (MorphismProperty.Over.w (𝟙 V.unop : V.unop ⟶ V.unop))
          (MorphismProperty.Over.w (𝟙 V.unop : V.unop ⟶ V.unop)) =
        c ⟨V.unop, P.carrier.obj.map f s⟩ :=
    pullHom_id (F := lineBundles) (M₁ := M) (M₂ := unitObject X)
      (f₁ := V.unop.hom) (f₂ := V.unop.hom)
      (c ⟨V.unop, P.carrier.obj.map f s⟩)
  exact hview.trans ((chartComposition_eq hh htransition).trans hid)

end Construction


/-- The unique positive coefficient carrying one torsor section to another. -/
def transport (U : X.Etaleᵒᵖ) (s t : P.carrier.obj.obj U) : A.obj.obj U :=
  (P.sectionEquiv U s).symm t

/-- The legacy value is the same generic positive transporter, by uniqueness. -/
theorem transport_eq_positiveTransport (U : X.Etaleᵒᵖ) (s t : P.carrier.obj.obj U) :
    transport P U s t = P.positiveTransport U s t :=
  (P.positiveTransport_eq_sectionEquiv_symm U s t).symm

@[simp] theorem action_transport (U : X.Etaleᵒᵖ) (s t : P.carrier.obj.obj U) :
    P.action U (transport P U s t) s = t := by
  simpa only [transport_eq_positiveTransport] using P.action_positiveTransport U s t

theorem transport_eq (U : X.Etaleᵒᵖ) (s t : P.carrier.obj.obj U)
    (a : A.obj.obj U) (ha : P.action U a s = t) : transport P U s t = a := by
  rw [transport_eq_positiveTransport]
  exact P.positiveTransport_eq U s t a ha

@[simp] theorem transport_self (U : X.Etaleᵒᵖ) (s : P.carrier.obj.obj U) :
    transport P U s s = 0 := by
  simpa only [transport_eq_positiveTransport] using P.positiveTransport_self U s

theorem transport_trans (U : X.Etaleᵒᵖ) (s t r : P.carrier.obj.obj U) :
    transport P U s t + transport P U t r = transport P U s r := by
  simpa only [transport_eq_positiveTransport] using P.positiveTransport_trans U s t r

theorem transport_naturality {U V : X.Etaleᵒᵖ} (f : U ⟶ V)
    (s t : P.carrier.obj.obj U) :
    A.obj.map f (transport P U s t) =
      transport P V (P.carrier.obj.map f s) (P.carrier.obj.map f t) := by
  simpa only [transport_eq_positiveTransport] using P.positiveTransport_naturality f s t

namespace Character


/-- Literal unit of the character applied to the original positive transport. -/
def transportUnit (U : X.Etaleᵒᵖ) (s t : P.carrier.obj.obj U) : Γ(U.unop.left, ⊤)ˣ :=
  (unitsSections X U (χ.hom.app U (transport P U s t))).toMul

@[simp] theorem transportUnit_self (U : X.Etaleᵒᵖ) (s : P.carrier.obj.obj U) :
    transportUnit P χ U s s = 1 := by simp [transportUnit]

theorem transportUnit_trans (U : X.Etaleᵒᵖ) (s t r : P.carrier.obj.obj U) :
    transportUnit P χ U s t * transportUnit P χ U t r = transportUnit P χ U s r := by
  have ht := congrArg (fun a => (unitsSections X U (χ.hom.app U a)).toMul)
    (transport_trans P U s t r)
  simpa only [transportUnit, map_add, toMul_add] using ht

theorem transportUnit_naturality {U V : X.Etaleᵒᵖ} (f : U ⟶ V)
    (s t : P.carrier.obj.obj U) :
    pullUnit f.unop.left (transportUnit P χ U s t) =
      transportUnit P χ V (P.carrier.obj.map f s) (P.carrier.obj.map f t) := by
  unfold pullUnit transportUnit
  rw [← unitsSections_naturality]
  have hχ := ConcreteCategory.congr_hom (χ.hom.naturality f) (transport P U s t)
  change χ.hom.app V (A.obj.map f (transport P U s t)) =
    (gm X).obj.map f (χ.hom.app U (transport P U s t)) at hχ
  rw [← hχ, transport_naturality]


end Character


/-- A fixed genuine scheme fiber product. -/
def chosenPullback {A B S : Scheme.{u}} (f : A ⟶ S) (g : B ⟶ S) : ChosenPullback f g where
  pullback := CategoryTheory.Limits.pullback f g
  p₁ := pullback.fst f g
  p₂ := pullback.snd f g
  condition := pullback.condition
  isLimit := (IsPullback.of_hasPullback f g).isLimit

/-- The chosen pairwise fibre product of two torsor trivialization schemes. -/
def overlap (i j : Index P) : ChosenPullback (coverMap P i) (coverMap P j) :=
  chosenPullback _ _

instance overlap_p₁_etale (i j : Index P) : Etale (overlap P i j).p₁ := by
  dsimp [overlap, chosenPullback]
  infer_instance
instance overlap_p₂_etale (i j : Index P) : Etale (overlap P i j).p₂ := by
  dsimp [overlap, chosenPullback]
  infer_instance
instance overlap_p_etale (i j : Index P) : Etale (overlap P i j).p := by
  dsimp [overlap, chosenPullback]
  infer_instance

/-- The pairwise overlap viewed as an object of the small etale site of `X`. -/
def overlapEtale (i j : Index P) : X.Etale := Scheme.Etale.mk (overlap P i j).p

/-- The first projection from the overlap in the small etale site. -/
def overlapFst (i j : Index P) : overlapEtale P i j ⟶ i.1 :=
  MorphismProperty.Over.homMk (overlap P i j).p₁ (by simp [overlapEtale, coverMap]) (by trivial)
/-- The second projection from the overlap in the small etale site. -/
def overlapSnd (i j : Index P) : overlapEtale P i j ⟶ j.1 :=
  MorphismProperty.Over.homMk (overlap P i j).p₂ (by simp [overlapEtale, coverMap]) (by trivial)


/-- The chosen triple overlap of three torsor trivialization schemes, with its pairwise
projections. -/
def triple (i j k : Index P) : ChosenPullback₃ (overlap P i j) (overlap P j k) (overlap P i k) where
  chosenPullback := chosenPullback (overlap P i j).p₂ (overlap P j k).p₁
  l := Classical.choice (ChosenPullback.LiftStruct.nonempty (by
    simp only [Category.assoc]
    rw [(overlap P i j).condition, ← Category.assoc,
      (chosenPullback (overlap P i j).p₂ (overlap P j k).p₁).condition,
      Category.assoc, (overlap P j k).condition]) (by simp))

instance triple_p_etale (i j k : Index P) : Etale (triple P i j k).p := by
  dsimp [triple, chosenPullback]
  infer_instance

/-- The triple overlap viewed as an object of the small etale site of `X`. -/
def tripleEtale (i j k : Index P) : X.Etale := Scheme.Etale.mk (triple P i j k).p

/-- The first projection from the triple overlap to a trivialization scheme. -/
def tripleFst (i j k : Index P) : tripleEtale P i j k ⟶ i.1 :=
  MorphismProperty.Over.homMk (triple P i j k).p₁ (by simp [tripleEtale, coverMap]) (by trivial)
/-- The middle projection from the triple overlap to a trivialization scheme. -/
def tripleMid (i j k : Index P) : tripleEtale P i j k ⟶ j.1 :=
  MorphismProperty.Over.homMk (triple P i j k).p₂ (by simp [tripleEtale, coverMap]) (by trivial)
/-- The third projection from the triple overlap to a trivialization scheme. -/
def tripleSnd (i j k : Index P) : tripleEtale P i j k ⟶ k.1 :=
  MorphismProperty.Over.homMk (triple P i j k).p₃ (by simp [tripleEtale, coverMap]) (by trivial)
/-- The projection from the triple overlap to the first and second pairwise overlap. -/
def triple12 (i j k : Index P) : tripleEtale P i j k ⟶ overlapEtale P i j :=
  MorphismProperty.Over.homMk (triple P i j k).p₁₂ (by simp [tripleEtale, overlapEtale]) (by
      trivial)
/-- The projection from the triple overlap to the second and third pairwise overlap. -/
def triple23 (i j k : Index P) : tripleEtale P i j k ⟶ overlapEtale P j k :=
  MorphismProperty.Over.homMk (triple P i j k).p₂₃ (by simp [tripleEtale, overlapEtale]) (by
      trivial)
/-- The projection from the triple overlap to the first and third pairwise overlap. -/
def triple13 (i j k : Index P) : tripleEtale P i j k ⟶ overlapEtale P i k :=
  MorphismProperty.Over.homMk (triple P i j k).p₁₃ (by simp [tripleEtale, overlapEtale]) (by
      trivial)

@[simp] theorem triple12_fst (i j k : Index P) :
    triple12 P i j k ≫ overlapFst P i j = tripleFst P i j k := by
  apply MorphismProperty.Over.Hom.ext
  exact (triple P i j k).p₁₂_p₁
@[simp] theorem triple12_snd (i j k : Index P) :
    triple12 P i j k ≫ overlapSnd P i j = tripleMid P i j k := by
  apply MorphismProperty.Over.Hom.ext
  exact (triple P i j k).p₁₂_p₂
@[simp] theorem triple23_fst (i j k : Index P) :
    triple23 P i j k ≫ overlapFst P j k = tripleMid P i j k := by
  apply MorphismProperty.Over.Hom.ext
  exact (triple P i j k).p₂₃_p₂
@[simp] theorem triple23_snd (i j k : Index P) :
    triple23 P i j k ≫ overlapSnd P j k = tripleSnd P i j k := by
  apply MorphismProperty.Over.Hom.ext
  exact (triple P i j k).p₂₃_p₃
@[simp] theorem triple13_fst (i j k : Index P) :
    triple13 P i j k ≫ overlapFst P i k = tripleFst P i j k := by
  apply MorphismProperty.Over.Hom.ext
  exact (triple P i j k).p₁₃_p₁
@[simp] theorem triple13_snd (i j k : Index P) :
    triple13 P i j k ≫ overlapSnd P i k = tripleSnd P i j k := by
  apply MorphismProperty.Over.Hom.ext
  exact (triple P i j k).p₁₃_p₃

/-- The diagonal from a trivialization scheme to its self-overlap in the small etale site. -/
def diagonalEtale (i : Index P) : i.1 ⟶ overlapEtale P i i :=
  MorphismProperty.Over.homMk (AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.diagonal
      (overlap P) i)
    (by
      change AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.diagonal (overlap P) i ≫
          (overlap P i i).p = i.1.hom
      rw [← (overlap P i i).hp₁, ← Category.assoc,
          AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.diagonal_p₁, Category.id_comp]
      rfl) (by trivial)
@[simp] theorem diagonal_fst (i : Index P) :
    diagonalEtale P i ≫ overlapFst P i i = 𝟙 _ := by
  apply MorphismProperty.Over.Hom.ext
  exact AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.diagonal_p₁ (overlap P) i
@[simp] theorem diagonal_snd (i : Index P) :
    diagonalEtale P i ≫ overlapSnd P i i = 𝟙 _ := by
  apply MorphismProperty.Over.Hom.ext
  exact AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.diagonal_p₂ (overlap P) i

/-- Any common etale refinement has its canonical map into the overlap. -/
def overlapLift {V : X.Etale} (i j : Index P) (a : V ⟶ i.1) (b : V ⟶ j.1) :
    V ⟶ overlapEtale P i j :=
  MorphismProperty.Over.homMk
    ((overlap P i j).isPullback.lift a.left b.left
      (by exact (MorphismProperty.Over.w a).trans (MorphismProperty.Over.w b).symm))
    (by
      change (overlap P i j).isPullback.lift _ _ _ ≫ (overlap P i j).p = V.hom
      rw [← (overlap P i j).hp₁, ← Category.assoc, IsPullback.lift_fst]
      exact MorphismProperty.Over.w a) (by trivial)

@[simp] theorem overlapLift_fst {V : X.Etale} (i j : Index P)
    (a : V ⟶ i.1) (b : V ⟶ j.1) : overlapLift P i j a b ≫ overlapFst P i j = a := by
  apply MorphismProperty.Over.Hom.ext
  exact IsPullback.lift_fst _ _ _ _
@[simp] theorem overlapLift_snd {V : X.Etale} (i j : Index P)
    (a : V ⟶ i.1) (b : V ⟶ j.1) : overlapLift P i j a b ≫ overlapSnd P i j = b := by
  apply MorphismProperty.Over.Hom.ext
  exact IsPullback.lift_snd _ _ _ _

namespace Character


/-- The global unit carrying the first restricted torsor section to the second on their overlap. -/
def overlapUnit (i j : Index P) : Γ((overlap P i j).pullback, ⊤)ˣ :=
  transportUnit P χ (op (overlapEtale P i j))
    (P.carrier.obj.map (overlapFst P i j).op i.2)
    (P.carrier.obj.map (overlapSnd P i j).op j.2)

/-- Literal global-unit transitions obtained from the original torsor action. -/
def cocycle : AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.Cocycle (overlap P)
    (triple P) where
  unit := overlapUnit P χ
  diagonal i := by
    change pullUnit (diagonalEtale P i).left (transportUnit P χ _ _ _) = 1
    erw [transportUnit_naturality P χ (diagonalEtale P i).op]
    simp only [← Functor.map_comp_apply, ← op_comp, diagonal_fst, diagonal_snd,
      op_id, transportUnit_self]
  cocycle i j k := by
    change pullUnit (triple12 P i j k).left (transportUnit P χ _ _ _) *
      pullUnit (triple23 P i j k).left (transportUnit P χ _ _ _) =
      pullUnit (triple13 P i j k).left (transportUnit P χ _ _ _)
    erw [transportUnit_naturality P χ (triple12 P i j k).op,
      transportUnit_naturality P χ (triple23 P i j k).op,
      transportUnit_naturality P χ (triple13 P i j k).op]
    simp only [← Functor.map_comp_apply, ← op_comp, triple12_fst, triple12_snd,
      triple23_fst, triple23_snd, triple13_fst, triple13_snd]
    exact transportUnit_trans P χ _ _ _ _

/-- The chosen-overlap transition has the literal unique-transport value on every refinement. -/
theorem overlapUnit_pullback {V : X.Etale} (i j : Index P)
    (a : V ⟶ i.1) (b : V ⟶ j.1) :
    pullUnit (overlapLift P i j a b).left (overlapUnit P χ i j) =
      transportUnit P χ (op V) (P.carrier.obj.map a.op i.2) (P.carrier.obj.map b.op j.2) := by
  have hh := transportUnit_naturality P χ (overlapLift P i j a b).op
    (P.carrier.obj.map (overlapFst P i j).op i.2)
    (P.carrier.obj.map (overlapSnd P i j).op j.2)
  change pullUnit (overlapLift P i j a b).left (overlapUnit P χ i j) = _ at hh
  simpa only [← Functor.map_comp_apply, ← op_comp, overlapLift_fst, overlapLift_snd] using hh

/-- All refinement maps of the native descent datum have the same positive transport. -/
theorem descentData_hom {V : X.Etale} (i j : Index P)
    (a : V ⟶ i.1) (b : V ⟶ j.1) :
    (cocycle P χ).descentData.descentData.hom V.hom a.left b.left
      (MorphismProperty.Over.w a) (MorphismProperty.Over.w b) =
    AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.transition a.left b.left
      (transportUnit P χ (op V) (P.carrier.obj.map a.op i.2) (P.carrier.obj.map b.op j.2)) := by
  change Pseudofunctor.DescentData'.pullHom' (cocycle P χ).descentData.hom
    V.hom a.left b.left (MorphismProperty.Over.w a) (MorphismProperty.Over.w b) = _
  have h₁ : (overlapLift P i j a b).left ≫ (overlap P i j).p₁ = a.left :=
    IsPullback.lift_fst _ _ _ _
  have h₂ : (overlapLift P i j a b).left ≫ (overlap P i j).p₂ = b.left :=
    IsPullback.lift_snd _ _ _ _
  rw [Pseudofunctor.DescentData'.pullHom'_eq_pullHom _ _ _ _ (overlapLift P i j a b).left
    (MorphismProperty.Over.w a) (MorphismProperty.Over.w b) h₁ h₂]
  change Pseudofunctor.LocallyDiscreteOpToCat.pullHom
    (AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.transition (overlap P i j).p₁
        (overlap P i j).p₂ (overlapUnit P χ i j))
      (overlapLift P i j a b).left a.left b.left h₁ h₂ = _
  rw [AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.pullHom_transition]
  have hh := congrArg Units.val (overlapUnit_pullback P χ i j a b)
  exact congrArg (AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.transition a.left
      b.left) hh

end Character



/-- The unit-line comparison between pullback of the unit object and the unit object on the
source. -/
def unitIso {Y Z : Scheme.{u}} (f : Y ⟶ Z) :
    (lineBundles.map f.op.toLoc).toFunctor.obj (unitObject Z) ≅ unitObject Y :=
  ObjectProperty.isoMk _ (pullbackUnitIso f)

/-- The line-bundle pullback comparison from a composite morphism to iterated pullback. -/
def compIso {Y Z S : Scheme.{u}} (f : Y ⟶ S) (a : Z ⟶ Y) (q : Z ⟶ S)
    (w : a ≫ f = q) (M : lineBundles.obj (.mk (op S))) :
    (lineBundles.map q.op.toLoc).toFunctor.obj M ≅
      (lineBundles.map a.op.toLoc).toFunctor.obj ((lineBundles.map f.op.toLoc).toFunctor.obj M) :=
  (Cat.Hom.toNatIso (lineBundles.mapComp' f.op.toLoc a.op.toLoc q.op.toLoc (by
    rw [← Quiver.Hom.comp_toLoc, ← op_comp, w]))).app M

theorem unitIso_comp {Y Z S : Scheme.{u}} (f : Y ⟶ S) (a : Z ⟶ Y) (q : Z ⟶ S)
    (w : a ≫ f = q) :
    (compIso f a q w (unitObject S)).hom ≫
      (lineBundles.map a.op.toLoc).toFunctor.map (unitIso f).hom ≫ (unitIso a).hom =
        (unitIso q).hom := by
  subst q
  apply ObjectProperty.hom_ext
  exact Scheme.Modules.pullbackUnitIso_comp_inv a f

/-- Multiplication by the global section `a` on the unit line bundle. -/
def unitScalar (Y : Scheme.{u}) (a : Γ(Y, ⊤)) : unitObject Y ⟶ unitObject Y :=
  ObjectProperty.homMk (AlgebraicGeometry.Scheme.Modules.Invertible.TrivializedPower.scalarMap
      Y (SheafOfModules.unit Y.ringCatSheaf) a)

theorem transition_eq {Y₁ Y₂ Z : Scheme.{u}} (a : Z ⟶ Y₁) (b : Z ⟶ Y₂) (u : Γ(Z, ⊤)) :
    AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.transition a b u = (unitIso a).hom
        ≫ unitScalar Z u ≫ (unitIso b).inv := rfl

@[reassoc] theorem rawRestriction_unit {Y Z S : Scheme.{u}} (f : Y ⟶ S) (a : Z ⟶ Y)
    (q : Z ⟶ S) (w : a ≫ f = q) (M : lineBundles.obj (.mk (op S)))
    (α : (lineBundles.map f.op.toLoc).toFunctor.obj M ⟶ unitObject Y) :
    pullHom (α ≫ (unitIso f).inv) a q q w w ≫ (unitIso q).hom =
      (compIso f a q w M).hom ≫ (lineBundles.map a.op.toLoc).toFunctor.map α ≫
        (unitIso a).hom := by
  have hh : (lineBundles.map a.op.toLoc).toFunctor.map (unitIso f).inv ≫
      (compIso f a q w (unitObject S)).inv ≫ (unitIso q).hom = (unitIso a).hom := by
    rw [← unitIso_comp f a q w]
    simp only [Iso.inv_hom_id_assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id]
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
  change ((compIso f a q w M).hom ≫
    (lineBundles.map a.op.toLoc).toFunctor.map (α ≫ (unitIso f).inv) ≫
      (compIso f a q w (unitObject S)).inv) ≫ _ = _
  simp only [Functor.map_comp, Category.assoc]
  rw [hh]

/-- Native descent compatibility is exactly positive scalar compatibility of frames. -/
theorem chart_comm_to_raw {Y₁ Y₂ Z S : Scheme.{u}}
    (f₁ : Y₁ ⟶ S) (f₂ : Y₂ ⟶ S) (a : Z ⟶ Y₁) (b : Z ⟶ Y₂) (q : Z ⟶ S)
    (ha : a ≫ f₁ = q) (hb : b ≫ f₂ = q)
    (M : lineBundles.obj (.mk (op S)))
    (α : (lineBundles.map f₁.op.toLoc).toFunctor.obj M ⟶ unitObject Y₁)
    (β : (lineBundles.map f₂.op.toLoc).toFunctor.obj M ⟶ unitObject Y₂)
    (u : Γ(Z, ⊤))
    (hc : (lineBundles.map a.op.toLoc).toFunctor.map α ≫
        AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.transition a b u =
      (compIso f₁ a q ha M).inv ≫ (compIso f₂ b q hb M).hom ≫
        (lineBundles.map b.op.toLoc).toFunctor.map β) :
    pullHom (α ≫ (unitIso f₁).inv) a q q ha ha ≫
        AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.transition q q u =
      pullHom (β ≫ (unitIso f₂).inv) b q q hb hb := by
  apply (cancel_mono (unitIso q).hom).mp
  rw [transition_eq]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [rawRestriction_unit_assoc, rawRestriction_unit]
  have hh := congrArg (fun k => (compIso f₁ a q ha M).hom ≫ k ≫ (unitIso b).hom) hc
  simpa only [transition_eq, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Iso.hom_inv_id_assoc] using hh

/-- Positive compatibility of raw frames implies the native descent square. -/
theorem raw_to_chart_comm {Y₁ Y₂ Z S : Scheme.{u}}
    (f₁ : Y₁ ⟶ S) (f₂ : Y₂ ⟶ S) (a : Z ⟶ Y₁) (b : Z ⟶ Y₂) (q : Z ⟶ S)
    (ha : a ≫ f₁ = q) (hb : b ≫ f₂ = q)
    (M : lineBundles.obj (.mk (op S)))
    (α : (lineBundles.map f₁.op.toLoc).toFunctor.obj M ⟶ unitObject Y₁)
    (β : (lineBundles.map f₂.op.toLoc).toFunctor.obj M ⟶ unitObject Y₂)
    (u : Γ(Z, ⊤))
    (hr : pullHom (α ≫ (unitIso f₁).inv) a q q ha ha ≫
        AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.transition q q u =
      pullHom (β ≫ (unitIso f₂).inv) b q q hb hb) :
    (lineBundles.map a.op.toLoc).toFunctor.map α ≫
        AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.transition a b u =
      (compIso f₁ a q ha M).inv ≫ (compIso f₂ b q hb M).hom ≫
        (lineBundles.map b.op.toLoc).toFunctor.map β := by
  apply (cancel_epi (compIso f₁ a q ha M).hom).mp
  apply (cancel_mono (unitIso b).hom).mp
  have hh := congrArg (fun k => k ≫ (unitIso q).hom) hr
  rw [transition_eq] at hh
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at hh
  rw [rawRestriction_unit_assoc, rawRestriction_unit] at hh
  simpa only [transition_eq, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Iso.hom_inv_id_assoc] using hh


/-- Recovery is compatible with every native refinement, with the coherence displayed. -/
theorem recovery_square {ι : Type*} {S : Scheme.{u}} {U : ι → Scheme.{u}}
    {f : ∀ i, U i ⟶ S} {sq : ∀ i j, ChosenPullback (f i) (f j)}
    {sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k)}
    (c : AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.Cocycle sq sq₃) (h :
        EtaleLineBundleDescent.{u})
    (hf : Sieve.ofArrows U f ∈ Scheme.etaleTopology S)
    (i j : ι) {V : Scheme.{u}} (q : V ⟶ S) (a : V ⟶ U i) (b : V ⟶ U j)
    (ha : a ≫ f i = q) (hb : b ≫ f j = q) :
    (lineBundles.map a.op.toLoc).toFunctor.map ((c.recoveryIso h hf).hom.hom i) ≫
      c.descentData.descentData.hom q a b ha hb =
    (compIso (f i) a q ha (c.descendedObject h hf)).inv ≫
      (compIso (f j) b q hb (c.descendedObject h hf)).hom ≫
      (lineBundles.map b.op.toLoc).toFunctor.map ((c.recoveryIso h hf).hom.hom j) := by
  simpa only [Pseudofunctor.toDescentData_obj, Pseudofunctor.DescentData.ofObj_hom,
    compIso, Iso.app_hom, Iso.app_inv, Cat.Hom.toNatIso_hom, Cat.Hom.toNatIso_inv,
    Category.assoc] using (c.recoveryIso h hf).hom.comm q a b ha hb



variable (h : EtaleLineBundleDescent.{u})

/-- A literal frame, regarded in the fixed full rank-one subcategory. -/
def frameChart (L : LineBundle X) (U : X.Etaleᵒᵖ)
    (s : (frameSheaf h X L).obj.obj U) :
    (lineBundles.map U.unop.hom.op.toLoc).toFunctor.obj (ofLineBundle X L) ≅
      unitObject U.unop.left :=
  ObjectProperty.isoMk _ (frameSectionsEquiv h X L U s)

theorem frameChart_raw (L : LineBundle X) (U : X.Etaleᵒᵖ)
    (s : (frameSheaf h X L).obj.obj U) :
    (frameChart h L U s).hom ≫ (unitIso U.unop.hom).inv = frameRawHom h X L U s := by
  apply ObjectProperty.hom_ext
  change (frameHom h X L U s ≫ (pullbackUnitIso U.unop.hom).hom) ≫
    (pullbackUnitIso U.unop.hom).inv = frameHom h X L U s
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

namespace Character


/-- The one bundle descended from the original torsor and its character. -/
def lineBundle : LineBundle X := (cocycle P χ).descended etaleLineBundleDescent (cover_mem P)

/-- The actual local trivialization specified by each original torsor section. -/
def chart (i : Index P) :
    (Scheme.Modules.pullback (coverMap P i)).obj (lineBundle P χ).val ≅
      SheafOfModules.unit (coverObject P i).ringCatSheaf :=
  (cocycle P χ).chart etaleLineBundleDescent (cover_mem P) i

/-- The descent recovery map before identifying the pulled structure module. -/
def chartMap (i : Index P) :
    (lineBundles.map (coverMap P i).op.toLoc).toFunctor.obj ((cocycle P χ).descendedObject
      etaleLineBundleDescent
        (cover_mem P)) ⟶
      unitObject (coverObject P i) :=
  ((cocycle P χ).recoveryIso etaleLineBundleDescent (cover_mem P)).hom.hom i

/-- The descended local chart valued in the pulled-back base unit object,
using the fixed native étale line-bundle descent theorem. -/
def rawChart : Construction.RawChartFamily P
    ((cocycle P χ).descendedObject etaleLineBundleDescent (cover_mem P)) :=
  fun i => chartMap P χ i ≫ (unitIso (coverMap P i)).inv

/-- The original recovered charts satisfy the shared native-object transition relation. -/
theorem rawChart_relations :
    Construction.ChartRelations P
      ((cocycle P χ).descendedObject etaleLineBundleDescent (cover_mem P))
      (rawChart P χ) (transportUnit P χ) := by
  intro V i j a b
  change pullHom (rawChart P χ i) a.left V.hom V.hom
      (MorphismProperty.Over.w a) (MorphismProperty.Over.w a) ≫
      AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.transition V.hom V.hom
        ((transportUnit P χ (op V) (P.carrier.obj.map a.op i.2) (P.carrier.obj.map b.op j.2) :
            Γ(V.left, ⊤)ˣ) : Γ(V.left, ⊤)) =
    pullHom (rawChart P χ j) b.left V.hom V.hom
      (MorphismProperty.Over.w b) (MorphismProperty.Over.w b)
  apply chart_comm_to_raw (coverMap P i) (coverMap P j) a.left b.left V.hom
    (MorphismProperty.Over.w a) (MorphismProperty.Over.w b)
    ((cocycle P χ).descendedObject etaleLineBundleDescent (cover_mem P)) (chartMap P χ i) (chartMap
      P χ j)
  have hh := recovery_square (cocycle P χ) etaleLineBundleDescent (cover_mem P) i j
    V.hom a.left b.left (MorphismProperty.Over.w a) (MorphismProperty.Over.w b)
  rw [descentData_hom P χ i j a b] at hh
  exact hh

theorem rawChart_relation {V : X.Etale} (i j : Index P) (a : V ⟶ i.1) (b : V ⟶ j.1) :
    pullHom (rawChart P χ i) a.left V.hom V.hom
      (MorphismProperty.Over.w a) (MorphismProperty.Over.w a) ≫
      AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.transition V.hom V.hom
        ((transportUnit P χ (op V) (P.carrier.obj.map a.op i.2) (P.carrier.obj.map b.op j.2) :
            Γ(V.left, ⊤)ˣ) : Γ(V.left, ⊤)) =
    pullHom (rawChart P χ j) b.left V.hom V.hom
      (MorphismProperty.Over.w b) (MorphismProperty.Over.w b) :=
  rawChart_relations P χ i j a b

/-- The original torsor section is sent to its own actual descended chart. -/
def toFrame (U : X.Etaleᵒᵖ) (s : P.carrier.obj.obj U) :
    (frameSheaf etaleLineBundleDescent X (lineBundle P χ)).obj.obj U :=
  (frameSectionsEquiv etaleLineBundleDescent X (lineBundle P χ) U).symm (chart P χ ⟨U.unop, s⟩)

@[simp] theorem toFrame_raw (U : X.Etaleᵒᵖ) (s : P.carrier.obj.obj U) :
    frameRawHom etaleLineBundleDescent X (lineBundle P χ) U (toFrame P χ U s) = rawChart P χ
      ⟨U.unop, s⟩ := by
  rfl

/-- Whole raw-chart naturality is supplied by the variable native-object relation factory. -/
theorem rawChart_natural :
    Construction.NaturalFamily P.carrier.obj
      (Construction.rawPresheaf X
        ((cocycle P χ).descendedObject etaleLineBundleDescent (cover_mem P)))
      (Construction.sectionFamily P
        ((cocycle P χ).descendedObject etaleLineBundleDescent (cover_mem P))
        (rawChart P χ)) :=
  Construction.sectionFamily_natural P
    ((cocycle P χ).descendedObject etaleLineBundleDescent (cover_mem P))
    (rawChart P χ) (transportUnit P χ) (rawChart_relations P χ) (transportUnit_self P χ)

/-- The original raw-frame value, through the same native-object view used by the factory. -/
theorem toFrame_raw_native (U : X.Etaleᵒᵖ) (s : P.carrier.obj.obj U) :
    Construction.frameRawHomNative etaleLineBundleDescent X
        ((cocycle P χ).descendedObject etaleLineBundleDescent (cover_mem P)) U
        (toFrame P χ U s) =
      Construction.sectionFamily P
        ((cocycle P χ).descendedObject etaleLineBundleDescent (cover_mem P))
        (rawChart P χ) U s :=
  toFrame_raw P χ U s

/-- Whole naturality uses the same frameRawHom and the actual native raw-chart family. -/
theorem toFrame_natural :
    Construction.NaturalFamily P.carrier.obj
      (frameSheaf etaleLineBundleDescent X (lineBundle P χ)).obj (toFrame P χ) := by
  exact Construction.naturalFamily_of_injective
    (F := P.carrier.obj)
    (G := (frameSheaf etaleLineBundleDescent X (lineBundle P χ)).obj)
    (H := Construction.rawPresheaf X
      ((cocycle P χ).descendedObject etaleLineBundleDescent (cover_mem P)))
    (Construction.frameRawHomNative etaleLineBundleDescent X
      ((cocycle P χ).descendedObject etaleLineBundleDescent (cover_mem P)))
    (Construction.frameRawHomNative_naturality etaleLineBundleDescent X
      ((cocycle P χ).descendedObject etaleLineBundleDescent (cover_mem P)))
    (Construction.frameRawHomNative_injective etaleLineBundleDescent X
      ((cocycle P χ).descendedObject etaleLineBundleDescent (cover_mem P)))
    (toFrame P χ)
    (Construction.sectionFamily P
      ((cocycle P χ).descendedObject etaleLineBundleDescent (cover_mem P))
      (rawChart P χ))
    (toFrame_raw_native P χ) (rawChart_natural P χ)

/-- Restriction sends the frame of an original section to its restricted frame. -/
theorem toFrame_naturality {U V : X.Etaleᵒᵖ} (f : U ⟶ V) (s : P.carrier.obj.obj U) :
    (frameSheaf etaleLineBundleDescent X (lineBundle P χ)).obj.map f (toFrame P χ U s) =
      toFrame P χ V (P.carrier.obj.map f s) :=
  toFrame_natural P χ f s


theorem toFrame_equivariant (U : X.Etaleᵒᵖ) (a : A.obj.obj U) (s : P.carrier.obj.obj U) :
    toFrame P χ U (P.action U a s) = frameAction etaleLineBundleDescent X (lineBundle P χ) U
      (χ.hom.app U a) (toFrame P χ U s) := by
  apply frameRawHom_injective etaleLineBundleDescent X (lineBundle P χ) U
  rw [frameRawHom_action, toFrame_raw, toFrame_raw]
  have hh := rawChart_relation P χ ⟨U.unop, s⟩ ⟨U.unop, P.action U a s⟩
    (𝟙 U.unop) (𝟙 U.unop)
  have ht : transportUnit P χ U s (P.action U a s) = (unitsSections X U (χ.hom.app U a)).toMul := by
    unfold transportUnit
    rw [transport_eq P U s (P.action U a s) a rfl]
  simp only [site_id_left] at hh
  simp only [op_id, op_unop, CategoryTheory.Functor.map_id, types_id_apply] at hh
  erw [pullHom_id, pullHom_id, ht] at hh
  exact hh.symm

/-- An actual equivariant morphism of sheaves, constructed without torsor classification. -/
def frameMap : Scheme.EtaleCohomology.Torsor.Hom χ P (frameTorsor etaleLineBundleDescent X
    (lineBundle P χ)) where
  map := ⟨{ app U := ↾(toFrame P χ U)
            naturality {U V} f := by
              ext s
              exact (toFrame_naturality P χ f s).symm }⟩
  equivariant := toFrame_equivariant P χ

@[simp] theorem toFrame_sections (U : X.Etaleᵒᵖ) (s : P.carrier.obj.obj U) :
    frameSectionsEquiv etaleLineBundleDescent X (lineBundle P χ) U (toFrame P χ U s) =
      chart P χ ⟨U.unop, s⟩ := (frameSectionsEquiv etaleLineBundleDescent X (lineBundle P χ)
        U).apply_symm_apply _

theorem frameMap_chart_comm (L : LineBundle X)
    (r : Scheme.EtaleCohomology.Torsor.Hom χ P (frameTorsor etaleLineBundleDescent X L))
    {V : X.Etale} (i j : Index P) (a : V ⟶ i.1) (b : V ⟶ j.1) :
    (lineBundles.map a.left.op.toLoc).toFunctor.map
      (frameChart etaleLineBundleDescent L (op i.1) (r.map.hom.app (op i.1) i.2)).hom ≫
        AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.transition a.left b.left
          ((transportUnit P χ (op V) (P.carrier.obj.map a.op i.2)
            (P.carrier.obj.map b.op j.2) : Γ(V.left, ⊤)ˣ) : Γ(V.left, ⊤)) =
      (compIso (coverMap P i) a.left V.hom (MorphismProperty.Over.w a) (ofLineBundle X L)).inv ≫
      (compIso (coverMap P j) b.left V.hom (MorphismProperty.Over.w b) (ofLineBundle X L)).hom ≫
      (lineBundles.map b.left.op.toLoc).toFunctor.map
        (frameChart etaleLineBundleDescent L (op j.1) (r.map.hom.app (op j.1) j.2)).hom := by
  apply raw_to_chart_comm (coverMap P i) (coverMap P j) a.left b.left V.hom
    (MorphismProperty.Over.w a) (MorphismProperty.Over.w b) (ofLineBundle X L)
    (frameChart etaleLineBundleDescent L (op i.1) (r.map.hom.app (op i.1) i.2)).hom
    (frameChart etaleLineBundleDescent L (op j.1) (r.map.hom.app (op j.1) j.2)).hom
  erw [frameChart_raw etaleLineBundleDescent L (op i.1) (r.map.hom.app (op i.1) i.2),
    frameChart_raw etaleLineBundleDescent L (op j.1) (r.map.hom.app (op j.1) j.2)]
  have h₁ := congrArg (fun k => k i.2) (r.map.hom.naturality a.op)
  have h₂ := congrArg (fun k => k j.2) (r.map.hom.naturality b.op)
  change r.map.hom.app (op V) (P.carrier.obj.map a.op i.2) =
    (frameSheaf etaleLineBundleDescent X L).obj.map a.op (r.map.hom.app (op i.1) i.2) at h₁
  change r.map.hom.app (op V) (P.carrier.obj.map b.op j.2) =
    (frameSheaf etaleLineBundleDescent X L).obj.map b.op (r.map.hom.app (op j.1) j.2) at h₂
  have hr := r.equivariant (op V)
    (transport P (op V) (P.carrier.obj.map a.op i.2) (P.carrier.obj.map b.op j.2))
    (P.carrier.obj.map a.op i.2)
  change r.map.hom.app (op V) (P.action (op V) _ _) =
    frameAction etaleLineBundleDescent X L (op V) _ (r.map.hom.app (op V) _) at hr
  rw [action_transport, h₁, h₂] at hr
  have hh := congrArg (frameRawHom etaleLineBundleDescent X L (op V)) hr.symm
  rw [frameRawHom_action, frameRawHom_naturality, frameRawHom_naturality,
    presheafHom_map_eq_pullHom, presheafHom_map_eq_pullHom] at hh
  exact hh

/-- Isomorphism of actual native overlap descent data supplied by an equivariant frame map. -/
def frameMapChosenDescentIso (L : LineBundle X)
    (r : Scheme.EtaleCohomology.Torsor.Hom χ P (frameTorsor etaleLineBundleDescent X L)) :
    Pseudofunctor.DescentData'.ofDescentData (overlap P) (triple P)
      ((lineBundles.toDescentData (coverMap P)).obj (ofLineBundle X L)) ≅
        (cocycle P χ).descentData :=
  Pseudofunctor.DescentData'.isoMk
    (fun i => frameChart etaleLineBundleDescent L (op i.1) (r.map.hom.app (op i.1) i.2)) (by
      intro i j
      exact frameMap_chart_comm P χ L r i j (overlapFst P i j) (overlapSnd P i j))

/-- The frame map identifies the full native descent data. -/
def frameMapDescentIso (L : LineBundle X)
    (r : Scheme.EtaleCohomology.Torsor.Hom χ P (frameTorsor etaleLineBundleDescent X L)) :
    (lineBundles.toDescentData (coverMap P)).obj (ofLineBundle X L) ≅
      (cocycle P χ).descentData.descentData :=
  let E := Pseudofunctor.DescentData'.descentDataEquivalence lineBundles (overlap P) (triple P)
  (E.counitIso.app _).symm ≪≫ E.functor.mapIso (frameMapChosenDescentIso P χ L r)

/-- Effective and fully faithful native descent recovers the bundle of a character-equivariant frame
map. -/
def lineBundleIsoOfFrameMap (L : LineBundle X)
    (r : Scheme.EtaleCohomology.Torsor.Hom χ P (frameTorsor etaleLineBundleDescent X
        L)) : (lineBundle P χ).val ≅ L.val :=
  (rankOne.prop (.mk (op X))).fullyFaithfulι.isoEquiv
    ((AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.Cocycle.stackEquivalence
      etaleLineBundleDescent
        (cover_mem P)).fullyFaithfulFunctor.preimageIso
      ((cocycle P χ).recoveryIso etaleLineBundleDescent (cover_mem P) ≪≫ (frameMapDescentIso P χ L
        r).symm))

/-- The bundle recovery carries exactly the original positive charts. -/
theorem lineBundleIsoOfFrameMap_chart (L : LineBundle X)
    (r : Scheme.EtaleCohomology.Torsor.Hom χ P (frameTorsor etaleLineBundleDescent X
        L)) (i : Index P) :
    (Scheme.Modules.pullback (coverMap P i)).map (lineBundleIsoOfFrameMap P χ L r).hom ≫
      (frameSectionsEquiv etaleLineBundleDescent X L (op i.1) (r.map.hom.app (op i.1) i.2)).hom =
        (chart P χ i).hom := by
  have hh := (AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.Cocycle.stackEquivalence
      etaleLineBundleDescent (cover_mem P)).fullyFaithfulFunctor.map_preimage
    ((cocycle P χ).recoveryIso etaleLineBundleDescent (cover_mem P) ≪≫ (frameMapDescentIso P χ L
      r).symm).hom
  have hh' := congrArg (fun k => (k.hom i).hom) hh
  change (Scheme.Modules.pullback (coverMap P i)).map (lineBundleIsoOfFrameMap P χ L r).hom = _
      at hh'
  rw [hh']
  change ((chart P χ i).hom ≫
    ((frameSectionsEquiv etaleLineBundleDescent X L (op i.1) (r.map.hom.app (op i.1) i.2)).inv ≫ 𝟙
      _)) ≫
      (frameSectionsEquiv etaleLineBundleDescent X L (op i.1) (r.map.hom.app (op i.1) i.2)).hom = _
  simp only [Category.comp_id, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end Character
end General


variable (P : Torsor (gm X)) (h : EtaleLineBundleDescent.{u})

/- Identity-character compatibility API on the same original torsor. -/

/-- The unit representing positive transport in the original multiplicative-group torsor. -/
abbrev transportUnit (U : X.Etaleᵒᵖ) (s t : P.carrier.obj.obj U) : Γ(U.unop.left, ⊤)ˣ :=
  Character.transportUnit P (𝟙 (gm X)) U s t

theorem transportUnit_self (U : X.Etaleᵒᵖ) (s : P.carrier.obj.obj U) :
    transportUnit P U s s = 1 :=
  Character.transportUnit_self P (𝟙 (gm X)) U s

theorem transportUnit_trans (U : X.Etaleᵒᵖ) (s t r : P.carrier.obj.obj U) :
    transportUnit P U s t * transportUnit P U t r = transportUnit P U s r :=
  Character.transportUnit_trans P (𝟙 (gm X)) U s t r

theorem transportUnit_naturality {U V : X.Etaleᵒᵖ} (f : U ⟶ V)
    (s t : P.carrier.obj.obj U) :
    pullUnit f.unop.left (transportUnit P U s t) =
      transportUnit P V (P.carrier.obj.map f s) (P.carrier.obj.map f t) :=
  Character.transportUnit_naturality P (𝟙 (gm X)) f s t

/-- The transport unit between the two tautological sections on their chosen overlap. -/
abbrev overlapUnit (i j : Index P) : Γ((overlap P i j).pullback, ⊤)ˣ :=
  Character.overlapUnit P (𝟙 (gm X)) i j

/-- The unit descent cocycle of the original multiplicative-group torsor. -/
abbrev cocycle : AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.Cocycle (overlap P)
    (triple P) :=
  Character.cocycle P (𝟙 (gm X))

theorem overlapUnit_pullback {V : X.Etale} (i j : Index P)
    (a : V ⟶ i.1) (b : V ⟶ j.1) :
    pullUnit (overlapLift P i j a b).left (overlapUnit P i j) =
      transportUnit P (op V) (P.carrier.obj.map a.op i.2) (P.carrier.obj.map b.op j.2) :=
  Character.overlapUnit_pullback P (𝟙 (gm X)) i j a b

theorem descentData_hom {V : X.Etale} (i j : Index P)
    (a : V ⟶ i.1) (b : V ⟶ j.1) :
    (cocycle P).descentData.descentData.hom V.hom a.left b.left
      (MorphismProperty.Over.w a) (MorphismProperty.Over.w b) =
    AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.transition a.left b.left
      (transportUnit P (op V) (P.carrier.obj.map a.op i.2) (P.carrier.obj.map b.op j.2)) :=
  Character.descentData_hom P (𝟙 (gm X)) i j a b

/-- The bundle obtained by descending the identity-character cocycle. -/
abbrev lineBundle (_h : EtaleLineBundleDescent.{u}) :=
  Character.lineBundle P (𝟙 (gm X))

/-- The local trivialization of the associated bundle determined by a torsor section. -/
abbrev chart (_h : EtaleLineBundleDescent.{u}) :=
  Character.chart P (𝟙 (gm X))

/-- The descent recovery map from the associated bundle to the local unit object. -/
abbrev chartMap (_h : EtaleLineBundleDescent.{u}) :=
  Character.chartMap P (𝟙 (gm X))

/-- The recovered local chart valued in the pulled-back base unit object. -/
abbrev rawChart (_h : EtaleLineBundleDescent.{u}) :=
  Character.rawChart P (𝟙 (gm X))

theorem rawChart_relation (h : EtaleLineBundleDescent.{u}) {V : X.Etale} (i j : Index P) (a : V ⟶
    i.1) (b : V ⟶ j.1) :
    pullHom (rawChart P h i) a.left V.hom V.hom
      (MorphismProperty.Over.w a) (MorphismProperty.Over.w a) ≫
      AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.transition V.hom V.hom
        ((transportUnit P (op V) (P.carrier.obj.map a.op i.2) (P.carrier.obj.map b.op j.2) :
            Γ(V.left, ⊤)ˣ) : Γ(V.left, ⊤)) =
    pullHom (rawChart P h j) b.left V.hom V.hom
      (MorphismProperty.Over.w b) (MorphismProperty.Over.w b) :=
  Character.rawChart_relation P (𝟙 (gm X)) i j a b

/-- Send a torsor section to its frame in the associated bundle. -/
abbrev toFrame (_h : EtaleLineBundleDescent.{u}) :=
  Character.toFrame P (𝟙 (gm X))

theorem toFrame_raw (h : EtaleLineBundleDescent.{u}) (U : X.Etaleᵒᵖ) (s : P.carrier.obj.obj
    U) :
    frameRawHom h X (lineBundle P h) U (toFrame P h U s) = rawChart P h ⟨U.unop, s⟩ :=
  Character.toFrame_raw P (𝟙 (gm X)) U s

theorem toFrame_naturality (h : EtaleLineBundleDescent.{u}) {U V : X.Etaleᵒᵖ} (f : U ⟶ V) (s :
    P.carrier.obj.obj U) :
    (frameSheaf h X (lineBundle P h)).obj.map f (toFrame P h U s) =
      toFrame P h V (P.carrier.obj.map f s) :=
  Character.toFrame_naturality P (𝟙 (gm X)) f s

theorem toFrame_equivariant (h : EtaleLineBundleDescent.{u}) (U : X.Etaleᵒᵖ) (a : (gm X).obj.obj U)
    (s : P.carrier.obj.obj U) :
    toFrame P h U (P.action U a s) = frameAction h X (lineBundle P h) U a (toFrame P h U s) :=
  Character.toFrame_equivariant P (𝟙 (gm X)) U a s

/-- The equivariant map from the original torsor to the associated bundle's frame torsor. -/
abbrev frameMap (_h : EtaleLineBundleDescent.{u}) :=
  Character.frameMap P (𝟙 (gm X))

theorem frameMap_chart_comm (h : EtaleLineBundleDescent.{u}) (L : LineBundle X)
    (r : Scheme.EtaleCohomology.Torsor.Hom (𝟙 (gm X)) P (frameTorsor h X L))
    {V : X.Etale} (i j : Index P) (a : V ⟶ i.1) (b : V ⟶ j.1) :
    (lineBundles.map a.left.op.toLoc).toFunctor.map
      (frameChart h L (op i.1) (r.map.hom.app (op i.1) i.2)).hom ≫
        AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.transition a.left b.left
          ((transportUnit P (op V) (P.carrier.obj.map a.op i.2)
            (P.carrier.obj.map b.op j.2) : Γ(V.left, ⊤)ˣ) : Γ(V.left, ⊤)) =
      (compIso (coverMap P i) a.left V.hom (MorphismProperty.Over.w a) (ofLineBundle X L)).inv ≫
      (compIso (coverMap P j) b.left V.hom (MorphismProperty.Over.w b) (ofLineBundle X L)).hom ≫
      (lineBundles.map b.left.op.toLoc).toFunctor.map
        (frameChart h L (op j.1) (r.map.hom.app (op j.1) j.2)).hom :=
  Character.frameMap_chart_comm P (𝟙 (gm X)) L r i j a b

/-- The isomorphism of chosen overlap descent data induced by an equivariant frame map. -/
abbrev frameMapChosenDescentIso (h : EtaleLineBundleDescent.{u}) (L : LineBundle X)
    (r : Scheme.EtaleCohomology.Torsor.Hom (𝟙 (gm X)) P (frameTorsor h X L)) :
    Pseudofunctor.DescentData'.ofDescentData (overlap P) (triple P)
      ((lineBundles.toDescentData (coverMap P)).obj (ofLineBundle X L)) ≅
        (cocycle P).descentData :=
  Character.frameMapChosenDescentIso P (𝟙 (gm X)) L r

/-- Recover a bundle isomorphism from an equivariant map to its frame torsor. -/
abbrev lineBundleIsoOfFrameMap (h : EtaleLineBundleDescent.{u}) (L : LineBundle X)
    (r : Scheme.EtaleCohomology.Torsor.Hom (𝟙 (gm X)) P (frameTorsor h X L)) :
        (lineBundle P h).val ≅ L.val :=
  Character.lineBundleIsoOfFrameMap P (𝟙 (gm X)) L r


/-- The genuine frame torsor of the associated bundle recovers the original torsor. -/
def frameIso : Scheme.EtaleCohomology.Torsor.Iso P (frameTorsor h X
    (lineBundle P h)) := (frameMap P h).toIso


/-- The torsor recovery isomorphism sends a section to its literal descended local chart. -/
@[simp] theorem frameIso_sections (U : X.Etaleᵒᵖ) (s : P.carrier.obj.obj U) :
    frameSectionsEquiv h X (lineBundle P h) U
      ((frameIso P h).carrierIso.hom.hom.app U s) = chart P h ⟨U.unop, s⟩ :=
  (frameSectionsEquiv h X (lineBundle P h) U).apply_symm_apply _

/-- Rebuilding from the genuine frame torsor recovers each actual line bundle. -/
def bundleRecovery (L : LineBundle X) :
    (lineBundle (frameTorsor h X L) h).val ≅ L.val :=
  lineBundleIsoOfFrameMap (frameTorsor h X L) h L
    { map := 𝟙 _
      equivariant := fun _ _ _ => rfl }

/-- Pullback of a global module map is compatible with the native pseudofunctor coherence. -/
theorem pullHom_global {Y Z S : Scheme.{u}} (f : Y ⟶ S) (a : Z ⟶ Y) (q : Z ⟶ S)
    (w : a ≫ f = q) {M N : lineBundles.obj (.mk (op S))} (g : M ⟶ N) :
    pullHom ((lineBundles.map f.op.toLoc).toFunctor.map g) a q q w w =
      (lineBundles.map q.op.toLoc).toFunctor.map g := by
  have hn := (Cat.Hom.toNatIso
    (lineBundles.mapComp' f.op.toLoc a.op.toLoc q.op.toLoc (by
      rw [← Quiver.Hom.comp_toLoc, ← op_comp, w]))).hom.naturality g
  change (lineBundles.map q.op.toLoc).toFunctor.map g ≫ (compIso f a q w N).hom =
    (compIso f a q w M).hom ≫
      (lineBundles.map a.op.toLoc).toFunctor.map ((lineBundles.map f.op.toLoc).toFunctor.map g)
          at hn
  change (compIso f a q w M).hom ≫
    (lineBundles.map a.op.toLoc).toFunctor.map ((lineBundles.map f.op.toLoc).toFunctor.map g) ≫
    (compIso f a q w N).inv = _
  rw [← Category.assoc, ← hn, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Transport of a frame from `L` to `M` by precomposition with the inverse line-bundle
isomorphism. -/
def mapFrame {L M : LineBundle X} (e : L.val ≅ M.val) (U : X.Etaleᵒᵖ)
    (s : (frameSheaf h X L).obj.obj U) : (frameSheaf h X M).obj.obj U :=
  (frameSectionsEquiv h X M U).symm
    ((Scheme.Modules.pullback U.unop.hom).mapIso e.symm ≪≫ frameSectionsEquiv h X L U s)

/-- The inverse of the line-bundle isomorphism `e`, viewed as a morphism in the line-bundle
category. -/
def bundleIsoHom {L M : LineBundle X} (e : L.val ≅ M.val) : ofLineBundle X M ⟶ ofLineBundle X L :=
  ObjectProperty.homMk e.inv

theorem mapFrame_raw {L M : LineBundle X} (e : L.val ≅ M.val) (U : X.Etaleᵒᵖ)
    (s : (frameSheaf h X L).obj.obj U) :
    frameRawHom h X M U (mapFrame h e U s) =
      (lineBundles.map U.unop.hom.op.toLoc).toFunctor.map (bundleIsoHom e) ≫ frameRawHom h X L
          U s := by
  apply ObjectProperty.hom_ext
  change ((Scheme.Modules.pullback U.unop.hom).map e.inv ≫
    (frameHom h X L U s ≫ (pullbackUnitIso U.unop.hom).hom)) ≫
      (pullbackUnitIso U.unop.hom).inv =
        (Scheme.Modules.pullback U.unop.hom).map e.inv ≫ frameHom h X L U s
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem mapFrame_naturality {L M : LineBundle X} (e : L.val ≅ M.val)
    {U V : X.Etaleᵒᵖ} (f : U ⟶ V) (s : (frameSheaf h X L).obj.obj U) :
    (frameSheaf h X M).obj.map f (mapFrame h e U s) =
      mapFrame h e V ((frameSheaf h X L).obj.map f s) := by
  apply frameRawHom_injective h X M V
  rw [frameRawHom_naturality, mapFrame_raw, mapFrame_raw, frameRawHom_naturality]
  have hc := homRestriction_comp (ofLineBundle X M) (ofLineBundle X L)
    (ofLineBundle X (unitBundle X)) ((Scheme.Etale.forget X).map f.unop).op
    ((lineBundles.map U.unop.hom.op.toLoc).toFunctor.map (bundleIsoHom e))
    (frameRawHom h X L U s)
  rw [hc]
  apply congrArg (fun k => k ≫
    (lineBundles.presheafHom (ofLineBundle X L) (ofLineBundle X (unitBundle X))).map
      ((Scheme.Etale.forget X).map f.unop).op (frameRawHom h X L U s))
  rw [presheafHom_map_eq_pullHom]
  exact pullHom_global U.unop.hom f.unop.left V.unop.hom (MorphismProperty.Over.w f.unop)
      (bundleIsoHom e)

theorem mapFrame_equivariant {L M : LineBundle X} (e : L.val ≅ M.val)
    (U : X.Etaleᵒᵖ) (a : (gm X).obj.obj U) (s : (frameSheaf h X L).obj.obj U) :
    mapFrame h e U (frameAction h X L U a s) = frameAction h X M U a (mapFrame h e U s) := by
  apply frameRawHom_injective h X M U
  rw [mapFrame_raw, frameRawHom_action, frameRawHom_action, mapFrame_raw]
  exact (Category.assoc _ _ _).symm

/-- An actual O_X-linear isomorphism gives an actual equivariant frame-sheaf isomorphism. -/
def frameIsoOfBundleIso {L M : LineBundle X} (e : L.val ≅ M.val) :
    Scheme.EtaleCohomology.Torsor.Iso (frameTorsor h X L) (frameTorsor h X M) :=
  (show Scheme.EtaleCohomology.Torsor.Hom (𝟙 (gm X)) (frameTorsor h X L)
      (frameTorsor h X M) from
    { map := ⟨{ app U := ↾(mapFrame h e U)
                naturality {U V} f := by
                  ext s
                  exact (mapFrame_naturality h e f s).symm }⟩
      equivariant := mapFrame_equivariant h e }).toIso

/-- Equivariantly isomorphic torsors have actually isomorphic associated module sheaves. -/
def bundleIsoOfTorsorIso {Q : Torsor (gm X)} (e :
    Scheme.EtaleCohomology.Torsor.Iso P Q) :
    (lineBundle P h).val ≅ (lineBundle Q h).val :=
  lineBundleIsoOfFrameMap P h (lineBundle Q h)
    { map := (e.trans (frameIso Q h)).carrierIso.hom
      equivariant := (e.trans (frameIso Q h)).equivariant }

/-- The associated actual line bundle on isomorphism classes. -/
def torsorClassToBundle : TorsorClass (gm X) → LineBundleClass X :=
  Quotient.map (fun P => lineBundle P h)
    (fun _ _ ⟨e⟩ => ⟨bundleIsoOfTorsorIso _ h e⟩)

/-- The actual frame torsor on isomorphism classes. -/
def bundleClassToTorsor : LineBundleClass X → TorsorClass (gm X) :=
  Quotient.map (frameTorsor h X) (fun _ _ ⟨e⟩ => ⟨frameIsoOfBundleIso h e⟩)

/-- The proved correspondence of actual line-bundle and genuine Gm-torsor isomorphism classes.
No tensor/contracted-sum additivity assertion is made here. -/
def classEquiv (X : Scheme.{u}) : LineBundleClass X ≃ TorsorClass (gm X) where
  toFun := bundleClassToTorsor etaleLineBundleDescent
  invFun := torsorClassToBundle etaleLineBundleDescent
  left_inv := by
    intro c
    refine Quotient.inductionOn c ?_
    intro L
    exact Quotient.sound ⟨bundleRecovery etaleLineBundleDescent L⟩
  right_inv := by
    intro c
    refine Quotient.inductionOn c ?_
    intro P
    exact Quotient.sound ⟨(frameIso P etaleLineBundleDescent).symm⟩

end AlgebraicGeometry.Scheme.Modules.Invertible.AssociatedBundle
