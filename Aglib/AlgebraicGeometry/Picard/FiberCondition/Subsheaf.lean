/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.FppfSections
public import Aglib.AlgebraicGeometry.Sites.FppfCoveringPoints
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Subsheaf

/-!
# Subsheaves of `Pic_{X/S,(fppf)}` cut out by fiber conditions

Let `p : X ⟶ S` be a morphism of schemes. A **fiber condition** `C : FiberCondition p` is a
condition `C.Holds T a t` on a point `t` of an `S`-scheme `T` and a line-bundle class
`a ∈ Pic(X ×_S T)`, meant to depend only on the restriction of `a` to the fiber over `t`, and
required to be

* invariant under base change of the point (`holds_map`): for every morphism `g : T' ⟶ T` over
  `S` and every `t' ∈ T'`, the condition holds at `t'` for `g^* a` if and only if it holds at
  `g t'` for `a`. This is the invariance of Kleiman, *The Picard scheme*, arXiv:math/0504020v1,
  proof of Thm 4.8, p. 28 ("(4.8.1) remains valid after any base change `p : T' → T`"), and it
  contains both the invariance under extension of the residue field (`g` a morphism of residue
  points) and the dependence on the fiber only (`holds_iff_holds_residuePoint`);
* open in locally Noetherian families (`isOpen_setOf_holds`): for `T` locally Noetherian, the set
  of points where it holds is open (Kleiman p. 28, openness of `T'^φ` by EGA III₂ 7.9.11).

Conditions are stated on classes, so they are invariant under isomorphism of line bundles;
`FiberCondition.ofLineBundle` builds one from a condition on line bundles that is invariant
under isomorphism. Two classes with the same image in `Pic_{X/S,(fppf)}(T)` satisfy the condition
at the same points (`holds_iff_of_eq`): they become equal after pullback along an fppf covering
sieve. In particular invariance under tensoring with a class pulled back from `T`
(`holds_add_basePullback_iff`) is a consequence, since such classes vanish in `P_{X/S}(T)`.

For a section `ξ` of `Pic_{X/S,(fppf)}` over `T`, `C.HoldsAt ξ t` says that some local
representative of `ξ` around `t` satisfies `C`. Through every point there is a representative
along a flat morphism locally of finite presentation (`exists_flat_app_eq`). The condition does
not depend on the representative (`holdsAt_iff`; this is the overlap argument of Kleiman p. 28
with the covering `T'' → T' ×_T T'`), and it is compatible with base change (`holdsAt_map`).

The **subsheaf `Pic^C`** is `C.subfunctor`. Kleiman defines `P^φ` as "the étale subsheaf
associated to the presheaf whose `T`-points are represented by the invertible sheaves `L` on
`X_T`" satisfying (4.8.1) at every point of `T` (p. 28; `P^φ_m` on p. 29 likewise). Here the
presheaf is the image presheaf `C.imageSubfunctor` of classes satisfying the condition at every
point, and `C.subfunctor` is its fppf sheafification inside `Pic_{X/S,(fppf)}` on `Over S`,
Mathlib's `Subfunctor.sheafify`. It is an fppf sheaf (`isSheaf_subfunctor`), and its sections are
exactly those satisfying the condition at every point (`mem_subfunctor_iff`). The conjunction
`C ⊓ D` of two conditions cuts out `Pic^C ∩ Pic^D` (`subfunctor_inf`). Kleiman's `P^φ_m`
(p. 29) has this form, with `D` the pointwise (4.8.3), which he shows equivalent to (4.8.2); for
the stratum `Pic^φ_m` of the Picard plan (`docs/PICARD_PLAN.md`, Representability, step 2), `D` is
(4.8.3) together with `H^0(X_t, L_t(m)) ≠ 0`, a single condition, since the nonvanishing condition
alone is not open. No hypothesis on `p`, on `S` or on the test scheme is used here; openness on
locally Noetherian test schemes is in [OpenSubfunctor](OpenSubfunctor.lean).

The fppf covering-point lemma is `Scheme.exists_flat_mem_range_of_mem_fppfTopology`
([Sites/FppfCoveringPoints](../../Sites/FppfCoveringPoints.lean)).
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme

namespace RelativePicard

open Scheme.Modules.Invertible

variable {S X : Scheme.{u}} (p : X ⟶ S)

/-- **Fiber condition** for the family `X ×_S T ⟶ T`: a condition `Holds T a t` on a point `t` of
an `S`-scheme `T` and a class `a ∈ Pic(X ×_S T)`, invariant under base change of the point and
open in locally Noetherian families (Kleiman, *The Picard scheme*, arXiv:math/0504020v1, proof of
Thm 4.8, p. 28). -/
structure FiberCondition where
  /-- The condition at the point `t` of `T` for the class `a ∈ Pic(X ×_S T)`, that is, for the
  restriction of `a` to the fiber `X_t` over the residue field `κ(t)`. -/
  Holds : ∀ T : Over S, (familyPicardFunctor p).obj (op T) → T.left → Prop
  /-- Invariance under base change of the point: for `g : T' ⟶ T` over `S` and `t' ∈ T'`, the
  condition holds at `t'` for `g^* a` if and only if it holds at `g t'` for `a`. -/
  holds_map : ∀ {T T' : Over S} (g : T' ⟶ T) (a : (familyPicardFunctor p).obj (op T))
    (t' : T'.left), Holds T' ((familyPicardFunctor p).map g.op a) t' ↔ Holds T a (g.left t')
  /-- Openness in locally Noetherian families. -/
  isOpen_setOf_holds : ∀ T : Over S, IsLocallyNoetherian T.left →
    ∀ a : (familyPicardFunctor p).obj (op T), IsOpen {t : T.left | Holds T a t}

namespace FiberCondition

variable {p}

/-- A fiber condition from a condition on line bundles that is invariant under isomorphism. The
pullback along `g : T' ⟶ T` is pullback along `(familyScheme p).map g`, Mathlib's
`pullback.map p T'.hom p T.hom (𝟙 X) g.left (𝟙 S)`. -/
def ofLineBundle (P : ∀ T : Over S, LineBundle (pullback p T.hom) → T.left → Prop)
    (hiso : ∀ (T : Over S) (L L' : LineBundle (pullback p T.hom)), Nonempty (L.val ≅ L'.val) →
      ∀ t : T.left, P T L t ↔ P T L' t)
    (hmap : ∀ {T T' : Over S} (g : T' ⟶ T) (L : LineBundle (pullback p T.hom)) (t' : T'.left),
      P T' (pullbackLineBundle ((familyScheme p).map g) L) t' ↔ P T L (g.left t'))
    (hopen : ∀ T : Over S, IsLocallyNoetherian T.left → ∀ L : LineBundle (pullback p T.hom),
      IsOpen {t : T.left | P T L t}) : FiberCondition p where
  Holds T a t := Quotient.liftOn (a : PicardGroup (pullback p T.hom)) (fun L ↦ P T L t)
    (fun L L' h ↦ propext (hiso T L L' h t))
  holds_map g a t' := by
    induction (a : PicardGroup _) using Quotient.inductionOn with | h L =>
    exact hmap g L t'
  isOpen_setOf_holds T hT a := by
    induction (a : PicardGroup _) using Quotient.inductionOn with | h L =>
    exact hopen T hT L

theorem ofLineBundle_holds_classOf (P : ∀ T : Over S, LineBundle (pullback p T.hom) → T.left → Prop)
    (hiso : ∀ (T : Over S) (L L' : LineBundle (pullback p T.hom)), Nonempty (L.val ≅ L'.val) →
      ∀ t : T.left, P T L t ↔ P T L' t)
    (hmap : ∀ {T T' : Over S} (g : T' ⟶ T) (L : LineBundle (pullback p T.hom)) (t' : T'.left),
      P T' (pullbackLineBundle ((familyScheme p).map g) L) t' ↔ P T L (g.left t'))
    (hopen : ∀ T : Over S, IsLocallyNoetherian T.left → ∀ L : LineBundle (pullback p T.hom),
      IsOpen {t : T.left | P T L t}) (T : Over S) (L : LineBundle (pullback p T.hom))
    (t : T.left) :
    (ofLineBundle P hiso hmap hopen).Holds T (classOf _ L) t ↔ P T L t :=
  Iff.rfl

/-- The residue point `Spec κ(t) ⟶ T` of `t ∈ T`, as a morphism of `S`-schemes. -/
abbrev residuePoint (T : Over S) (t : T.left) :
    Over.mk (T.left.fromSpecResidueField t ≫ T.hom) ⟶ T :=
  Over.homMk (T.left.fromSpecResidueField t)

variable (C : FiberCondition p)

/-- A fiber condition depends only on the fiber: it holds at `t` for `a` if and only if it holds
for the restriction of `a` to `X ×_S Spec κ(t)` (at the point of `Spec κ(t)`). -/
theorem holds_iff_holds_residuePoint {T : Over S} (a : (familyPicardFunctor p).obj (op T))
    (t : T.left) (s : Spec (T.left.residueField t)) :
    C.Holds T a t ↔ C.Holds _ ((familyPicardFunctor p).map (residuePoint T t).op a) s := by
  rw [C.holds_map]
  change C.Holds T a t ↔ C.Holds T a (T.left.fromSpecResidueField t s)
  rw [Scheme.fromSpecResidueField_apply]

/-- **Key lemma.** Two classes on `X ×_S W` with the same image in `Pic_{X/S,(fppf)}(W)` satisfy a
fiber condition at the same points: they agree after pullback along an fppf covering sieve
(local injectivity of `quotientProjection p ≫ toFppfPicardSheaf p`), and the condition is
invariant under base change of the point. -/
theorem holds_iff_of_eq {W : Over S} {a b : (familyPicardFunctor p).obj (op W)}
    (h : (quotientProjection p ≫ toFppfPicardSheaf p).app (op W) a =
      (quotientProjection p ≫ toFppfPicardSheaf p).app (op W) b) (w : W.left) :
    C.Holds W a w ↔ C.Holds W b w := by
  have hmem := Presheaf.equalizerSieve_mem (Scheme.fppfTopology.over S)
    (quotientProjection p ≫ toFppfPicardSheaf p) a b h
  obtain ⟨V, g, hg, -, -, v, rfl⟩ := Scheme.exists_flat_mem_range_of_mem_fppfTopology_over hmem w
  have hab : (familyPicardFunctor p).map (Over.homMk g : Over.mk (g ≫ W.hom) ⟶ W).op a =
      (familyPicardFunctor p).map (Over.homMk g : Over.mk (g ≫ W.hom) ⟶ W).op b := hg
  have ha := C.holds_map (Over.homMk g : Over.mk (g ≫ W.hom) ⟶ W) a v
  have hb := C.holds_map (Over.homMk g : Over.mk (g ≫ W.hom) ⟶ W) b v
  rw [hab] at ha
  exact ha.symm.trans hb

/-- Invariance under tensor product with a class pulled back from the base: classes from `Pic(T)`
vanish in `P_{X/S}(T)`. -/
theorem holds_add_basePullback_iff {T : Over S} (a : (familyPicardFunctor p).obj (op T))
    (c : (basePicardFunctor S).obj (op T)) (t : T.left) :
    C.Holds T (a + (basePullback p).app (op T) c) t ↔ C.Holds T a t := by
  refine C.holds_iff_of_eq ?_ t
  have h0 : (quotientProjection p).app (op T) ((basePullback p).app (op T) c) = 0 :=
    quotientProjection_basePullback_apply p (op T) c
  rw [NatTrans.comp_app, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, map_add, h0,
    add_zero]

/-- The condition at a point `t ∈ T` for a section `ξ` of `Pic_{X/S,(fppf)}` over `T`: some
representative `a ∈ Pic(X ×_S V)` of the restriction of `ξ` to some `h : V ⟶ T` satisfies the
condition at some point `v` over `t`. By `holdsAt_iff` every such representative then does. -/
def HoldsAt {T : Over S} (ξ : (fppfPicardSheaf p).obj.obj (op T)) (t : T.left) : Prop :=
  ∃ (V : Over S) (h : V ⟶ T) (v : V.left) (a : (familyPicardFunctor p).obj (op V)),
    h.left v = t ∧
      (quotientProjection p ≫ toFppfPicardSheaf p).app (op V) a =
        (fppfPicardSheaf p).obj.map h.op ξ ∧ C.Holds V a v

/-- **Independence of the representative.** If `a ∈ Pic(X ×_S V)` represents the restriction of
`ξ` along `h : V ⟶ T`, then `ξ` satisfies the condition at `h v` exactly when `a` satisfies it
at `v`. This is the overlap argument of Kleiman, arXiv:math/0504020v1, p. 28: two
representatives are compared on `V ×_T V'`, where they have the same image in the fppf sheaf. -/
theorem holdsAt_iff {T V : Over S} (ξ : (fppfPicardSheaf p).obj.obj (op T)) (h : V ⟶ T)
    (a : (familyPicardFunctor p).obj (op V))
    (ha : (quotientProjection p ≫ toFppfPicardSheaf p).app (op V) a =
      (fppfPicardSheaf p).obj.map h.op ξ) (v : V.left) :
    C.HoldsAt ξ (h.left v) ↔ C.Holds V a v := by
  refine ⟨fun ⟨V', h', v', a', hv', ha', hC⟩ ↦ ?_, fun hC ↦ ⟨V, h, v, a, rfl, ha, hC⟩⟩
  obtain ⟨q, hq₁, hq₂⟩ :=
    Scheme.Pullback.exists_preimage_pullback (f := h.left) (g := h'.left) v v' hv'.symm
  let Q : Over S := Over.mk (pullback.fst h.left h'.left ≫ V.hom)
  let q₁ : Q ⟶ V := Over.homMk (pullback.fst h.left h'.left)
  let q₂ : Q ⟶ V' := Over.homMk (pullback.snd h.left h'.left) (by
    change pullback.snd h.left h'.left ≫ V'.hom = pullback.fst h.left h'.left ≫ V.hom
    rw [← Over.w h', ← Over.w h, ← Category.assoc, ← Category.assoc, pullback.condition])
  have hq : q₁ ≫ h = q₂ ≫ h' := by
    ext
    exact pullback.condition
  have e : (quotientProjection p ≫ toFppfPicardSheaf p).app (op Q)
        ((familyPicardFunctor p).map q₁.op a) =
      (quotientProjection p ≫ toFppfPicardSheaf p).app (op Q)
        ((familyPicardFunctor p).map q₂.op a') := by
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, ha, ha',
      ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← Functor.map_comp, ← op_comp, ← op_comp, hq]
  have key := C.holds_iff_of_eq e q
  rw [C.holds_map, C.holds_map] at key
  have e₁ : q₁.left q = v := hq₁
  have e₂ : q₂.left q = v' := hq₂
  rw [e₁, e₂] at key
  exact key.mpr hC

/-- **Base change.** For `g : T' ⟶ T` over `S`, the restriction of `ξ` to `T'` satisfies the
condition at `t'` if and only if `ξ` satisfies it at `g t'`. -/
theorem holdsAt_map {T T' : Over S} (g : T' ⟶ T) (ξ : (fppfPicardSheaf p).obj.obj (op T))
    (t' : T'.left) :
    C.HoldsAt ((fppfPicardSheaf p).obj.map g.op ξ) t' ↔ C.HoldsAt ξ (g.left t') := by
  constructor
  · rintro ⟨V, h, v, a, rfl, ha, hC⟩
    refine ⟨V, h ≫ g, v, a, rfl, ?_, hC⟩
    rw [ha, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  · rintro ⟨V, h, v, a, hv, ha, hC⟩
    obtain ⟨q, hq₁, hq₂⟩ :=
      Scheme.Pullback.exists_preimage_pullback (f := h.left) (g := g.left) v t' hv
    let Q : Over S := Over.mk (pullback.fst h.left g.left ≫ V.hom)
    let q₁ : Q ⟶ V := Over.homMk (pullback.fst h.left g.left)
    let q₂ : Q ⟶ T' := Over.homMk (pullback.snd h.left g.left) (by
      change pullback.snd h.left g.left ≫ T'.hom = pullback.fst h.left g.left ≫ V.hom
      rw [← Over.w g, ← Over.w h, ← Category.assoc, ← Category.assoc, pullback.condition])
    have hq : q₁ ≫ h = q₂ ≫ g := by
      ext
      exact pullback.condition
    refine ⟨Q, q₂, q, (familyPicardFunctor p).map q₁.op a, hq₂, ?_, ?_⟩
    · rw [NatTrans.naturality_apply, ha, ← ConcreteCategory.comp_apply,
        ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← Functor.map_comp, ← op_comp,
        ← op_comp, hq]
    · rw [C.holds_map]
      have e₁ : q₁.left q = v := hq₁
      rw [e₁]
      exact hC

/-- A section that is the image of a class satisfies the condition exactly where the class
does. -/
theorem holdsAt_app_iff {T : Over S} (a : (familyPicardFunctor p).obj (op T)) (t : T.left) :
    C.HoldsAt ((quotientProjection p ≫ toFppfPicardSheaf p).app (op T) a) t ↔ C.Holds T a t := by
  have h := C.holdsAt_iff ((quotientProjection p ≫ toFppfPicardSheaf p).app (op T) a) (𝟙 T) a
    (by rw [op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]) t
  exact h

/-- Every section of `Pic_{X/S,(fppf)}` over `T` is represented by a class along some flat
morphism `h : V ⟶ T`, locally of finite presentation, through any given point of `T`. -/
theorem exists_flat_app_eq {T : Over S} (ξ : (fppfPicardSheaf p).obj.obj (op T)) (t : T.left) :
    ∃ (V : Scheme.{u}) (h : V ⟶ T.left)
      (a : (familyPicardFunctor p).obj (op (Over.mk (h ≫ T.hom)))),
      Flat h ∧ LocallyOfFinitePresentation h ∧ t ∈ Set.range h ∧
        (quotientProjection p ≫ toFppfPicardSheaf p).app _ a =
          (fppfPicardSheaf p).obj.map (Over.homMk h : Over.mk (h ≫ T.hom) ⟶ T).op ξ := by
  obtain ⟨V, h, ⟨a, ha⟩, hflat, hlfp, ht⟩ :=
    Scheme.exists_flat_mem_range_of_mem_fppfTopology_over
      (Presheaf.imageSieve_mem (Scheme.fppfTopology.over S)
        (quotientProjection p ≫ toFppfPicardSheaf p) ξ) t
  exact ⟨V, h, a, hflat, hlfp, ht, ha⟩

/-- The conjunction of two fiber conditions (Kleiman, arXiv:math/0504020v1, p. 29: `P^φ_m` is cut
out by (4.8.1) together with (4.8.2)). -/
instance : Min (FiberCondition p) where
  min C D :=
    { Holds T a t := C.Holds T a t ∧ D.Holds T a t
      holds_map g a t' := and_congr (C.holds_map g a t') (D.holds_map g a t')
      isOpen_setOf_holds T hT a :=
        (C.isOpen_setOf_holds T hT a).inter (D.isOpen_setOf_holds T hT a) }

theorem inf_holds (D : FiberCondition p) {T : Over S} (a : (familyPicardFunctor p).obj (op T))
    (t : T.left) : (C ⊓ D).Holds T a t ↔ C.Holds T a t ∧ D.Holds T a t :=
  Iff.rfl

/-- A section satisfies the conjunction of two conditions at a point if and only if it satisfies
both: they are tested on a common representative (`exists_flat_app_eq`). -/
theorem inf_holdsAt (D : FiberCondition p) {T : Over S}
    (ξ : (fppfPicardSheaf p).obj.obj (op T)) (t : T.left) :
    (C ⊓ D).HoldsAt ξ t ↔ C.HoldsAt ξ t ∧ D.HoldsAt ξ t := by
  obtain ⟨V, h, a, -, -, ⟨v, rfl⟩, ha⟩ := exists_flat_app_eq ξ t
  exact ((C ⊓ D).holdsAt_iff ξ _ a ha v).trans
    (and_congr (C.holdsAt_iff ξ _ a ha v) (D.holdsAt_iff ξ _ a ha v)).symm

/-- The sub-presheaf of the underlying presheaf of sets of `Pic_{X/S,(fppf)}` of the images of
classes satisfying the condition at every point. -/
def imageSubfunctor :
    Subfunctor ((fppfPicardSheaf p).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}) where
  obj T := {ξ | ∃ a : (familyPicardFunctor p).obj T,
    (quotientProjection p ≫ toFppfPicardSheaf p).app T a = ξ ∧ ∀ t, C.Holds T.unop a t}
  map {T T'} f := by
    rintro _ ⟨a, rfl, ha⟩
    refine ⟨(familyPicardFunctor p).map f a, NatTrans.naturality_apply _ f a, fun t ↦ ?_⟩
    exact (C.holds_map f.unop a t).2 (ha _)

/-- **The subsheaf `Pic^C ⊂ Pic_{X/S,(fppf)}`** (Kleiman, arXiv:math/0504020v1, p. 28, definition
of `P^φ`, and p. 29, definition of `P^φ_m`, for the fppf topology): the subsheaf associated to the
presheaf of classes satisfying the condition at every point, that is, the sections that are
fppf-locally images of such classes. -/
def subfunctor :
    Subfunctor ((fppfPicardSheaf p).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
  C.imageSubfunctor.sheafify (Scheme.fppfTopology.over S)

/-- `Pic^C` is an fppf sheaf. -/
theorem isSheaf_subfunctor :
    Presieve.IsSheaf (Scheme.fppfTopology.over S) C.subfunctor.toFunctor :=
  C.imageSubfunctor.sheafify_isSheaf (isSheaf_fppfPicardSheaf_forget p)

/-- **Pointwise description of `Pic^C`.** A section of `Pic_{X/S,(fppf)}` over any `S`-scheme `T`
lies in `Pic^C` if and only if it satisfies the condition at every point of `T`. -/
theorem mem_subfunctor_iff {T : Over S} (ξ : (fppfPicardSheaf p).obj.obj (op T)) :
    ξ ∈ C.subfunctor.obj (op T) ↔ ∀ t : T.left, C.HoldsAt ξ t := by
  change C.imageSubfunctor.sieveOfSection ξ ∈ (Scheme.fppfTopology.over S) T ↔ _
  constructor
  · intro hξ t
    obtain ⟨V, h, ⟨a, ha, hC⟩, -, -, v, rfl⟩ :=
      Scheme.exists_flat_mem_range_of_mem_fppfTopology_over hξ t
    exact ⟨_, _, v, a, rfl, ha, hC v⟩
  · intro hξ
    refine (Scheme.fppfTopology.over S).superset_covering ?_
      (Presheaf.imageSieve_mem (Scheme.fppfTopology.over S)
        (quotientProjection p ≫ toFppfPicardSheaf p) ξ)
    rintro V f ⟨a, ha⟩
    change ((fppfPicardSheaf p).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}).map f.op ξ ∈
      C.imageSubfunctor.obj (op V)
    exact ⟨a, ha, fun v ↦ (C.holdsAt_iff ξ f a ha v).mp (hξ _)⟩

/-- An image of a class lies in `Pic^C` if and only if the class satisfies the condition at
every point. -/
theorem app_mem_subfunctor_iff {T : Over S} (a : (familyPicardFunctor p).obj (op T)) :
    (quotientProjection p ≫ toFppfPicardSheaf p).app (op T) a ∈ C.subfunctor.obj (op T) ↔
      ∀ t : T.left, C.Holds T a t := by
  rw [mem_subfunctor_iff]
  exact forall_congr' fun t ↦ C.holdsAt_app_iff a t

/-- `Pic^{C ⊓ D} = Pic^C ∩ Pic^D`. -/
theorem subfunctor_inf (D : FiberCondition p) :
    (C ⊓ D).subfunctor = C.subfunctor ⊓ D.subfunctor := by
  ext T ξ
  induction T using Opposite.rec with | op T =>
  change ξ ∈ (C ⊓ D).subfunctor.obj (op T) ↔
    ξ ∈ C.subfunctor.obj (op T) ∧ ξ ∈ D.subfunctor.obj (op T)
  rw [mem_subfunctor_iff, mem_subfunctor_iff, mem_subfunctor_iff]
  simp only [inf_holdsAt, forall_and]

end FiberCondition

end RelativePicard

end AlgebraicGeometry.Scheme
