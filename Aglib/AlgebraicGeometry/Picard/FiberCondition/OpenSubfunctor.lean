/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.FiberCondition.Subsheaf
public import Aglib.AlgebraicGeometry.Properties.Noetherian.LocallyNoetherianOver
public import Aglib.AlgebraicGeometry.Sites.OverRepresentability
public import Aglib.AlgebraicGeometry.Sites.OverRepresentability.LocallyNoetherian

/-!
# Subsheaves of `Pic_{X/S,(fppf)}` cut out by fiber conditions are open

Let `p : X ⟶ S` be a morphism of schemes and `C : FiberCondition p` a fiber condition
([Subsheaf](Subsheaf.lean)), with associated fppf subsheaf `Pic^C = C.subfunctor` of
`Pic_{X/S,(fppf)}`. This file proves that `Pic^C ⟶ Pic_{X/S,(fppf)}` is an open immersion of
functors on locally Noetherian test schemes (Kleiman, *The Picard scheme*, arXiv:math/0504020v1,
proof of Thm 4.8, pp. 28–29, from "Fix a map `T → P`" to "Thus `T^φ` and `P^φ ×_P T` have the
same `R`-points", with fppf coverings in place of étale ones).

For an `S`-scheme `T` with `T` locally Noetherian and a section `ξ` of `Pic_{X/S,(fppf)}` over
`T`:

* the points of `T` where `ξ` satisfies the condition form an open subset
  (`isOpen_setOf_holdsAt`), the open subscheme `U_ξ = C.opens ξ` (Kleiman's `T^φ`);
* a morphism `g : Z ⟶ T` over `S`, from any `S`-scheme `Z`, pulls `ξ` back into `Pic^C` if and only
  if `g` factors through `U_ξ` (`map_mem_subfunctor_iff`);
* if the failure of the condition is also open in locally Noetherian families, `U_ξ` is open and
  closed (`isClopen_setOf_holdsAt_of_isClosed`); this is the case needed for the strata `Pic^φ`
  of Kleiman's (4.8.1), whose condition is open and closed by local constancy of the Euler
  characteristic (supplied separately).

In the form consumed by Zariski-local representability on locally Noetherian test schemes
(`Scheme.LocalRepresentability`; Stacks, Tag 01JJ, with open subfunctors in the sense of Tag
01JI): the restriction `C.locallyNoetherianSubfunctor` of `Pic^C` to
`Scheme.LocallyNoetherianOver S` is an open subfunctor (`isOpenSubfunctor`), and for each `T` and
`ξ` the open subscheme `U_ξ` represents `Pic^C ×_{Pic} h_T`, the subfunctor
`C.preimageSubfunctor ξ` of the functor of points of `T` (`preimageRepresentableBy`).

Kleiman descends the open locus `T'^φ` of a representative along the étale covering
`T' → T`. Here the open is described intrinsically, as the set of points where `ξ` satisfies the
condition (`FiberCondition.HoldsAt`); its preimage under each fppf morphism `h : V ⟶ T` along which
`ξ` has a representative `a` is the open locus of `a` (`holdsAt_iff`), and fppf morphisms are open
maps. The fppf morphisms `V ⟶ T` are locally of finite type, so `V` is locally Noetherian, which
is where the hypothesis on `T` is used. No hypothesis on `p` or `S` is used.

For families of conditions, `opens_inf` (the open of `C ⊓ D` is the intersection),
`opens_mono`, `disjoint_opens` and `iSup_opens_eq_top` record intersections, monotonicity,
disjointness and covering of the opens from the corresponding pointwise properties of the
conditions (Kleiman p. 29: the `T^φ` are disjoint and cover `T`; the `P^φ_m ×_{P^φ} T` form a
nested sequence of opens with union `T`).
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.RelativePicard.FiberCondition

open LocalRepresentability

variable {S X : Scheme.{u}} {p : X ⟶ S} (C : FiberCondition p)

/-- **Openness** (Kleiman, arXiv:math/0504020v1, p. 28: `T^φ ⊂ T` is open). For `T` locally
Noetherian, the points of `T` where a section `ξ` of `Pic_{X/S,(fppf)}` satisfies the condition
form an open subset. -/
theorem isOpen_setOf_holdsAt {T : Over S} [IsLocallyNoetherian T.left]
    (ξ : (fppfPicardSheaf p).obj.obj (op T)) : IsOpen {t : T.left | C.HoldsAt ξ t} := by
  rw [isOpen_iff_forall_mem_open]
  intro t ht
  obtain ⟨V, h, a, hflat, hlfp, ⟨v, rfl⟩, ha⟩ := exists_flat_app_eq ξ t
  have : Flat h := hflat
  have : LocallyOfFinitePresentation h := hlfp
  have hV : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian h
  refine ⟨h '' {v' | C.Holds _ a v'}, ?_, h.isOpenMap _ (C.isOpen_setOf_holds _ hV a),
    v, (C.holdsAt_iff ξ _ a ha v).mp ht, rfl⟩
  rintro _ ⟨v', hv', rfl⟩
  exact (C.holdsAt_iff ξ _ a ha v').mpr hv'

/-- If the failure of the condition is also open in locally Noetherian families, then for `T`
locally Noetherian the points where `ξ` satisfies the condition form a closed subset. -/
theorem isClosed_setOf_holdsAt_of_isClosed
    (hC : ∀ T : Over S, IsLocallyNoetherian T.left →
      ∀ a : (familyPicardFunctor p).obj (op T), IsClosed {t : T.left | C.Holds T a t})
    {T : Over S} [IsLocallyNoetherian T.left] (ξ : (fppfPicardSheaf p).obj.obj (op T)) :
    IsClosed {t : T.left | C.HoldsAt ξ t} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro t ht
  obtain ⟨V, h, a, hflat, hlfp, ⟨v, rfl⟩, ha⟩ := exists_flat_app_eq ξ t
  have : Flat h := hflat
  have : LocallyOfFinitePresentation h := hlfp
  have hV : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian h
  refine ⟨h '' {v' | ¬ C.Holds _ a v'}, ?_, h.isOpenMap _ (hC _ hV a).isOpen_compl,
    v, fun hv ↦ ht ((C.holdsAt_iff ξ _ a ha v).mpr hv), rfl⟩
  rintro _ ⟨v', hv', rfl⟩ hv''
  exact hv' ((C.holdsAt_iff ξ _ a ha v').mp hv'')

/-- **The open and closed variant.** If the condition and its failure are both open in locally
Noetherian families, then for `T` locally Noetherian the points where `ξ` satisfies the condition
form an open and closed subset (Kleiman, arXiv:math/0504020v1, p. 29: the `T^φ` are disjoint and
cover `T`, so each is open and closed). -/
theorem isClopen_setOf_holdsAt_of_isClosed
    (hC : ∀ T : Over S, IsLocallyNoetherian T.left →
      ∀ a : (familyPicardFunctor p).obj (op T), IsClosed {t : T.left | C.Holds T a t})
    {T : Over S} [IsLocallyNoetherian T.left] (ξ : (fppfPicardSheaf p).obj.obj (op T)) :
    IsClopen {t : T.left | C.HoldsAt ξ t} :=
  ⟨C.isClosed_setOf_holdsAt_of_isClosed hC ξ, C.isOpen_setOf_holdsAt ξ⟩

/-- The open subscheme `U_ξ ⊆ T` of points where a section `ξ` of `Pic_{X/S,(fppf)}` satisfies
the condition, for `T` locally Noetherian (Kleiman's `T^φ`, arXiv:math/0504020v1, p. 28). -/
def opens {T : Over S} [IsLocallyNoetherian T.left] (ξ : (fppfPicardSheaf p).obj.obj (op T)) :
    T.left.Opens :=
  ⟨{t | C.HoldsAt ξ t}, C.isOpen_setOf_holdsAt ξ⟩

theorem mem_opens_iff {T : Over S} [IsLocallyNoetherian T.left]
    (ξ : (fppfPicardSheaf p).obj.obj (op T)) (t : T.left) : t ∈ C.opens ξ ↔ C.HoldsAt ξ t :=
  Iff.rfl

/-- The open of the conjunction of two conditions is the intersection of their opens. -/
theorem opens_inf (D : FiberCondition p) {T : Over S} [IsLocallyNoetherian T.left]
    (ξ : (fppfPicardSheaf p).obj.obj (op T)) : (C ⊓ D).opens ξ = C.opens ξ ⊓ D.opens ξ :=
  SetLike.ext fun t ↦ C.inf_holdsAt D ξ t

/-- **Open immersion** (Kleiman, arXiv:math/0504020v1, pp. 28–29: `T^φ` represents
`P^φ ×_P T`). For `T` locally Noetherian, a morphism `g : Z ⟶ T` over `S`, from any `S`-scheme
`Z`, pulls a section `ξ` of `Pic_{X/S,(fppf)}` back into `Pic^C` if and only if `g` factors through
the open subscheme `U_ξ`. -/
theorem map_mem_subfunctor_iff {T : Over S} [IsLocallyNoetherian T.left]
    (ξ : (fppfPicardSheaf p).obj.obj (op T)) {Z : Over S} (g : Z ⟶ T) :
    (fppfPicardSheaf p).obj.map g.op ξ ∈ C.subfunctor.obj (op Z) ↔
      g.left ⁻¹ᵁ C.opens ξ = ⊤ := by
  rw [C.mem_subfunctor_iff, eq_top_iff]
  constructor
  · intro h z _
    exact (C.holdsAt_map g ξ z).mp (h z)
  · intro h z
    exact (C.holdsAt_map g ξ z).mpr (h (show z ∈ (⊤ : Z.left.Opens) from trivial))

/-- A section lies in `Pic^C` exactly when its open subscheme is everything. -/
theorem mem_subfunctor_iff_opens_eq_top {T : Over S} [IsLocallyNoetherian T.left]
    (ξ : (fppfPicardSheaf p).obj.obj (op T)) : ξ ∈ C.subfunctor.obj (op T) ↔ C.opens ξ = ⊤ := by
  rw [C.mem_subfunctor_iff, eq_top_iff]
  exact ⟨fun h t _ ↦ h t, fun h t ↦ h (show t ∈ (⊤ : T.left.Opens) from trivial)⟩

/-- `Pic^C` on locally Noetherian test schemes: the restriction of `C.subfunctor` to
`Scheme.LocallyNoetherianOver S`. -/
abbrev locallyNoetherianSubfunctor :
    Subfunctor ((Scheme.locallyNoetherianOverInclusion S).op ⋙ (fppfPicardSheaf p).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
  restrictSubfunctor (Scheme.locallyNoetherianOver S) C.subfunctor

/-- **`Pic^C` is an open subfunctor of `Pic_{X/S,(fppf)}` on locally Noetherian test schemes**
(Kleiman, arXiv:math/0504020v1, pp. 28–29, with fppf coverings; "representable by open
immersions" in the sense of Stacks, Tag 01JI). This is the openness hypothesis of
`LocalRepresentability.SubfunctorCover`. -/
theorem isOpenSubfunctor : IsOpenSubfunctor C.locallyNoetherianSubfunctor := by
  intro T ξ
  have : IsLocallyNoetherian ((Scheme.locallyNoetherianOverInclusion S).obj T).left := T.property
  exact ⟨C.opens ξ, fun Z g ↦ C.map_mem_subfunctor_iff ξ g.hom⟩

/-- `Pic^C ×_{Pic} h_T`: for a locally Noetherian test scheme `T` and a section `ξ` of
`Pic_{X/S,(fppf)}` over `T`, the subfunctor of the functor of points of `T` consisting of the
morphisms `g : Z ⟶ T` along which `ξ` pulls back into `Pic^C`. -/
def preimageSubfunctor {T : Scheme.LocallyNoetherianOver S}
    (ξ : (fppfPicardSheaf p).obj.obj (op T.obj)) : Subfunctor (yoneda.obj T) where
  obj Z := {g | (fppfPicardSheaf p).obj.map g.hom.op ξ ∈ C.subfunctor.obj (op Z.unop.obj)}
  map {Z Z'} f g hg := by
    change (fppfPicardSheaf p).obj.map (f.unop ≫ g).hom.op ξ ∈ C.subfunctor.obj (op Z'.unop.obj)
    have h := C.subfunctor.map f.unop.hom.op
      (show (fppfPicardSheaf p).obj.map g.hom.op ξ ∈ C.subfunctor.obj (op Z.unop.obj) from hg)
    change (fppfPicardSheaf p).obj.map f.unop.hom.op ((fppfPicardSheaf p).obj.map g.hom.op ξ) ∈
      C.subfunctor.obj (op Z'.unop.obj) at h
    rwa [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp] at h

theorem mem_preimageSubfunctor_iff {T : Scheme.LocallyNoetherianOver S}
    (ξ : (fppfPicardSheaf p).obj.obj (op T.obj)) {Z : Scheme.LocallyNoetherianOver S}
    (g : Z ⟶ T) :
    g ∈ (C.preimageSubfunctor ξ).obj (op Z) ↔ g.hom.left ⁻¹ᵁ C.opens ξ = ⊤ :=
  C.map_mem_subfunctor_iff ξ g.hom

/-- **`U_ξ` represents `Pic^C ×_{Pic} h_T`** (Kleiman, arXiv:math/0504020v1, pp. 28–29: "`T^φ` is
(represents) the fiber product of functors `P^φ ×_P T`"), on locally Noetherian test schemes: the
open subscheme `U_ξ`, as the object `LocalRepresentability.restrictOpens T (C.opens ξ)`,
represents `C.preimageSubfunctor ξ`, through composition with the inclusion
`LocalRepresentability.restrictOpensι T (C.opens ξ)`. -/
def preimageRepresentableBy {T : Scheme.LocallyNoetherianOver S}
    (ξ : (fppfPicardSheaf p).obj.obj (op T.obj)) :
    (C.preimageSubfunctor ξ).toFunctor.RepresentableBy (restrictOpens T (C.opens ξ)) where
  homEquiv {Z} :=
    { toFun k := ⟨k ≫ restrictOpensι T (C.opens ξ), by
        rw [mem_preimageSubfunctor_iff]
        change (k.hom.left ≫ (C.opens ξ).ι) ⁻¹ᵁ C.opens ξ = ⊤
        rw [Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self, Scheme.Hom.preimage_top]⟩
      invFun g := ObjectProperty.homMk (overOpensLift g.1.hom (C.opens ξ)
        ((C.mem_preimageSubfunctor_iff ξ g.1).mp g.2))
      left_inv k := by
        apply ObjectProperty.hom_ext
        apply Over.OverMorphism.ext
        apply (cancel_mono (C.opens ξ).ι).mp
        exact IsOpenImmersion.lift_fac _ _ _
      right_inv g := by
        apply Subtype.ext
        apply ObjectProperty.hom_ext
        apply Over.OverMorphism.ext
        exact IsOpenImmersion.lift_fac _ _ _ }
  homEquiv_comp f k := by
    apply Subtype.ext
    exact Category.assoc _ _ _

theorem preimageRepresentableBy_homEquiv_coe {T : Scheme.LocallyNoetherianOver S}
    (ξ : (fppfPicardSheaf p).obj.obj (op T.obj)) {Z : Scheme.LocallyNoetherianOver S}
    (k : Z ⟶ restrictOpens T (C.opens ξ)) :
    ((C.preimageRepresentableBy ξ).homEquiv k).1 = k ≫ restrictOpensι T (C.opens ξ) :=
  rfl

/-! ### Families of conditions -/

/-- A pointwise stronger condition has a smaller open (Kleiman, arXiv:math/0504020v1, p. 29: the
`P^φ_m ×_{P^φ} T` form a nested sequence). -/
theorem opens_mono {D : FiberCondition p}
    (hCD : ∀ (T : Over S) (a : (familyPicardFunctor p).obj (op T)) (t : T.left),
      C.Holds T a t → D.Holds T a t)
    {T : Over S} [IsLocallyNoetherian T.left] (ξ : (fppfPicardSheaf p).obj.obj (op T)) :
    C.opens ξ ≤ D.opens ξ := by
  rintro t ⟨V, h, v, a, hv, ha, hC⟩
  exact ⟨V, h, v, a, hv, ha, hCD V a v hC⟩

/-- Pointwise exclusive conditions have disjoint opens (Kleiman, arXiv:math/0504020v1, p. 29: the
`T^φ` are disjoint). -/
theorem disjoint_opens {D : FiberCondition p}
    (hCD : ∀ (T : Over S) (a : (familyPicardFunctor p).obj (op T)) (t : T.left),
      C.Holds T a t → ¬ D.Holds T a t)
    {T : Over S} [IsLocallyNoetherian T.left] (ξ : (fppfPicardSheaf p).obj.obj (op T)) :
    Disjoint (C.opens ξ) (D.opens ξ) := by
  rw [disjoint_iff, eq_bot_iff]
  rintro t ⟨htC, htD⟩
  obtain ⟨V, h, a, -, -, ⟨v, rfl⟩, ha⟩ := exists_flat_app_eq ξ t
  exact absurd ((D.holdsAt_iff ξ _ a ha v).mp htD)
    (hCD _ a v ((C.holdsAt_iff ξ _ a ha v).mp htC))

/-- Pointwise covering conditions have covering opens (Kleiman, arXiv:math/0504020v1, p. 29: the
`T^φ` cover `T`, and the union of the `P^φ_m ×_{P^φ} T` is `T`). -/
theorem iSup_opens_eq_top {ι : Type*} (D : ι → FiberCondition p)
    (hD : ∀ (T : Over S) (a : (familyPicardFunctor p).obj (op T)) (t : T.left),
      ∃ i, (D i).Holds T a t)
    {T : Over S} [IsLocallyNoetherian T.left] (ξ : (fppfPicardSheaf p).obj.obj (op T)) :
    ⨆ i, (D i).opens ξ = ⊤ := by
  rw [eq_top_iff]
  intro t _
  obtain ⟨V, h, a, -, -, ⟨v, rfl⟩, ha⟩ := exists_flat_app_eq ξ t
  obtain ⟨i, hi⟩ := hD _ a v
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, ((D i).holdsAt_iff ξ _ a ha v).mpr hi⟩

end AlgebraicGeometry.Scheme.RelativePicard.FiberCondition
