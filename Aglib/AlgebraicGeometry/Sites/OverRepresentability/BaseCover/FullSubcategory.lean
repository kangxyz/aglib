/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Properties.Noetherian.LocallyNoetherianOverBaseChange
public import Aglib.AlgebraicGeometry.Sites.OverRepresentability.BaseCover
public import Aglib.AlgebraicGeometry.Sites.OverRepresentability.LocallyNoetherian

/-!
# Representability is local on the base, for test schemes in a full subcategory

Let `P` be a property of schemes over `S` that passes to open immersions and is local for open
covers (`IsOpenLocal P`), and `F` a presheaf on the full subcategory `P.FullSubcategory`, with
values in any universe, satisfying the Zariski sheaf condition `IsZariskiSheaf F`. Let
`j i : U i ⟶ S` be open immersions covering `S`, and `Q i` properties of schemes over `U i` such
that `Over.map (j i)` carries `Q i` into `P`, and an object of `P` whose structure morphism lands
in the image of `j i`, viewed over `U i`, satisfies `Q i`. If each restriction of `F` along
`Over.map (j i)`, a presheaf on `(Q i).FullSubcategory`, is representable, then `F` is
representable (`isRepresentable_of_openCover_base_of_isOpenLocal`). This is the step "it is a
local matter on `S` to represent a Zariski sheaf on the category of `S`-schemes" of Kleiman,
*The Picard scheme*, arXiv:math/0504020v1, proof of Thm 4.8, p. 28, which cites EGA I (1971),
Ch. 0, (4.5.5), p. 106 (citation not checked here), for test schemes in a full subcategory.

The proof is that of `isRepresentable_of_openCover_base` (Over `S`) on the full subcategory: the
sections of `F` over test schemes whose structure morphism lands in the image of `j i` form an open
subfunctor (`fullSubcategoryBaseSubfunctor`, `isOpenSubfunctor_fullSubcategoryBaseSubfunctor`),
represented by the image under `Over.map (j i)` of a representing object of the restriction
(`representableByFullSubcategoryBaseSubfunctor`); these subfunctors cover `F`
(`SubfunctorCover.baseCover`), and `SubfunctorCover.representableByGlued` glues the representing
objects. The glued object has a property of morphisms local at the source when the charts have it
(`SubfunctorCover.prop_glued_hom`).

**Locally Noetherian test schemes.** For `P` and `Q i` the locally Noetherian test schemes, the
restriction along `Over.map (j i)` is the restriction along `LocallyNoetherianOver.map (j i)`, and
the conditions on `Q i` hold since `Over.map (j i)` does not change the underlying scheme
(`SubfunctorCover.locallyNoetherianBaseCover`,
`isRepresentable_of_openCover_base_of_isLocallyNoetherian`). This is the form used by the Picard
functor on locally Noetherian test schemes over a locally Noetherian base
(`Aglib.AlgebraicGeometry.Picard.Representability.LocallyNoetherianBase`).
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite

universe v u

namespace AlgebraicGeometry.Scheme.LocalRepresentability

section Subfunctor

variable {S V : Scheme.{u}} (j : V ⟶ S) [IsOpenImmersion j] {P : ObjectProperty (Over S)}
  (F : P.FullSubcategoryᵒᵖ ⥤ Type v)

/-- The subfunctor of sections of `F` over test schemes whose structure morphism lands in the
image of the open immersion `j`. -/
def fullSubcategoryBaseSubfunctor : Subfunctor F where
  obj T := {_ξ | T.unop.obj.hom ⁻¹ᵁ j.opensRange = ⊤}
  map {T T'} f _ hξ := by
    change T'.unop.obj.hom ⁻¹ᵁ j.opensRange = ⊤
    rw [← Over.w f.unop.hom, Scheme.Hom.comp_preimage,
      show T.unop.obj.hom ⁻¹ᵁ j.opensRange = ⊤ from hξ]
    exact Scheme.Hom.preimage_top _

lemma mem_fullSubcategoryBaseSubfunctor_iff {T : P.FullSubcategory} (ξ : F.obj (op T)) :
    ξ ∈ (fullSubcategoryBaseSubfunctor j F).obj (op T) ↔ T.obj.hom ⁻¹ᵁ j.opensRange = ⊤ :=
  Iff.rfl

/-- The subfunctor `fullSubcategoryBaseSubfunctor j F` is open: a section over `T` pulls back into
it exactly over the preimage in `T` of the image of `j`. -/
lemma isOpenSubfunctor_fullSubcategoryBaseSubfunctor :
    IsOpenSubfunctor (fullSubcategoryBaseSubfunctor j F) := by
  intro T _
  refine ⟨T.obj.hom ⁻¹ᵁ j.opensRange, fun Z g => ?_⟩
  change Z.obj.hom ⁻¹ᵁ j.opensRange = ⊤ ↔ g.hom.left ⁻¹ᵁ (T.obj.hom ⁻¹ᵁ j.opensRange) = ⊤
  rw [← Over.w g.hom, Scheme.Hom.comp_preimage]

end Subfunctor

section Representable

variable {S V : Scheme.{u}} (j : V ⟶ S) [IsOpenImmersion j]
  {P : ObjectProperty (Over S)} {Q : ObjectProperty (Over V)}
  (hQP : ∀ Y : Over V, Q Y → P ((Over.map j).obj Y))

/-- `Over.map j` on the full subcategories of `Q` and `P`. -/
abbrev fullSubcategoryOverMap : Q.FullSubcategory ⥤ P.FullSubcategory :=
  P.lift (Q.ι ⋙ Over.map j) fun Y => hQP Y.obj Y.property

variable {j}
  (hPQ : ∀ (T : Over S) (hT : T.hom ⁻¹ᵁ j.opensRange = ⊤), P T → Q (overRestrictBase j T hT))

/-- A test scheme over `S` whose structure morphism lands in the image of `j`, as a test scheme
over `V`. -/
abbrev fullSubcategoryRestrictBase (T : P.FullSubcategory) (hT : T.obj.hom ⁻¹ᵁ j.opensRange = ⊤) :
    Q.FullSubcategory :=
  ⟨overRestrictBase j T.obj hT, hPQ T.obj hT T.property⟩

/-- `T` is the image of its restriction under `Over.map j`. -/
def fullSubcategoryRestrictBaseIso (T : P.FullSubcategory)
    (hT : T.obj.hom ⁻¹ᵁ j.opensRange = ⊤) :
    (fullSubcategoryOverMap j hQP).obj (fullSubcategoryRestrictBase hPQ T hT) ≅ T :=
  P.isoMk (overRestrictBaseIso j T.obj hT)

variable {hQP} {Y : Q.FullSubcategory}

/-- A morphism `T ⟶ Y` over `S` from a test scheme `T` landing in the image of `j`, as a morphism
over `V` from the restriction of `T`. -/
abbrev fullSubcategoryRestrictHom {T : P.FullSubcategory} (hT : T.obj.hom ⁻¹ᵁ j.opensRange = ⊤)
    (g : T ⟶ (fullSubcategoryOverMap j hQP).obj Y) : fullSubcategoryRestrictBase hPQ T hT ⟶ Y :=
  ObjectProperty.homMk (overRestrictHom j (Y := Y.obj) hT g.hom)

variable {F : P.FullSubcategoryᵒᵖ ⥤ Type v}
  (e : ((fullSubcategoryOverMap j hQP).op ⋙ F).RepresentableBy Y)

/-- The section of `F` over `T` given by a morphism `T ⟶ Y` over `S`. -/
def fullSubcategoryBaseHomEquivFun {T : P.FullSubcategory}
    (g : T ⟶ (fullSubcategoryOverMap j hQP).obj Y) : F.obj (op T) :=
  F.map (fullSubcategoryRestrictBaseIso hQP hPQ T
      (preimage_eq_top_of_hom j (Y := Y.obj) g.hom)).inv.op
    (e.homEquiv (fullSubcategoryRestrictHom hPQ (preimage_eq_top_of_hom j (Y := Y.obj) g.hom) g))

/-- The morphism `T ⟶ Y` over `S` given by a section of `F` over a test scheme `T` landing in the
image of `j`. -/
def fullSubcategoryBaseHomEquivInv {T : P.FullSubcategory}
    (hT : T.obj.hom ⁻¹ᵁ j.opensRange = ⊤) (ξ : F.obj (op T)) :
    T ⟶ (fullSubcategoryOverMap j hQP).obj Y :=
  ObjectProperty.homMk (Over.homMk (U := T.obj) (V := (Over.map j).obj Y.obj)
    (e.homEquiv.symm (F.map (fullSubcategoryRestrictBaseIso hQP hPQ T hT).hom.op ξ)).hom.left (by
      have hw := Over.w
        (e.homEquiv.symm (F.map (fullSubcategoryRestrictBaseIso hQP hPQ T hT).hom.op ξ)).hom
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ j) hw).trans (overRestrictBase_hom_comp j T.obj hT))))

lemma fullSubcategoryBaseHomEquivInv_fun {T : P.FullSubcategory}
    (hT : T.obj.hom ⁻¹ᵁ j.opensRange = ⊤) (g : T ⟶ (fullSubcategoryOverMap j hQP).obj Y) :
    fullSubcategoryBaseHomEquivInv hPQ e hT (fullSubcategoryBaseHomEquivFun hPQ e g) = g := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  simp only [fullSubcategoryBaseHomEquivInv, fullSubcategoryBaseHomEquivFun,
    ObjectProperty.homMk_hom, Over.homMk_left]
  rw [map_hom_inv_apply, Equiv.symm_apply_apply]
  rfl

lemma fullSubcategoryBaseHomEquivFun_inv {T : P.FullSubcategory}
    (hT : T.obj.hom ⁻¹ᵁ j.opensRange = ⊤) (ξ : F.obj (op T)) :
    fullSubcategoryBaseHomEquivFun hPQ e (fullSubcategoryBaseHomEquivInv hPQ e hT ξ) = ξ := by
  have h : fullSubcategoryRestrictHom hPQ
      (preimage_eq_top_of_hom j (Y := Y.obj) (fullSubcategoryBaseHomEquivInv hPQ e hT ξ).hom)
      (fullSubcategoryBaseHomEquivInv hPQ e hT ξ) =
        e.homEquiv.symm (F.map (fullSubcategoryRestrictBaseIso hQP hPQ T hT).hom.op ξ) := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    rfl
  simp only [fullSubcategoryBaseHomEquivFun]
  rw [h, Equiv.apply_symm_apply, map_inv_hom_apply]

lemma fullSubcategoryBaseHomEquivFun_comp {T₁ T₂ : P.FullSubcategory} (f : T₁ ⟶ T₂)
    (g : T₂ ⟶ (fullSubcategoryOverMap j hQP).obj Y) :
    fullSubcategoryBaseHomEquivFun hPQ e (f ≫ g) =
      F.map f.op (fullSubcategoryBaseHomEquivFun hPQ e g) := by
  have h₁ := preimage_eq_top_of_hom j (Y := Y.obj) (f ≫ g).hom
  have h₂ := preimage_eq_top_of_hom j (Y := Y.obj) g.hom
  let m : fullSubcategoryRestrictBase hPQ T₁ h₁ ⟶ fullSubcategoryRestrictBase hPQ T₂ h₂ :=
    ObjectProperty.homMk (overRestrictMap j f.hom h₁ h₂)
  have hf :
      fullSubcategoryRestrictHom hPQ h₁ (f ≫ g) = m ≫ fullSubcategoryRestrictHom hPQ h₂ g := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    rfl
  have hmor : (fullSubcategoryRestrictBaseIso hQP hPQ T₁ h₁).inv ≫
      (fullSubcategoryOverMap j hQP).map m =
        f ≫ (fullSubcategoryRestrictBaseIso hQP hPQ T₂ h₂).inv := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    simp [m, fullSubcategoryRestrictBaseIso, overRestrictBaseIso, overRestrictMap]
  simp only [fullSubcategoryBaseHomEquivFun]
  rw [hf, e.homEquiv_comp]
  simp only [Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op]
  rw [← map_comp_op_apply, ← map_comp_op_apply, hmor]

/-- If the restriction of `F` along `Over.map j` is represented by `Y`, then the sections of `F`
over test schemes landing in the image of `j` are represented by `Y`, viewed over `S`. -/
def representableByFullSubcategoryBaseSubfunctor :
    (fullSubcategoryBaseSubfunctor j F).toFunctor.RepresentableBy
      ((fullSubcategoryOverMap j hQP).obj Y) where
  homEquiv {_} :=
    { toFun g :=
        ⟨fullSubcategoryBaseHomEquivFun hPQ e g, preimage_eq_top_of_hom j (Y := Y.obj) g.hom⟩
      invFun ξ := fullSubcategoryBaseHomEquivInv hPQ e
        ((mem_fullSubcategoryBaseSubfunctor_iff j F ξ.1).1 ξ.2) ξ.1
      left_inv g := fullSubcategoryBaseHomEquivInv_fun hPQ e _ g
      right_inv ξ := Subtype.ext (fullSubcategoryBaseHomEquivFun_inv hPQ e _ ξ.1) }
  homEquiv_comp f g := Subtype.ext (fullSubcategoryBaseHomEquivFun_comp hPQ e f g)

end Representable

section Cover

variable {S : Scheme.{u}} {P : ObjectProperty (Over S)} [IsOpenLocal P]
  {F : P.FullSubcategoryᵒᵖ ⥤ Type v}

/-- **The base cover**: for open immersions `j i : U i ⟶ S` covering `S`, the open subfunctors
`fullSubcategoryBaseSubfunctor (j i) F`, with representations of the restrictions of `F` along
`Over.map (j i)`, form an open cover of `F` by representable subfunctors. -/
abbrev SubfunctorCover.baseCover {ι : Type u} {U : ι → Scheme.{u}} (j : ∀ i, U i ⟶ S)
    [∀ i, IsOpenImmersion (j i)] (hcov : ∀ x : S, ∃ i, x ∈ Set.range (j i))
    {Q : ∀ i, ObjectProperty (Over (U i))}
    (hQP : ∀ i (Y : Over (U i)), Q i Y → P ((Over.map (j i)).obj Y))
    (hPQ : ∀ i (T : Over S) (hT : T.hom ⁻¹ᵁ (j i).opensRange = ⊤), P T →
      Q i (overRestrictBase (j i) T hT))
    (Y : ∀ i, (Q i).FullSubcategory)
    (e : ∀ i, ((fullSubcategoryOverMap (j i) (hQP i)).op ⋙ F).RepresentableBy (Y i)) :
    SubfunctorCover F where
  I := ι
  sub i := fullSubcategoryBaseSubfunctor (j i) F
  isOpen i := isOpenSubfunctor_fullSubcategoryBaseSubfunctor (j i) F
  X i := (fullSubcategoryOverMap (j i) (hQP i)).obj (Y i)
  representableBy i := representableByFullSubcategoryBaseSubfunctor (hPQ i) (e i)
  covers T _ x := by
    obtain ⟨i, hi⟩ := hcov (T.obj.hom x)
    refine ⟨i, restrictOpens T (T.obj.hom ⁻¹ᵁ (j i).opensRange), restrictOpensι T _, ?_, ?_⟩
    · change x ∈ Set.range (T.obj.hom ⁻¹ᵁ (j i).opensRange).ι
      rw [Scheme.Opens.range_ι]
      exact hi
    · change ((T.obj.hom ⁻¹ᵁ (j i).opensRange).ι ≫ T.obj.hom) ⁻¹ᵁ (j i).opensRange = ⊤
      rw [Scheme.Hom.comp_preimage]
      exact Scheme.Opens.ι_preimage_self _

/-- **Representability is local on the base**, for test schemes in a full subcategory (Kleiman,
arXiv:math/0504020v1, proof of Thm 4.8, p. 28): for `P` open-local (`IsOpenLocal P`), open
immersions `j i : U i ⟶ S` covering `S`, and properties `Q i` of schemes over `U i` such that
`Over.map (j i)` carries `Q i` into `P` (`hQP`) and every object of `P` landing in the image of
`j i`, viewed over `U i`, satisfies `Q i` (`hPQ`), a Zariski sheaf on `P.FullSubcategory` whose
restrictions along `Over.map (j i)` are representable is representable. -/
theorem isRepresentable_of_openCover_base_of_isOpenLocal (hF : IsZariskiSheaf F) {ι : Type u}
    {U : ι → Scheme.{u}} (j : ∀ i, U i ⟶ S) [∀ i, IsOpenImmersion (j i)]
    (hcov : ∀ x : S, ∃ i, x ∈ Set.range (j i)) {Q : ∀ i, ObjectProperty (Over (U i))}
    (hQP : ∀ i (Y : Over (U i)), Q i Y → P ((Over.map (j i)).obj Y))
    (hPQ : ∀ i (T : Over S) (hT : T.hom ⁻¹ᵁ (j i).opensRange = ⊤), P T →
      Q i (overRestrictBase (j i) T hT))
    (hrep : ∀ i, ((fullSubcategoryOverMap (j i) (hQP i)).op ⋙ F).IsRepresentable) :
    F.IsRepresentable :=
  (SubfunctorCover.baseCover j hcov hQP hPQ _
    fun i => ((fullSubcategoryOverMap (j i) (hQP i)).op ⋙ F).representableBy).isRepresentable hF

/-- The glued object of a cover by representable open subfunctors has a property of morphisms
that is local at the source when the structure morphisms of the representing objects have it. -/
theorem SubfunctorCover.prop_glued_hom (𝒰 : SubfunctorCover F)
    (Pr : MorphismProperty Scheme.{u}) [IsZariskiLocalAtSource Pr]
    (h : ∀ i, Pr (𝒰.X i).obj.hom) : Pr 𝒰.glued.obj.hom :=
  IsZariskiLocalAtSource.of_openCover (P := Pr) 𝒰.schemeGlueData.openCover fun i => by
    have hi : 𝒰.schemeGlueData.openCover.f i ≫ 𝒰.glued.obj.hom = (𝒰.X i).obj.hom :=
      𝒰.ι_gluedHom i
    rw [hi]
    exact h i

end Cover

section LocallyNoetherian

variable {S : Scheme.{u}} {F : (LocallyNoetherianOver S)ᵒᵖ ⥤ Type v}

/-- **The base cover on locally Noetherian test schemes**: for open immersions `j i : U i ⟶ S`
covering `S` and representations of the restrictions of `F` along `LocallyNoetherianOver.map (j i)`
by `Y i`, the open subfunctors of sections over test schemes landing in the images of the `j i`
form an open cover of `F` by subfunctors represented by the `Y i`, viewed over `S`. -/
abbrev SubfunctorCover.locallyNoetherianBaseCover {ι : Type u} {U : ι → Scheme.{u}}
    (j : ∀ i, U i ⟶ S) [∀ i, IsOpenImmersion (j i)] (hcov : ∀ x : S, ∃ i, x ∈ Set.range (j i))
    (Y : ∀ i, LocallyNoetherianOver (U i))
    (e : ∀ i, ((LocallyNoetherianOver.map (j i)).op ⋙ F).RepresentableBy (Y i)) :
    SubfunctorCover F :=
  SubfunctorCover.baseCover (Q := fun i => locallyNoetherianOver (U i)) j hcov
    (fun _ _ hY => hY) (fun _ _ _ hT => hT) Y e

/-- **Representability is local on the base**, on locally Noetherian test schemes (Kleiman,
arXiv:math/0504020v1, proof of Thm 4.8, p. 28): a Zariski sheaf on locally Noetherian schemes over
`S` whose restrictions along `LocallyNoetherianOver.map (j i)`, for open immersions `j i` covering
`S`, are representable is representable. -/
theorem isRepresentable_of_openCover_base_of_isLocallyNoetherian (hF : IsZariskiSheaf F)
    {ι : Type u} {U : ι → Scheme.{u}} (j : ∀ i, U i ⟶ S) [∀ i, IsOpenImmersion (j i)]
    (hcov : ∀ x : S, ∃ i, x ∈ Set.range (j i))
    (hrep : ∀ i, ((LocallyNoetherianOver.map (j i)).op ⋙ F).IsRepresentable) :
    F.IsRepresentable :=
  (SubfunctorCover.locallyNoetherianBaseCover j hcov _
    fun i => ((LocallyNoetherianOver.map (j i)).op ⋙ F).representableBy).isRepresentable hF

end LocallyNoetherian

end AlgebraicGeometry.Scheme.LocalRepresentability
