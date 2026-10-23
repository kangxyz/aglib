/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.OverRepresentability

/-!
# Representability of Zariski sheaves is local on the base

Let `F` be a Zariski sheaf on `Over S`, with values in any universe, and `j i : U i ⟶ S` open
immersions covering `S`. If each restriction `(Over.map (j i)).op ⋙ F` of `F` to schemes over
`U i` is representable, then `F` is representable (`isRepresentable_of_openCover_base`,
`overZariskiLocalRepresentability`). This is the step "it is a local matter on `S` to represent a
Zariski sheaf on the category of `S`-schemes" of Kleiman, arXiv:math/0504020v1, proof of
Thm 4.8, p. 28, which cites EGA I (1971), Ch. 0, (4.5.5), p. 106 (citation not checked here).

The proof applies `OverSubfunctorCover` to the open subfunctors `baseSubfunctor (j i) F` of
sections over schemes whose structure morphism lands in the image of `j i`; the subfunctor
`baseSubfunctor j F` is represented by `(Over.map j).obj Y` when the restriction of `F` along
`Over.map j` is represented by `Y` (`representableByBaseSubfunctor`).
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite

universe v u

namespace AlgebraicGeometry.Scheme.LocalRepresentability

variable {S V : Scheme.{u}} (j : V ⟶ S) [IsOpenImmersion j]

/-- A scheme over `S` whose structure morphism lands in the image of `j`, as a scheme over the
source of `j`. -/
abbrev overRestrictBase (T : Over S) (hT : T.hom ⁻¹ᵁ j.opensRange = ⊤) : Over V :=
  Over.mk (IsOpenImmersion.lift j T.hom
    (range_subset_range_of_preimage_opensRange_eq_top T.hom j hT))

lemma overRestrictBase_hom_comp (T : Over S) (hT : T.hom ⁻¹ᵁ j.opensRange = ⊤) :
    (overRestrictBase j T hT).hom ≫ j = T.hom :=
  IsOpenImmersion.lift_fac _ _ _

/-- `T` is the image of its restriction under `Over.map j`. -/
def overRestrictBaseIso (T : Over S) (hT : T.hom ⁻¹ᵁ j.opensRange = ⊤) :
    (Over.map j).obj (overRestrictBase j T hT) ≅ T :=
  Over.isoMk (Iso.refl _) ((Category.id_comp _).trans (overRestrictBase_hom_comp j T hT).symm)

lemma preimage_eq_top_of_hom {T : Over S} {Y : Over V} (g : T ⟶ (Over.map j).obj Y) :
    T.hom ⁻¹ᵁ j.opensRange = ⊤ := by
  have h : g.left ≫ Y.hom ≫ j = T.hom := Over.w g
  rw [← h]
  simp

/-- A morphism to `(Over.map j).obj Y` over `S`, as a morphism over `V`. -/
def overRestrictHom {T : Over S} (hT : T.hom ⁻¹ᵁ j.opensRange = ⊤) {Y : Over V}
    (g : T ⟶ (Over.map j).obj Y) : overRestrictBase j T hT ⟶ Y :=
  Over.homMk (U := overRestrictBase j T hT) (V := Y) g.left
    ((cancel_mono j).1 ((Category.assoc _ _ _).trans
      ((Over.w g).trans (overRestrictBase_hom_comp j T hT).symm)))

/-- A morphism over `S` between schemes landing in the image of `j`, as a morphism over `V`. -/
def overRestrictMap {T₁ T₂ : Over S} (f : T₁ ⟶ T₂) (h₁ : T₁.hom ⁻¹ᵁ j.opensRange = ⊤)
    (h₂ : T₂.hom ⁻¹ᵁ j.opensRange = ⊤) : overRestrictBase j T₁ h₁ ⟶ overRestrictBase j T₂ h₂ :=
  Over.homMk (U := overRestrictBase j T₁ h₁) (V := overRestrictBase j T₂ h₂) f.left
    ((cancel_mono j).1 ((Category.assoc _ _ _).trans
      ((congrArg (f.left ≫ ·) (overRestrictBase_hom_comp j T₂ h₂)).trans
        ((Over.w f).trans (overRestrictBase_hom_comp j T₁ h₁).symm))))

lemma map_hom_inv_apply {C : Type*} [Category* C] (F : Cᵒᵖ ⥤ Type v) {X Y : C} (e : X ≅ Y)
    (x : F.obj (op X)) : F.map e.hom.op (F.map e.inv.op x) = x := by
  rw [← map_comp_op_apply, e.hom_inv_id, op_id, F.map_id]
  rfl

lemma map_inv_hom_apply {C : Type*} [Category* C] (F : Cᵒᵖ ⥤ Type v) {X Y : C} (e : X ≅ Y)
    (x : F.obj (op Y)) : F.map e.inv.op (F.map e.hom.op x) = x := by
  rw [← map_comp_op_apply, e.inv_hom_id, op_id, F.map_id]
  rfl

variable (F : (Over S)ᵒᵖ ⥤ Type v)

/-- The subfunctor of sections of `F` over schemes whose structure morphism lands in the image
of `j`. -/
def baseSubfunctor : Subfunctor F where
  obj T := {_ξ | T.unop.hom ⁻¹ᵁ j.opensRange = ⊤}
  map {T T'} f _ hξ := by
    change T'.unop.hom ⁻¹ᵁ j.opensRange = ⊤
    rw [← Over.w f.unop, Scheme.Hom.comp_preimage,
      show T.unop.hom ⁻¹ᵁ j.opensRange = ⊤ from hξ]
    exact Scheme.Hom.preimage_top _

lemma mem_baseSubfunctor_iff {T : Over S} (ξ : F.obj (op T)) :
    ξ ∈ (baseSubfunctor j F).obj (op T) ↔ T.hom ⁻¹ᵁ j.opensRange = ⊤ :=
  Iff.rfl

lemma isOpen_baseSubfunctor : IsOpenOverSubfunctor (baseSubfunctor j F) := by
  intro T _
  refine ⟨T.hom ⁻¹ᵁ j.opensRange, fun Z g => ?_⟩
  change Z.hom ⁻¹ᵁ j.opensRange = ⊤ ↔ g.left ⁻¹ᵁ (T.hom ⁻¹ᵁ j.opensRange) = ⊤
  rw [← Over.w g, Scheme.Hom.comp_preimage]

variable {j F} {Y : Over V} (e : ((Over.map j).op ⋙ F).RepresentableBy Y)

/-- The section of `F` over `T` given by a morphism `T ⟶ Y` over `S`. -/
def baseHomEquivFun {T : Over S} (g : T ⟶ (Over.map j).obj Y) : F.obj (op T) :=
  F.map (overRestrictBaseIso j T (preimage_eq_top_of_hom j g)).inv.op
    (e.homEquiv (overRestrictHom j (preimage_eq_top_of_hom j g) g))

/-- The morphism `T ⟶ Y` over `S` given by a section of `F` over a scheme `T` landing in the
image of `j`. -/
def baseHomEquivInv {T : Over S} (hT : T.hom ⁻¹ᵁ j.opensRange = ⊤) (ξ : F.obj (op T)) :
    T ⟶ (Over.map j).obj Y :=
  Over.homMk (e.homEquiv.symm (F.map (overRestrictBaseIso j T hT).hom.op ξ)).left (by
    have hw := Over.w (e.homEquiv.symm (F.map (overRestrictBaseIso j T hT).hom.op ξ))
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ j) hw).trans (overRestrictBase_hom_comp j T hT)))

lemma baseHomEquivInv_fun {T : Over S} (hT : T.hom ⁻¹ᵁ j.opensRange = ⊤)
    (g : T ⟶ (Over.map j).obj Y) : baseHomEquivInv e hT (baseHomEquivFun e g) = g := by
  apply Over.OverMorphism.ext
  simp only [baseHomEquivInv, baseHomEquivFun, Over.homMk_left]
  rw [map_hom_inv_apply, Equiv.symm_apply_apply]
  rfl

lemma baseHomEquivFun_inv {T : Over S} (hT : T.hom ⁻¹ᵁ j.opensRange = ⊤) (ξ : F.obj (op T)) :
    baseHomEquivFun e (baseHomEquivInv e hT ξ) = ξ := by
  have h : overRestrictHom j (preimage_eq_top_of_hom j (baseHomEquivInv e hT ξ))
      (baseHomEquivInv e hT ξ) =
        e.homEquiv.symm (F.map (overRestrictBaseIso j T hT).hom.op ξ) := by
    ext
    rfl
  simp only [baseHomEquivFun]
  rw [h, Equiv.apply_symm_apply, map_inv_hom_apply]

lemma baseHomEquivFun_comp {T₁ T₂ : Over S} (f : T₁ ⟶ T₂) (g : T₂ ⟶ (Over.map j).obj Y) :
    baseHomEquivFun e (f ≫ g) = F.map f.op (baseHomEquivFun e g) := by
  have h₁ := preimage_eq_top_of_hom j (f ≫ g)
  have h₂ := preimage_eq_top_of_hom j g
  have hf : overRestrictHom j h₁ (f ≫ g) =
      overRestrictMap j f h₁ h₂ ≫ overRestrictHom j h₂ g := by
    ext
    rfl
  have hmor : (overRestrictBaseIso j T₁ h₁).inv ≫ (Over.map j).map (overRestrictMap j f h₁ h₂) =
      f ≫ (overRestrictBaseIso j T₂ h₂).inv := by
    ext
    simp [overRestrictBaseIso, overRestrictMap]
  simp only [baseHomEquivFun]
  rw [hf, e.homEquiv_comp]
  simp only [Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op]
  rw [← map_comp_op_apply, ← map_comp_op_apply, hmor]

/-- If the restriction of `F` along `Over.map j` is represented by `Y`, then the sections of `F`
over schemes landing in the image of `j` are represented by `Y`, viewed over `S`. -/
def representableByBaseSubfunctor :
    (baseSubfunctor j F).toFunctor.RepresentableBy ((Over.map j).obj Y) where
  homEquiv {_} :=
    { toFun g := ⟨baseHomEquivFun e g, preimage_eq_top_of_hom j g⟩
      invFun ξ := baseHomEquivInv e ((mem_baseSubfunctor_iff j F ξ.1).1 ξ.2) ξ.1
      left_inv g := baseHomEquivInv_fun e _ g
      right_inv ξ := Subtype.ext (baseHomEquivFun_inv e _ ξ.1) }
  homEquiv_comp f g := Subtype.ext (baseHomEquivFun_comp e f g)

/-- The open subfunctors `baseSubfunctor (j i) F` for open immersions `j i` covering `S`, with
representations of the restrictions of `F` along `Over.map (j i)`, form an open cover of `F` by
representable subfunctors. -/
def baseCover {ι : Type u} {U : ι → Scheme.{u}} (j : ∀ i, U i ⟶ S)
    [∀ i, IsOpenImmersion (j i)] (hcov : ∀ x : S, ∃ i, x ∈ Set.range (j i))
    (Y : ∀ i, Over (U i)) (e : ∀ i, ((Over.map (j i)).op ⋙ F).RepresentableBy (Y i)) :
    OverSubfunctorCover F where
  I := ι
  sub i := baseSubfunctor (j i) F
  isOpen i := isOpen_baseSubfunctor (j i) F
  X i := (Over.map (j i)).obj (Y i)
  representableBy i := representableByBaseSubfunctor (e i)
  covers T _ x := by
    obtain ⟨i, hi⟩ := hcov (T.hom x)
    refine ⟨i, overOpens T (T.hom ⁻¹ᵁ (j i).opensRange), overOpensι T _, ?_, ?_⟩
    · change x ∈ Set.range (T.hom ⁻¹ᵁ (j i).opensRange).ι
      rw [Scheme.Opens.range_ι]
      exact hi
    · change ((T.hom ⁻¹ᵁ (j i).opensRange).ι ≫ T.hom) ⁻¹ᵁ (j i).opensRange = ⊤
      rw [Scheme.Hom.comp_preimage]
      exact Scheme.Opens.ι_preimage_self _

/-- **Representability is local on the base** (Kleiman, arXiv:math/0504020v1, proof of
Thm 4.8, p. 28): a Zariski sheaf on `Over S` whose restrictions along open immersions covering
`S` are representable is representable. -/
theorem isRepresentable_of_openCover_base {F : (Over S)ᵒᵖ ⥤ Type v}
    (hF : Presieve.IsSheaf (Scheme.zariskiTopology.over S) F) {ι : Type u}
    {U : ι → Scheme.{u}} (j : ∀ i, U i ⟶ S) (hj : ∀ i, IsOpenImmersion (j i))
    (hcov : ∀ x : S, ∃ i, x ∈ Set.range (j i))
    (hrep : ∀ i, ((Over.map (j i)).op ⋙ F).IsRepresentable) : F.IsRepresentable :=
  have := hj
  (baseCover j hcov (fun i => ((Over.map (j i)).op ⋙ F).reprX)
    (fun i => ((Over.map (j i)).op ⋙ F).representableBy)).isRepresentable hF

/-- **Representability is local on the base**, for presheaves with values in `Type (u + 1)`, in
the form used by the Grassmannian of a locally free sheaf: a Zariski sheaf on `Over S` whose
restrictions along open immersions covering `S` are representable is representable. -/
theorem overZariskiLocalRepresentability (S : Scheme.{u}) :
    ∀ (F : (Over S)ᵒᵖ ⥤ Type (u + 1)), Presieve.IsSheaf (Scheme.zariskiTopology.over S) F →
      ∀ (ι : Type u) (U : ι → Scheme.{u}) (j : ∀ i, U i ⟶ S), (∀ i, IsOpenImmersion (j i)) →
        (∀ x : S, ∃ i, x ∈ Set.range (j i)) →
          (∀ i, ((Over.map (j i)).op ⋙ F).IsRepresentable) → F.IsRepresentable :=
  fun _ hF _ _ j hj hcov hrep => isRepresentable_of_openCover_base hF j hj hcov hrep

end AlgebraicGeometry.Scheme.LocalRepresentability
