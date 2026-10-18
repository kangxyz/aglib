/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.Charts
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.AffineNaturality
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.AffineRefinement
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.OpenSquareComposition
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.RefinementPasting
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Restriction.Composition

/-! # Refinement of the actual local nonflat comparison

Successive affine chart refinements preserve the actual local arrow. The proof
pastes the original pullback, higher-image open, and coefficient comparisons.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules.Nonflat

private theorem localComparison_map_paste
    {C D : Type*} [Category C] [Category D] (J : C ⥤ D)
    {E₁ F₁ A₁ B₁ C₁ : C} {E₀ F₀ A₀ B₀ C₀ D₁ D₂ C₂ : D}
    (s : E₀ ⟶ J.obj E₁) (t : F₀ ⟶ J.obj F₁) (ti : J.obj F₁ ⟶ F₀)
    (a₁ : E₁ ⟶ A₁) (b₁ : A₁ ⟶ B₁) (k₁ : B₁ ⟶ C₁)
    (d₁ : F₁ ⟶ C₁) (d₁i : C₁ ⟶ F₁)
    (a₀ : E₀ ⟶ A₀) (b₀ : A₀ ⟶ B₀) (k₀ : B₀ ⟶ C₀)
    (d₀ : F₀ ⟶ C₀) (d₀i : C₀ ⟶ F₀)
    (r : J.obj B₁ ⟶ D₁) (h : D₁ ⟶ D₂) (k : D₂ ⟶ C₂)
    (z : J.obj C₁ ⟶ C₂) (zi : C₂ ⟶ J.obj C₁) (v : B₀ ⟶ D₂) (w : C₀ ⟶ C₂)
    (ht : t ≫ ti = 𝟙 F₀) (hd₁ : d₁ ≫ d₁i = 𝟙 F₁)
    (hd₀ : d₀i ≫ d₀ = 𝟙 C₀) (hz : z ≫ zi = 𝟙 (J.obj C₁))
    (hk : J.map k₁ = r ≫ h ≫ k ≫ zi)
    (hsource : s ≫ J.map a₁ ≫ J.map b₁ ≫ r ≫ h = a₀ ≫ b₀ ≫ v)
    (hmiddle : v ≫ k = k₀ ≫ w)
    (htarget : ti ≫ d₀ ≫ w = J.map d₁ ≫ z) :
    s ≫ J.map (a₁ ≫ b₁ ≫ k₁ ≫ d₁i) = (a₀ ≫ b₀ ≫ k₀ ≫ d₀i) ≫ t := by
  have hd₁' : J.map d₁ ≫ J.map d₁i = 𝟙 (J.obj F₁) := by
    rw [← J.map_comp, hd₁, J.map_id]
  have hi := congrArg (fun u => d₀i ≫ t ≫ u ≫ zi ≫ J.map d₁i) htarget
  simp only [Category.assoc, reassoc_of% ht, reassoc_of% hd₀,
    reassoc_of% hz, hd₁', Category.comp_id] at hi
  simp only [Functor.map_comp, Category.assoc]
  rw [hk]
  simp only [Category.assoc]
  rw [reassoc_of% hsource, reassoc_of% hmiddle, hi]

/-- The actual local nonflat comparison commutes with simultaneous affine open refinement
of its two base charts, using the original restriction-composition isomorphisms. -/
theorem localMap_refinement
    {W U V X U₁ W₁ U₀ W₀ : Scheme.{u}}
    (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (g : V ⟶ X)
    (h : IsPullback a b f g) [QuasiCompact f] [QuasiSeparated f]
    {R S R₀ S₀ : CommRingCat.{u}}
    (j : Spec R ⟶ X) (v : Spec S ⟶ V) (σ : R ⟶ S)
    [IsOpenImmersion j] [IsOpenImmersion v] (hv : Spec.map σ ≫ j = v ≫ g)
    (p₁ : U₁ ⟶ U) (d₁ : U₁ ⟶ Spec R) [IsOpenImmersion p₁]
    (hU₁ : IsPullback p₁ d₁ f j)
    (c₁ : W₁ ⟶ W) (e₁ : W₁ ⟶ Spec S) [IsOpenImmersion c₁]
    (hW₁ : IsPullback c₁ e₁ b v)
    (q₁ : W₁ ⟶ U₁) (hq₁ : q₁ ≫ p₁ = c₁ ≫ a) (hb₁ : q₁ ≫ d₁ = e₁ ≫ Spec.map σ)
    (ρ : R ⟶ R₀) (τ : S ⟶ S₀) (σ₀ : R₀ ⟶ S₀)
    [IsOpenImmersion (Spec.map ρ)] [IsOpenImmersion (Spec.map τ)]
    (hb : Spec.map τ ≫ Spec.map σ = Spec.map σ₀ ≫ Spec.map ρ)
    (ht : Spec.map σ₀ ≫ (Spec.map ρ ≫ j) = (Spec.map τ ≫ v) ≫ g)
    (p₀ : U₀ ⟶ U₁) (d₀ : U₀ ⟶ Spec R₀) [IsOpenImmersion p₀]
    (hU₀ : IsPullback p₀ d₀ d₁ (Spec.map ρ))
    (c₀ : W₀ ⟶ W₁) (e₀ : W₀ ⟶ Spec S₀) [IsOpenImmersion c₀]
    (hW₀ : IsPullback c₀ e₀ e₁ (Spec.map τ))
    (q₀ : W₀ ⟶ U₀) (hq₀ : q₀ ≫ p₀ = c₀ ≫ q₁)
    (hb₀ : q₀ ≫ d₀ = e₀ ≫ Spec.map σ₀)
    (hqT : q₀ ≫ (p₀ ≫ p₁) = (c₀ ≫ c₁) ≫ a)
    (n : ℕ) (M : U.Modules) [M.IsQuasicoherent] :
    (restrictFunctorComp (Spec.map τ) v).hom.app
        ((pullback g).obj (((pushforward f).rightDerived n).obj M)) ≫
      (restrictFunctor (Spec.map τ)).map
        (localMap a b f g h j v σ hv n M p₁ d₁ hU₁ c₁ e₁ hW₁ q₁ hq₁ hb₁) =
    localMap a b f g h (Spec.map ρ ≫ j) (Spec.map τ ≫ v) σ₀ ht n M
        (p₀ ≫ p₁) d₀ (hU₀.paste_horiz hU₁)
        (c₀ ≫ c₁) e₀ (hW₀.paste_horiz hW₁) q₀ hqT hb₀ ≫
      (restrictFunctorComp (Spec.map τ) v).hom.app
        (((pushforward b).rightDerived n).obj ((pullback a).obj M)) := by
  let : QuasiCompact b := MorphismProperty.of_isPullback h inferInstance
  let : QuasiSeparated b := MorphismProperty.of_isPullback h inferInstance
  let : QuasiCompact d₁ := MorphismProperty.of_isPullback hU₁ inferInstance
  let : QuasiSeparated d₁ := MorphismProperty.of_isPullback hU₁ inferInstance
  let : QuasiCompact e₁ := MorphismProperty.of_isPullback hW₁ inferInstance
  let : QuasiSeparated e₁ := MorphismProperty.of_isPullback hW₁ inferInstance
  let : QuasiCompact d₀ := MorphismProperty.of_isPullback hU₀ inferInstance
  let : QuasiSeparated d₀ := MorphismProperty.of_isPullback hU₀ inferInstance
  let : QuasiCompact e₀ := MorphismProperty.of_isPullback hW₀ inferInstance
  let : QuasiSeparated e₀ := MorphismProperty.of_isPullback hW₀ inferInstance
  let N := (pullback a).obj M
  let E := ((pushforward f).rightDerived n).obj M
  let F := ((pushforward b).rightDerived n).obj N
  let J := restrictFunctor (Spec.map τ)
  let P := pullback (Spec.map σ₀)
  let H₀ := (pushforward d₀).rightDerived n
  let K₀ := (pushforward e₀).rightDerived n
  let u := (pullbackPushforwardAdjunction a).unit.app M
  let ψ₁ : M.restrict p₁ ⟶ (pushforward q₁).obj (N.restrict c₁) :=
    chartCoefficient a p₁ c₁ q₁ hq₁ u
  let ψ₀ : (M.restrict p₁).restrict p₀ ⟶
      (pushforward q₀).obj ((N.restrict c₁).restrict c₀) :=
    chartCoefficient q₁ p₀ c₀ q₀ hq₀ ψ₁
  let ψT : M.restrict (p₀ ≫ p₁) ⟶ (pushforward q₀).obj (N.restrict (c₀ ≫ c₁)) :=
    chartCoefficient a (p₀ ≫ p₁) (c₀ ≫ c₁) q₀ hqT u
  let m : M.restrict (p₀ ≫ p₁) ⟶ (M.restrict p₁).restrict p₀ :=
    (restrictFunctorComp p₀ p₁).hom.app M
  let mi : (M.restrict p₁).restrict p₀ ⟶ M.restrict (p₀ ≫ p₁) :=
    (restrictFunctorComp p₀ p₁).inv.app M
  let l : N.restrict (c₀ ≫ c₁) ⟶ (N.restrict c₁).restrict c₀ :=
    (restrictFunctorComp c₀ c₁).hom.app N
  let rf₁ : E.restrict j ⟶ ((pushforward d₁).rightDerived n).obj (M.restrict p₁) :=
    (higherDirectImageOpenRestrictionIso p₁ d₁ f j hU₁ n).hom.app M
  let rb₁ : F.restrict v ⟶ ((pushforward e₁).rightDerived n).obj (N.restrict c₁) :=
    (higherDirectImageOpenRestrictionIso c₁ e₁ b v hW₁ n).hom.app N
  let rb₁i : ((pushforward e₁).rightDerived n).obj (N.restrict c₁) ⟶ F.restrict v :=
    (higherDirectImageOpenRestrictionIso c₁ e₁ b v hW₁ n).inv.app N
  let rf₀ : (((pushforward d₁).rightDerived n).obj (M.restrict p₁)).restrict (Spec.map ρ) ⟶
      H₀.obj ((M.restrict p₁).restrict p₀) :=
    (higherDirectImageOpenRestrictionIso p₀ d₀ d₁ (Spec.map ρ) hU₀ n).hom.app
      (M.restrict p₁)
  let rb₀ : (((pushforward e₁).rightDerived n).obj (N.restrict c₁)).restrict (Spec.map τ) ⟶
      K₀.obj ((N.restrict c₁).restrict c₀) :=
    (higherDirectImageOpenRestrictionIso c₀ e₀ e₁ (Spec.map τ) hW₀ n).hom.app
      (N.restrict c₁)
  let rb₀i : K₀.obj ((N.restrict c₁).restrict c₀) ⟶
      (((pushforward e₁).rightDerived n).obj (N.restrict c₁)).restrict (Spec.map τ) :=
    (higherDirectImageOpenRestrictionIso c₀ e₀ e₁ (Spec.map τ) hW₀ n).inv.app
      (N.restrict c₁)
  let rfT : E.restrict (Spec.map ρ ≫ j) ⟶ H₀.obj (M.restrict (p₀ ≫ p₁)) :=
    (higherDirectImageOpenRestrictionIso (p₀ ≫ p₁) d₀ f (Spec.map ρ ≫ j)
      (hU₀.paste_horiz hU₁) n).hom.app M
  let rbT : F.restrict (Spec.map τ ≫ v) ⟶ K₀.obj (N.restrict (c₀ ≫ c₁)) :=
    (higherDirectImageOpenRestrictionIso (c₀ ≫ c₁) e₀ b (Spec.map τ ≫ v)
      (hW₀.paste_horiz hW₁) n).hom.app N
  let rbTi : K₀.obj (N.restrict (c₀ ≫ c₁)) ⟶ F.restrict (Spec.map τ ≫ v) :=
    (higherDirectImageOpenRestrictionIso (c₀ ≫ c₁) e₀ b (Spec.map τ ≫ v)
      (hW₀.paste_horiz hW₁) n).inv.app N
  let o₁ : ((pullback g).obj E).restrict v ⟶ (pullback (Spec.map σ)).obj (E.restrict j) :=
    (pullbackOpenSquare v (Spec.map σ) g j hv.symm).hom.app E
  let o₀source : ((pullback (Spec.map σ)).obj (E.restrict j)).restrict (Spec.map τ) ⟶
      P.obj ((E.restrict j).restrict (Spec.map ρ)) :=
    (pullbackOpenSquare (Spec.map τ) (Spec.map σ₀) (Spec.map σ) (Spec.map ρ) hb).hom.app
      (E.restrict j)
  let o₀target : ((pullback (Spec.map σ)).obj
      (((pushforward d₁).rightDerived n).obj (M.restrict p₁))).restrict (Spec.map τ) ⟶
      P.obj ((((pushforward d₁).rightDerived n).obj (M.restrict p₁)).restrict (Spec.map ρ)) :=
    (pullbackOpenSquare (Spec.map τ) (Spec.map σ₀) (Spec.map σ) (Spec.map ρ) hb).hom.app
      (((pushforward d₁).rightDerived n).obj (M.restrict p₁))
  let oT : ((pullback g).obj E).restrict (Spec.map τ ≫ v) ⟶
      P.obj (E.restrict (Spec.map ρ ≫ j)) :=
    (pullbackOpenSquare (Spec.map τ ≫ v) (Spec.map σ₀) g
      (Spec.map ρ ≫ j) ht.symm).hom.app E
  let β₁ := higherDirectImageAffineMap (R := R) (S := S) (X := U₁) (Y := W₁)
    (M := M.restrict p₁) (N := N.restrict c₁) q₁ e₁ d₁ σ hb₁ ψ₁ n
  let β₀ := higherDirectImageAffineMap (R := R₀) (S := S₀) (X := U₀) (Y := W₀)
    (M := (M.restrict p₁).restrict p₀) (N := (N.restrict c₁).restrict c₀)
    q₀ e₀ d₀ σ₀ hb₀ ψ₀ n
  let βT := higherDirectImageAffineMap (R := R₀) (S := S₀) (X := U₀) (Y := W₀)
    (M := M.restrict (p₀ ≫ p₁)) (N := N.restrict (c₀ ≫ c₁)) q₀ e₀ d₀ σ₀ hb₀ ψT n
  let s := (restrictFunctorComp (Spec.map τ) v).hom.app ((pullback g).obj E)
  let t := (restrictFunctorComp (Spec.map τ) v).hom.app F
  let ti := (restrictFunctorComp (Spec.map τ) v).inv.app F
  have hcoef : m ≫ ψ₀ = ψT ≫ (pushforward q₀).map l := by
    have hc := chartCoefficient_comp a p₁ c₁ q₁ hq₁ u p₀ c₀ q₀ hq₀ hqT
    change mi ≫ ψT ≫ (pushforward q₀).map l = ψ₀ at hc
    rw [← hc, Iso.hom_inv_id_app_assoc]
  have hmiddle : P.map (H₀.map m) ≫ β₀ =
      βT ≫ K₀.map l :=
    higherDirectImageAffineMap_naturality (R := R₀) (S := S₀) (X := U₀) (Y := W₀)
      q₀ e₀ d₀ σ₀ hb₀ ψT ψ₀
      (M := M.restrict (p₀ ≫ p₁)) (M' := (M.restrict p₁).restrict p₀)
      (N := N.restrict (c₀ ≫ c₁)) (N' := (N.restrict c₁).restrict c₀)
      m l hcoef n
  have hk : J.map β₁ =
      o₀target ≫
        P.map rf₀ ≫ β₀ ≫ rb₀i :=
    higherDirectImageAffineMap_restrict (R := R) (S := S) (R₀ := R₀) (S₀ := S₀)
      (X := U₁) (Y := W₁) (X₀ := U₀) (Y₀ := W₀)
      q₁ d₁ e₁ σ hb₁ p₀ c₀ q₀ d₀ e₀ ρ τ σ₀
      hU₀ hW₀ hq₀ hb₀ hb (M := M.restrict p₁) (N := N.restrict c₁) ψ₁ n
  have htarget : ti ≫ rbT ≫ K₀.map l =
      J.map rb₁ ≫ rb₀ :=
    higherDirectImageOpenRestrictionIso_comp c₁ e₁ b v c₀ e₀ (Spec.map τ)
      hW₁ hW₀ (hW₀.paste_horiz hW₁) N n
  have ho : oT = s ≫ J.map o₁ ≫
      o₀source ≫ P.map ((restrictFunctorComp (Spec.map ρ) j).inv.app E) :=
    pullbackOpenSquare_comp_hom_app v (Spec.map σ) g j (Spec.map τ) (Spec.map ρ)
      (Spec.map σ₀) hv.symm hb ht.symm E
  have hn :=
    (pullbackOpenSquare (Spec.map τ) (Spec.map σ₀) (Spec.map σ) (Spec.map ρ) hb).hom.naturality
      rf₁
  change J.map ((pullback (Spec.map σ)).map rf₁) ≫
      o₀target =
    o₀source ≫
      P.map ((restrictFunctor (Spec.map ρ)).map rf₁) at hn
  have hf := congrArg P.map
    (higherDirectImageOpenRestrictionIso_comp p₁ d₁ f j p₀ d₀ (Spec.map ρ)
      hU₁ hU₀ (hU₀.paste_horiz hU₁) M n)
  simp only [Functor.map_comp] at hf
  have hsource : s ≫ J.map o₁ ≫
      J.map ((pullback (Spec.map σ)).map rf₁) ≫
      o₀target ≫
      P.map rf₀ =
    oT ≫ P.map rfT ≫ P.map (H₀.map m) :=
    localSource_paste _ _ _ _ _ _ _ _ _ _ _ ho hn hf
  exact localComparison_map_paste
    (C := (Spec S).Modules) (D := (Spec S₀).Modules) J
    (E₁ := ((pullback g).obj E).restrict v) (F₁ := F.restrict v)
    (A₁ := (pullback (Spec.map σ)).obj (E.restrict j))
    (B₁ := (pullback (Spec.map σ)).obj
      (((pushforward d₁).rightDerived n).obj (M.restrict p₁)))
    (C₁ := ((pushforward e₁).rightDerived n).obj (N.restrict c₁))
    (E₀ := ((pullback g).obj E).restrict (Spec.map τ ≫ v))
    (F₀ := F.restrict (Spec.map τ ≫ v))
    (A₀ := P.obj (E.restrict (Spec.map ρ ≫ j)))
    (B₀ := P.obj (H₀.obj (M.restrict (p₀ ≫ p₁))))
    (C₀ := K₀.obj (N.restrict (c₀ ≫ c₁)))
    (D₁ := P.obj ((((pushforward d₁).rightDerived n).obj (M.restrict p₁)).restrict
      (Spec.map ρ)))
    (D₂ := P.obj (H₀.obj ((M.restrict p₁).restrict p₀)))
    (C₂ := K₀.obj ((N.restrict c₁).restrict c₀))
    s t ti o₁
    ((pullback (Spec.map σ)).map rf₁) β₁ rb₁ rb₁i
    oT (P.map rfT) βT rbT rbTi
    o₀target
    (P.map rf₀) β₀
    rb₀ rb₀i
    (P.map (H₀.map m)) (K₀.map l)
    ((restrictFunctorComp (Spec.map τ) v).hom_inv_id_app F)
    ((higherDirectImageOpenRestrictionIso c₁ e₁ b v hW₁ n).hom_inv_id_app N)
    ((higherDirectImageOpenRestrictionIso (c₀ ≫ c₁) e₀ b (Spec.map τ ≫ v)
      (hW₀.paste_horiz hW₁) n).inv_hom_id_app N)
    ((higherDirectImageOpenRestrictionIso c₀ e₀ e₁ (Spec.map τ) hW₀ n).hom_inv_id_app
      (N.restrict c₁))
    hk hsource hmiddle htarget

end AlgebraicGeometry.Scheme.Modules.Nonflat
