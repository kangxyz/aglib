/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Descent.Zariski
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Gluing module sheaves along open immersions

Let `f : ∀ i, X i ⟶ S` be a family of open immersions (`ι : Type u`) and `D` a descent datum
for the module-sheaf pullback pseudofunctor relative to `f`. This file constructs the glued
module sheaf and compares its descent datum with `D`, following the gluing of sheaves in
Stacks, Section 6.33 (Tag 00AK), Lemmas 6.33.2 and 6.33.3 (Tags 00AL, 00AM); the tags are
those of Stacks revision a04446e5; their statements were read on the Stacks website on
2026-10-17. The overlaps are Mathlib's `Limits.pullback (f i) (f k)`. Statements are generic in
the family: instantiating descent-data statements at concrete families of open subschemes made
the kernel time out.

* `transition`, `hom_eq_transition`, `transitionPullback`: the descent-datum morphism on the
  overlaps, in restriction and pullback form.
* `first`, `second`: S-module maps comparing the pushforwards of `D.obj i` and `D.obj k` on the
  overlap; `matching`, `gluedPresheaf`, `gluedPresheaf_isSheaf`, `glued`: matching families of
  sections form a sheaf of modules.
* `projection`, `toObj : (glued f D).restrict (f l) ⟶ D.obj l`, `projection_comp_first`,
  `isIso_second_app`, `projection_app_injective`, `toObj_comm`, `phi`, `phi_comm_aux`,
  `phi_comm_pure`.
* `CategoryTheory.Pseudofunctor.DescentData.comm_of_overlap` (generic): compatibility of a
  family of morphisms of descent data can be checked on overlaps through which every pair of maps
  factors; `exists_lift_pullback` supplies the factorization.
* `descentData_comm_of`, `phiDescent`, `comparison : (toDescentData f).obj (glued f D) ⟶ D`.
* `isIso_toObj`, `comparisonIso`, `essSurj_toDescentData`, `isStackFor_ofArrows`: effective
  descent, given surjectivity of the projections over opens in the range of `f l`.
* `ProjectionSurjective` (the cocycle step, proved as `projectionSurjective` in
  `Descent/ZariskiStack.lean`) and
  `isStack_zariskiTopology_of_projectionSurjective`, with the quasi-coherent and line-bundle
  corollaries.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Opposite Bicategory Pseudofunctor TopologicalSpace

namespace CategoryTheory.Pseudofunctor.DescentData

open LocallyDiscreteOpToCat

variable {C : Type*} [Category C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat}
  {ι : Type*} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}

/-- The compatibility of a family of morphisms of descent data can be checked on a family of
overlaps `W i k` through which every pair of maps to `X i`, `X k` over `S` factors. -/
lemma comm_of_overlap {D₁ D₂ : F.DescentData f} (φ : ∀ i, D₁.obj i ⟶ D₂.obj i)
    (W : ι → ι → C) (p₁ : ∀ i k, W i k ⟶ X i) (p₂ : ∀ i k, W i k ⟶ X k) (q : ∀ i k, W i k ⟶ S)
    (hp₁ : ∀ i k, p₁ i k ≫ f i = q i k) (hp₂ : ∀ i k, p₂ i k ≫ f k = q i k)
    (hlift : ∀ ⦃Y : C⦄ (q' : Y ⟶ S) ⦃i k : ι⦄ (f₁ : Y ⟶ X i) (f₂ : Y ⟶ X k),
      f₁ ≫ f i = q' → f₂ ≫ f k = q' → ∃ g : Y ⟶ W i k, g ≫ p₁ i k = f₁ ∧ g ≫ p₂ i k = f₂)
    (h : ∀ i k, (F.map (p₁ i k).op.toLoc).toFunctor.map (φ i) ≫
        D₂.hom (q i k) (p₁ i k) (p₂ i k) (hp₁ i k) (hp₂ i k) =
      D₁.hom (q i k) (p₁ i k) (p₂ i k) (hp₁ i k) (hp₂ i k) ≫
        (F.map (p₂ i k).op.toLoc).toFunctor.map (φ k))
    ⦃Y : C⦄ (q' : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q') (hf₂ : f₂ ≫ f i₂ = q') :
    (F.map f₁.op.toLoc).toFunctor.map (φ i₁) ≫ D₂.hom q' f₁ f₂ hf₁ hf₂ =
      D₁.hom q' f₁ f₂ hf₁ hf₂ ≫ (F.map f₂.op.toLoc).toFunctor.map (φ i₂) := by
  obtain ⟨g, hg₁, hg₂⟩ := hlift q' f₁ f₂ hf₁ hf₂
  have hq : g ≫ q i₁ i₂ = q' := by rw [← hp₁, ← Category.assoc, hg₁, hf₁]
  rw [← D₁.pullHom_hom g (q i₁ i₂) q' hq (p₁ i₁ i₂) (p₂ i₁ i₂) (hp₁ _ _) (hp₂ _ _) f₁ f₂ hg₁ hg₂,
    ← D₂.pullHom_hom g (q i₁ i₂) q' hq (p₁ i₁ i₂) (p₂ i₁ i₂) (hp₁ _ _) (hp₂ _ _) f₁ f₂ hg₁ hg₂]
  simp only [pullHom, Category.assoc]
  rw [Pseudofunctor.mapComp'_hom_naturality_assoc, ← Functor.map_comp_assoc, h,
    Functor.map_comp_assoc, Pseudofunctor.mapComp'_inv_naturality]

end CategoryTheory.Pseudofunctor.DescentData

namespace AlgebraicGeometry.Scheme.Modules.OpenCoverGluing

variable {S : Scheme.{u}} {ι : Type u} {X : ι → Scheme.{u}} (f : ∀ i, X i ⟶ S)
  [∀ i, IsOpenImmersion (f i)] (D : pullbackPseudofunctor.{u}.DescentData f)

/-- The object of the descent datum over `X i`. -/
abbrev obj (i : ι) : (X i).Modules := D.obj i

/-- The first projection from the overlap `X i ×_S X k`. -/
abbrev fst (i k : ι) : Limits.pullback (f i) (f k) ⟶ X i := Limits.pullback.fst (f i) (f k)

/-- The second projection from the overlap `X i ×_S X k`. -/
abbrev snd (i k : ι) : Limits.pullback (f i) (f k) ⟶ X k := Limits.pullback.snd (f i) (f k)

omit [∀ i, IsOpenImmersion (f i)] in
lemma fst_ι_eq_snd_ι (i k : ι) : fst f i k ≫ f i = snd f i k ≫ f k :=
  Limits.pullback.condition

/-- The transition of the descent datum on `U i ⊓ U k`, in restriction form. -/
def transition (i k : ι) :
    (obj f D i).restrict (fst f i k) ⟶ (obj f D k).restrict (snd f i k) :=
  (restrictFunctorIsoPullback (fst f i k)).hom.app (obj f D i) ≫
    D.hom (snd f i k ≫ (f k)) (fst f i k) (snd f i k) (fst_ι_eq_snd_ι f i k) rfl ≫
      (restrictFunctorIsoPullback (snd f i k)).inv.app (obj f D k)

/-- The pushforward of the object over `U i` to `S`. -/
abbrev ambient (i : ι) : S.Modules := (pushforward (f i)).obj (obj f D i)

/-- The pushforward to `S`, through `U k`, of the restriction to `U i ⊓ U k` of the object
over `U k`. -/
abbrev overlapAmbient (i k : ι) : S.Modules :=
  (pushforward (f k)).obj ((pushforward (snd f i k)).obj ((obj f D k).restrict (snd f i k)))

/-- Restriction from `U i` to `U i ⊓ U k`, followed by the transition to the object over `U k`. -/
def first (i k : ι) : ambient f D i ⟶ overlapAmbient f D i k :=
  (pushforward (f i)).map ((restrictAdjunction (fst f i k)).unit.app (obj f D i) ≫
      (pushforward (fst f i k)).map (transition f D i k)) ≫
    (pushforwardComp (fst f i k) (f i)).hom.app _ ≫
      (pushforwardCongr (fst_ι_eq_snd_ι f i k)).hom.app _ ≫
        (pushforwardComp (snd f i k) (f k)).inv.app _

/-- Restriction from `U k` to `U i ⊓ U k`. -/
def second (i k : ι) : ambient f D k ⟶ overlapAmbient f D i k :=
  (pushforward (f k)).map ((restrictAdjunction (snd f i k)).unit.app (obj f D k))

/-- Matching families of sections on an open `V` of `S`. -/
def matching (V : S.Opens) :
    Submodule (S.ringCatSheaf.obj.obj (op V)) (∀ i, (ambient f D i).val.obj (op V)) where
  carrier := {s | ∀ i k, (first f D i k).val.app (op V) (s i) =
    (second f D i k).val.app (op V) (s k)}
  add_mem' {s t} hs ht i k := by
    simp only [Pi.add_apply, map_add, hs i k, ht i k]
  zero_mem' i k := by
    simp only [Pi.zero_apply, map_zero]
  smul_mem' r s hs i k :=
    (((first f D i k).val.app (op V)).hom.map_smul r (s i)).trans
      ((congrArg (r • ·) (hs i k)).trans
        (((second f D i k).val.app (op V)).hom.map_smul r (s k)).symm)

/-- The glued presheaf of modules: matching families of sections. -/
def gluedPresheaf : _root_.PresheafOfModules.{u} S.ringCatSheaf.obj where
  obj V := ModuleCat.of _ (matching f D V.unop)
  map {V W} g := ModuleCat.ofHom
    (X := ModuleCat.of (S.ringCatSheaf.obj.obj V) (matching f D V.unop))
    (Y := (ModuleCat.restrictScalars (S.ringCatSheaf.obj.map g).hom).obj
      (ModuleCat.of (S.ringCatSheaf.obj.obj W) (matching f D W.unop)))
    { toFun s := ⟨fun i ↦ (ambient f D i).val.map g (s.1 i), fun i k ↦
        (_root_.PresheafOfModules.naturality_apply (first f D i k).val g (s.1 i)).trans
          ((congrArg _ (s.2 i k)).trans
            (_root_.PresheafOfModules.naturality_apply (second f D i k).val g (s.1 k)).symm)⟩
      map_add' s t := by
        apply Subtype.ext
        funext i
        exact map_add _ _ _
      map_smul' r s := by
        apply Subtype.ext
        funext i
        exact _root_.PresheafOfModules.map_smul _ _ _ _ }
  map_id V := by
    ext s
    apply Subtype.ext
    funext i
    exact congrArg (fun φ ↦ φ (s.1 i)) congr(ModuleCat.Hom.hom $((ambient f D i).val.map_id V))
  map_comp g₁ g₂ := by
    ext s
    apply Subtype.ext
    funext i
    exact congrArg (fun φ ↦ φ (s.1 i))
      congr(ModuleCat.Hom.hom $((ambient f D i).val.map_comp g₁ g₂))

lemma gluedPresheaf_isSheaf :
    Presheaf.IsSheaf (Opens.grothendieckTopology S) (gluedPresheaf f D).presheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing _).mpr
  intro κ V sf hsf
  let F (i : ι) : TopCat.Sheaf Ab S := ⟨(ambient f D i).presheaf, (ambient f D i).isSheaf⟩
  let G (i k : ι) : TopCat.Sheaf Ab S :=
    ⟨(overlapAmbient f D i k).presheaf, (overlapAmbient f D i k).isSheaf⟩
  let t (a : κ) : matching f D (V a) := sf a
  have hcomp (i : ι) : TopCat.Presheaf.IsCompatible (F i).1 V (fun a ↦ (t a).1 i) := fun a b ↦
    congrArg (fun s : matching f D (V a ⊓ V b) ↦ s.1 i) (hsf a b)
  choose g hg hgu using fun i ↦ (F i).existsUnique_gluing V _ (hcomp i)
  have hg' (i : ι) (a : κ) : (ambient f D i).val.map (Opens.leSupr V a).op (g i) = (t a).1 i :=
    hg i a
  have hmatch : g ∈ matching f D (iSup V) := by
    intro i k
    apply (G i k).eq_of_locally_eq V
    intro a
    have e₁ := (_root_.PresheafOfModules.naturality_apply (first f D i k).val
      (Opens.leSupr V a).op (g i)).symm
    have e₂ := (_root_.PresheafOfModules.naturality_apply (second f D i k).val
      (Opens.leSupr V a).op (g k)).symm
    refine e₁.trans (Eq.trans ?_ e₂.symm)
    rw [hg' i a, hg' k a]
    exact (t a).2 i k
  refine ⟨⟨g, hmatch⟩, fun a ↦ ?_, fun s hs ↦ ?_⟩
  · apply Subtype.ext
    funext i
    exact hg' i a
  · let s' : matching f D (iSup V) := s
    change s' = _
    apply Subtype.ext
    funext i
    exact hgu i (s'.1 i) (fun a ↦ congrArg (fun x : matching f D (V a) ↦ x.1 i) (hs a))

/-- The module sheaf glued from the descent datum. -/
def glued : S.Modules := ⟨gluedPresheaf f D, gluedPresheaf_isSheaf f D⟩

/-- The projection from the glued sheaf to the pushforward of the object over `U l`. -/
def projection (l : ι) : glued f D ⟶ ambient f D l :=
  ⟨{ app := fun V ↦ ModuleCat.ofHom (X := (glued f D).val.obj V)
        (Y := (ambient f D l).val.obj V)
        { toFun := fun s ↦ (s : matching f D V.unop).1 l,
          map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl },
      naturality := fun _ ↦ rfl }⟩

lemma projection_app_apply (l : ι) (V : S.Opens) (s : matching f D V) :
    (projection f D l).app V s = s.1 l :=
  rfl

/-- The comparison of the restriction of the glued sheaf to `U l` with the object over `U l`. -/
def toObj (l : ι) : (glued f D).restrict (f l) ⟶ obj f D l :=
  ((restrictAdjunction (f l)).homEquiv _ _).symm (projection f D l)

lemma toObj_app (l : ι) (W : (X l).Opens) :
    (toObj f D l).app W = (projection f D l).app ((f l) ''ᵁ W) ≫
      (obj f D l).presheaf.map (eqToHom ((f l).preimage_image_eq W).symm).op := by
  rw [toObj, Adjunction.homEquiv_counit, Hom.comp_app, restrictAdjunction_counit_app_app]
  rfl

/-- Over an open contained in the range of `f l`, restriction from `X i` to `X l ×_S X i` is
invertible. -/
lemma isIso_second_app {l i : ι} {V : S.Opens} (hV : V ≤ (f l).opensRange) :
    IsIso ((second f D l i).app V) := by
  have hle : (f i) ⁻¹ᵁ V ≤ (snd f l i) ''ᵁ ((snd f l i) ⁻¹ᵁ ((f i) ⁻¹ᵁ V)) := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Hom.opensRange_pullbackSnd]
    exact le_inf (Scheme.Hom.preimage_mono _ hV) le_rfl
  have he := le_antisymm (Scheme.Hom.image_preimage_le _ _) hle
  have : (homOfLE (Scheme.Hom.image_preimage_le (snd f l i) ((f i) ⁻¹ᵁ V))).op =
      eqToHom (congrArg op he.symm) := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  change IsIso ((obj f D i).presheaf.map
    (homOfLE (Scheme.Hom.image_preimage_le (snd f l i) ((f i) ⁻¹ᵁ V))).op)
  rw [this]
  infer_instance

/-- The glued sections match: the two restrictions to `U i ⊓ U k` of the projections agree. -/
lemma projection_comp_first (i k : ι) :
    projection f D i ≫ first f D i k = projection f D k ≫ second f D i k := by
  ext V : 1
  ext s
  exact (s : matching f D V).2 i k

/-- Over an open contained in `U l`, a matching family is determined by its component at `l`. -/
lemma projection_app_injective {l : ι} {V : S.Opens} (hV : V ≤ (f l).opensRange) :
    Function.Injective ((projection f D l).app V) := by
  intro s t hst
  let s' : matching f D V := s
  let t' : matching f D V := t
  change s' = t'
  have hl : s'.1 l = t'.1 l := hst
  apply Subtype.ext
  funext i
  have : IsIso ((second f D l i).app V) := isIso_second_app f D hV
  apply (ConcreteCategory.bijective_of_isIso ((second f D l i).app V)).1
  change (second f D l i).val.app (op V) (s'.1 i) = (second f D l i).val.app (op V) (t'.1 i)
  rw [← s'.2 l i, ← t'.2 l i, hl]

/-- The unit of the restriction adjunction is compatible with `restrictFunctorCongr` and
`pushforwardCongr`. -/
lemma restrictAdjunction_unit_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    [IsOpenImmersion f] [IsOpenImmersion g] (M : Y.Modules) :
    (restrictAdjunction g).unit.app M ≫ (pushforward g).map ((restrictFunctorCongr h).inv.app M) =
      (restrictAdjunction f).unit.app M ≫ (pushforwardCongr h).hom.app _ := by
  subst h
  have h₁ : (restrictFunctorCongr (rfl : f = f)).inv.app M = 𝟙 _ := by
    ext U : 1
    simp only [restrictFunctorCongr_inv_app_app, eqToHom_refl, op_id, Hom.id_app]
    exact M.presheaf.map_id _
  have h₂ : (pushforwardCongr (rfl : f = f)).hom.app ((restrictFunctor f).obj M) = 𝟙 _ := by
    ext U : 1
    simp only [pushforwardCongr_hom_app_app, eqToHom_refl, op_id, Hom.id_app]
    exact ((restrictFunctor f).obj M).presheaf.map_id _
  rw [h₁, h₂, CategoryTheory.Functor.map_id]

lemma unit_comp_map_toObj (l : ι) :
    (restrictAdjunction (f l)).unit.app (glued f D) ≫
      (pushforward (f l)).map (toObj f D l) = projection f D l := by
  exact ((restrictAdjunction (f l)).homEquiv_unit _ _ (toObj f D l)).symm.trans
    (Equiv.apply_symm_apply _ _)

/-- The comparison maps are compatible with the transitions, in restriction form. -/
lemma toObj_comm (i k : ι) :
    (restrictFunctorCongr (fst_ι_eq_snd_ι f i k)).inv.app (glued f D) ≫
        (restrictFunctorComp (fst f i k) (f i)).hom.app (glued f D) ≫
          (restrictFunctor (fst f i k)).map (toObj f D i) ≫ transition f D i k =
      (restrictFunctorComp (snd f i k) (f k)).hom.app (glued f D) ≫
        (restrictFunctor (snd f i k)).map (toObj f D k) := by
  apply ((restrictAdjunction (snd f i k ≫ (f k))).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  have hR : (restrictAdjunction (snd f i k ≫ (f k))).unit.app (glued f D) ≫
      (pushforward (snd f i k ≫ (f k))).map
        ((restrictFunctorComp (snd f i k) (f k)).hom.app (glued f D) ≫
          (restrictFunctor (snd f i k)).map (toObj f D k)) =
      projection f D k ≫ second f D i k ≫
        (pushforwardComp (snd f i k) (f k)).hom.app _ := by
    rw [Functor.map_comp, reassoc_of% (restrictAdjunction_comp_unit_app (snd f i k) (f k)
      (glued f D)), ← (pushforwardComp (snd f i k) (f k)).hom.naturality]
    dsimp only [Functor.comp_map]
    rw [← Functor.map_comp_assoc, Adjunction.unit_naturality, Functor.map_comp_assoc,
      reassoc_of% (unit_comp_map_toObj f D k)]
    rfl
  have hL : (restrictAdjunction (snd f i k ≫ (f k))).unit.app (glued f D) ≫
      (pushforward (snd f i k ≫ (f k))).map
        ((restrictFunctorCongr (fst_ι_eq_snd_ι f i k)).inv.app (glued f D) ≫
          (restrictFunctorComp (fst f i k) (f i)).hom.app (glued f D) ≫
            (restrictFunctor (fst f i k)).map (toObj f D i) ≫ transition f D i k) =
      projection f D i ≫ first f D i k ≫
        (pushforwardComp (snd f i k) (f k)).hom.app _ := by
    rw [Functor.map_comp, reassoc_of% (restrictAdjunction_unit_congr (fst_ι_eq_snd_ι f i k)
      (glued f D)), ← (pushforwardCongr (fst_ι_eq_snd_ι f i k)).hom.naturality]
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% (restrictAdjunction_comp_unit_app (fst f i k) (f i) (glued f D)),
      ← (pushforwardComp (fst f i k) (f i)).hom.naturality_assoc,
      ← (pushforwardComp (fst f i k) (f i)).hom.naturality_assoc]
    dsimp only [Functor.comp_map]
    rw [← Functor.map_comp_assoc, Adjunction.unit_naturality, Functor.map_comp_assoc,
      reassoc_of% (unit_comp_map_toObj f D i)]
    simp only [first, Functor.map_comp, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [hL, hR, reassoc_of% (projection_comp_first f D i k)]

/-- The comparison maps from the pullbacks of the glued sheaf. -/
def phi (l : ι) : (pullback (f l)).obj (glued f D) ⟶ obj f D l :=
  (restrictFunctorIsoPullback (f l)).inv.app (glued f D) ≫ toObj f D l

/-- The overlap compatibility of the comparison maps, stated with module-sheaf functors only. -/
lemma phi_comm_aux (i k : ι) :
    (pullback (fst f i k)).map (phi f D i) ≫
        ((restrictFunctorIsoPullback (fst f i k)).inv.app (obj f D i) ≫ transition f D i k ≫
          (restrictFunctorIsoPullback (snd f i k)).hom.app (obj f D k)) =
      ((pullbackComp (fst f i k) (f i)).hom.app (glued f D) ≫
          (pullbackCongr (fst_ι_eq_snd_ι f i k)).hom.app (glued f D) ≫
            (pullbackComp (snd f i k) (f k)).inv.app (glued f D)) ≫
        (pullback (snd f i k)).map (phi f D k) := by
  have c₁ := restrictFunctorIsoPullback_comp_hom_app (fst f i k) (f i) (glued f D)
  have c₂ := restrictFunctorIsoPullback_comp_hom_app (snd f i k) (f k) (glued f D)
  have c₃ := restrictFunctorIsoPullback_congr_hom_app (fst_ι_eq_snd_ι f i k) (glued f D)
  rw [← cancel_epi ((restrictFunctorCongr (fst_ι_eq_snd_ι f i k)).inv.app (glued f D) ≫
      (restrictFunctorIsoPullback (fst f i k ≫ (f i))).hom.app (glued f D) ≫
        (pullbackComp (fst f i k) (f i)).inv.app (glued f D)),
    ← cancel_mono ((restrictFunctorIsoPullback (snd f i k)).inv.app (obj f D k))]
  simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id, Iso.inv_hom_id_app_assoc]
  rw [reassoc_of% c₃, reassoc_of% c₂, reassoc_of% c₁,
    ← (restrictFunctorIsoPullback (fst f i k)).hom.naturality_assoc,
    ← (restrictFunctorIsoPullback (snd f i k)).hom.naturality_assoc]
  simp only [Iso.hom_inv_id_app, Category.comp_id, Iso.inv_hom_id_app_assoc, phi,
    Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp, Iso.hom_inv_id_app_assoc]
  exact toObj_comm f D i k

omit [∀ i, IsOpenImmersion (f i)] in
/-- Every pair of maps to `X i` and `X k` over `S` factors through `X i ×_S X k`. -/
lemma exists_lift_pullback {Y : Scheme.{u}} (q' : Y ⟶ S) {i k : ι} (f₁ : Y ⟶ X i)
    (f₂ : Y ⟶ X k) (hf₁ : f₁ ≫ f i = q') (hf₂ : f₂ ≫ f k = q') :
    ∃ g : Y ⟶ Limits.pullback (f i) (f k), g ≫ fst f i k = f₁ ∧ g ≫ snd f i k = f₂ :=
  ⟨Limits.pullback.lift f₁ f₂ (hf₁.trans hf₂.symm), Limits.pullback.lift_fst _ _ _,
    Limits.pullback.lift_snd _ _ _⟩

-- The descent-datum morphism is compared with module-sheaf maps: relaxed instance transparency
-- lets `pullbackPseudofunctor.obj _` (a `Cat.of`) be seen as `X.Modules`.
set_option backward.isDefEq.respectTransparency false in
/-- The descent-datum morphism on `X i ×_S X k` in terms of its restriction form. -/
lemma hom_eq_transition (i k : ι) :
    D.hom (snd f i k ≫ (f k)) (fst f i k) (snd f i k) (fst_ι_eq_snd_ι f i k) rfl =
      (restrictFunctorIsoPullback (fst f i k)).inv.app (obj f D i) ≫ transition f D i k ≫
        (restrictFunctorIsoPullback (snd f i k)).hom.app (obj f D k) := by
  simp only [transition, Category.assoc, Iso.inv_hom_id_app, Iso.inv_hom_id_app_assoc]
  exact (Category.comp_id _).symm

/-- The transition on `X i ×_S X k`, in pullback form, as a morphism of module sheaves. -/
def transitionPullback (i k : ι) :
    (pullback (fst f i k)).obj (obj f D i) ⟶ (pullback (snd f i k)).obj (obj f D k) :=
  (restrictFunctorIsoPullback (fst f i k)).inv.app (obj f D i) ≫ transition f D i k ≫
    (restrictFunctorIsoPullback (snd f i k)).hom.app (obj f D k)

lemma hom_eq_transitionPullback (i k : ι) :
    D.hom (snd f i k ≫ (f k)) (fst f i k) (snd f i k) (fst_ι_eq_snd_ι f i k) rfl =
      transitionPullback f D i k :=
  hom_eq_transition f D i k

/-- The overlap compatibility of `phi`, with module-sheaf functors only, in the form produced by
`pullbackPseudofunctor_toDescentData_obj_hom`. -/
lemma phi_comm_pure (i k : ι) :
    (pullback (fst f i k)).map (phi f D i) ≫ transitionPullback f D i k =
      ((pullbackComp (fst f i k) (f i)).hom.app (glued f D) ≫
          (pullbackCongr (fst_ι_eq_snd_ι f i k)).hom.app (glued f D) ≫
            (pullbackCongr (rfl : snd f i k ≫ f k = snd f i k ≫ f k).symm).hom.app (glued f D) ≫
              (pullbackComp (snd f i k) (f k)).inv.app (glued f D)) ≫
        (pullback (snd f i k)).map (phi f D k) := by
  have hrfl : (pullbackCongr (rfl : snd f i k ≫ f k = snd f i k ≫ f k).symm).hom.app
      (glued f D) = 𝟙 _ := by simp [pullbackCongr]
  rw [hrfl, Category.id_comp]
  exact phi_comm_aux f D i k

-- The object `M` and the maps `φ` are variables, which keeps the kernel check small.
/-- The overlap compatibility in descent-data form, from its module-sheaf form. -/
lemma descentData_comm_of {M : S.Modules}
    (φ : ∀ l, ((pullbackPseudofunctor.toDescentData f).obj M).obj l ⟶ D.obj l)
    (h : ∀ i k, (pullback (fst f i k)).map (φ i) ≫ transitionPullback f D i k =
      ((pullbackComp (fst f i k) (f i)).hom.app M ≫
          (pullbackCongr (fst_ι_eq_snd_ι f i k)).hom.app M ≫
            (pullbackCongr (rfl : snd f i k ≫ f k = snd f i k ≫ f k).symm).hom.app M ≫
              (pullbackComp (snd f i k) (f k)).inv.app M) ≫ (pullback (snd f i k)).map (φ k))
    (i k : ι) :
    (pullbackPseudofunctor.map (fst f i k).op.toLoc).toFunctor.map (φ i) ≫
        D.hom (snd f i k ≫ f k) (fst f i k) (snd f i k) (fst_ι_eq_snd_ι f i k) rfl =
      ((pullbackPseudofunctor.toDescentData f).obj M).hom (snd f i k ≫ f k) (fst f i k)
          (snd f i k) (fst_ι_eq_snd_ι f i k) rfl ≫
        (pullbackPseudofunctor.map (snd f i k).op.toLoc).toFunctor.map (φ k) := by
  rw [hom_eq_transitionPullback, pullbackPseudofunctor_toDescentData_obj_hom]
  exact h i k

/-- The comparison maps, typed as components of a morphism of descent data. -/
def phiDescent (l : ι) :
    ((pullbackPseudofunctor.toDescentData f).obj (glued f D)).obj l ⟶ D.obj l :=
  phi f D l

/-- The comparison morphism from the descent datum of the glued sheaf to `D`. -/
def comparison : (pullbackPseudofunctor.toDescentData f).obj (glued f D) ⟶ D where
  hom := phiDescent f D
  comm := DescentData.comm_of_overlap (F := pullbackPseudofunctor)
    (D₁ := (pullbackPseudofunctor.toDescentData f).obj (glued f D)) (D₂ := D) (phiDescent f D)
    (fun i k ↦ Limits.pullback (f i) (f k)) (fst f) (snd f) (fun i k ↦ snd f i k ≫ f k)
    (fst_ι_eq_snd_ι f) (fun _ _ ↦ rfl)
    (fun _ q' _ _ f₁ f₂ h₁ h₂ ↦ exists_lift_pullback f q' f₁ f₂ h₁ h₂)
    (descentData_comm_of f D (phiDescent f D) (phi_comm_pure f D))

/-- If the projection to `X l` is surjective on sections over every open in the range of `f l`,
the comparison `toObj l` is an isomorphism. -/
lemma isIso_toObj (l : ι)
    (hsurj : ∀ V : S.Opens, V ≤ (f l).opensRange →
      Function.Surjective ((projection f D l).app V)) :
    IsIso (toObj f D l) := by
  rw [Hom.isIso_iff_isIso_app]
  intro W
  rw [toObj_app]
  have hV : (f l) ''ᵁ W ≤ (f l).opensRange := Scheme.Hom.image_le_opensRange _ _
  have h₁ : IsIso ((projection f D l).app ((f l) ''ᵁ W)) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ⟨projection_app_injective f D hV, hsurj _ hV⟩
  have h₂ : IsIso ((obj f D l).presheaf.map (eqToHom ((f l).preimage_image_eq W).symm).op) :=
    inferInstance
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h₁ h₂

-- The components of `comparison` are typed in `pullbackPseudofunctor.obj _` (a `Cat.of`); the
-- isomorphisms are built in `X.Modules`, which needs relaxed instance transparency.
set_option backward.isDefEq.respectTransparency false in
/-- If every comparison map is invertible, the descent datum of the glued sheaf is isomorphic
to `D`. -/
def comparisonIso (h : ∀ l, IsIso (phi f D l)) :
    (pullbackPseudofunctor.toDescentData f).obj (glued f D) ≅ D :=
  DescentData.isoMk (fun l ↦ asIso (phi f D l)) (comparison f D).comm

/-- Essential surjectivity of `toDescentData f`, given surjectivity of the projections. -/
theorem essSurj_toDescentData
    (hsurj : ∀ (D : pullbackPseudofunctor.{u}.DescentData f) (l : ι) (V : S.Opens),
      V ≤ (f l).opensRange → Function.Surjective ((projection f D l).app V)) :
    (pullbackPseudofunctor.toDescentData f).EssSurj :=
  ⟨fun D ↦ ⟨glued f D, ⟨comparisonIso f D fun l ↦ by
    have := isIso_toObj f D l (hsurj D l)
    unfold phi
    infer_instance⟩⟩⟩

/-- Effective descent along a jointly surjective family of open immersions indexed by a small
type, given surjectivity of the projections. -/
theorem isStackFor_ofArrows (hf : ∀ x : S, ∃ (i : ι) (y : X i), f i y = x)
    (hsurj : ∀ (D : pullbackPseudofunctor.{u}.DescentData f) (l : ι) (V : S.Opens),
      V ≤ (f l).opensRange → Function.Surjective ((projection f D l).app V)) :
    pullbackPseudofunctor.IsStackFor (Presieve.ofArrows X f) := by
  rw [isStackFor_ofArrows_iff]
  have hff := fullyFaithfulToDescentDataOfOpenImmersion f hf
  have := hff.full
  have := hff.faithful
  have := essSurj_toDescentData f hsurj
  exact { }

end AlgebraicGeometry.Scheme.Modules.OpenCoverGluing

namespace AlgebraicGeometry.Scheme.Modules

/-- The cocycle step of Zariski gluing: for every small family of open immersions and every
descent datum, the projection of the glued sheaf to `X l` is surjective on sections over opens in
the range of `f l`. -/
def ProjectionSurjective : Prop :=
  ∀ (S : Scheme.{u}) (ι : Type u) (X : ι → Scheme.{u}) (f : ∀ i, X i ⟶ S)
    [∀ i, IsOpenImmersion (f i)] (D : pullbackPseudofunctor.{u}.DescentData f) (l : ι)
    (V : S.Opens), V ≤ (f l).opensRange →
      Function.Surjective ((OpenCoverGluing.projection f D l).app V)

/-- Module sheaves form a stack for the Zariski topology, given the cocycle step. -/
theorem isStack_zariskiTopology_of_projectionSurjective (h : ProjectionSurjective.{u}) :
    pullbackPseudofunctor.{u}.IsStack Scheme.zariskiTopology := by
  refine IsStack.of_precoverage (J := Scheme.zariskiPrecoverage) fun S R hR ↦ ?_
  obtain ⟨ι, X, f, rfl⟩ := R.exists_eq_ofArrows
  rw [Scheme.ofArrows_mem_precoverage_iff] at hR
  obtain ⟨hcov, hopen⟩ := hR
  have hI : ∀ i, IsOpenImmersion (f i) := hopen
  choose idx hidx using hcov
  have hstack := OpenCoverGluing.isStackFor_ofArrows (fun x : S ↦ f (idx x))
    (fun x ↦ ⟨x, hidx x⟩) (fun D l V hV ↦ h S S _ (fun x : S ↦ f (idx x)) D l V hV)
  refine hstack.of_le (J := Scheme.zariskiTopology) _ ?_ ?_
  · refine Precoverage.generate_mem_toGrothendieck ?_
    rw [Scheme.ofArrows_mem_precoverage_iff]
    exact ⟨fun x ↦ ⟨x, hidx x⟩, fun x ↦ hI (idx x)⟩
  · rintro _ _ ⟨x⟩
    exact Presieve.ofArrows.mk (idx x)

/-- Quasi-coherent sheaves form a Zariski stack, given the cocycle step. -/
theorem isStack_quasicoherentPseudofunctor_of_projectionSurjective
    (h : ProjectionSurjective.{u}) :
    quasicoherentPseudofunctor.{u}.IsStack Scheme.zariskiTopology :=
  have := isStack_zariskiTopology_of_projectionSurjective h
  isStack_quasicoherentPseudofunctor_of_isStack

/-- Line bundles form a Zariski stack, given the cocycle step. -/
theorem isStack_lineBundlePseudofunctor_of_projectionSurjective
    (h : ProjectionSurjective.{u}) :
    lineBundlePseudofunctor.{u}.IsStack Scheme.zariskiTopology :=
  have := isStack_zariskiTopology_of_projectionSurjective h
  isStack_lineBundlePseudofunctor_of_isStack

end AlgebraicGeometry.Scheme.Modules
