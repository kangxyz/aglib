/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.FiniteType.EventualSurjectivity
public import Aglib.AlgebraicGeometry.Limits.FixedBaseChange
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Eventual closed immersions with varying sources

For an inverse system of qcqs schemes with closed-immersion transitions over a
fixed qcqs target, a finite-type structure map which is a closed immersion at
the limit is already a closed immersion at some stage. This differs from
closedness of the base change of one fixed immersion. The affine argument uses
eventual affineness and eventual surjectivity in a filtered system of quotients.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme

/-- The contravariant global-section structure maps of a diagram over a
fixed scheme, retaining the actual maps on global sections. -/
def sectionsStructure {I : Type u} [Category.{u} I]
    (D : I ⥤ Scheme.{u}) {S : Scheme.{u}}
    (t : D ⟶ (Functor.const I).obj S) :
    (Functor.const Iᵒᵖ).obj Γ(S, ⊤) ⟶ D.op ⋙ Scheme.Γ where
  app i := (t.app i.unop).appTop
  naturality i j q := by
    change 𝟙 _ ≫ (t.app j.unop).appTop =
      (t.app i.unop).appTop ≫ (D.map q.unop).appTop
    rw [Category.id_comp, ← Hom.comp_appTop]
    congr 1
    simp

/-- A cone's structural equation remains literal after taking sections. -/
lemma sectionsStructure_fac {I : Type u} [Category.{u} I]
    (D : I ⥤ Scheme.{u}) {S : Scheme.{u}}
    (t : D ⟶ (Functor.const I).obj S) (c : Cone D)
    (p : c.pt ⟶ S) (hp : ∀ i, c.π.app i ≫ t.app i = p) (i : Iᵒᵖ) :
    (sectionsStructure D t).app i ≫ (Scheme.Γ.mapCocone c.op).ι.app i = p.appTop := by
  change (t.app i.unop).appTop ≫ (c.π.app i.unop).appTop = p.appTop
  rw [← Hom.comp_appTop, hp]

/-- Over an affine target, a closed immersion from the limit of a finite-type
closed-transition system is already a closed immersion at a finite stage. -/
theorem exists_isClosedImmersion_of_isLimit_of_isAffine
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {i j} (q : i ⟶ j), IsClosedImmersion (D.map q)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c)
    {S : Scheme.{u}} [IsAffine S] (t : D ⟶ (Functor.const I).obj S)
    [∀ i, LocallyOfFiniteType (t.app i)]
    (p : c.pt ⟶ S) (hp : ∀ i, c.π.app i ≫ t.app i = p)
    [IsClosedImmersion p] :
    ∃ i, IsClosedImmersion (t.app i) := by
  have : ∀ {i j} (q : i ⟶ j), IsAffineHom (D.map q) := fun _ ↦ inferInstance
  have : IsAffine c.pt := isAffine_of_isAffineHom p
  obtain ⟨i, hi⟩ := Scheme.exists_isAffine_of_isLimit D c hc
  let D' : Over i ⥤ Scheme.{u} := Over.forget i ⋙ D
  let c' : Cone D' := c.whisker (Over.forget i)
  let t' : D' ⟶ (Functor.const (Over i)).obj S :=
    Functor.whiskerLeft (Over.forget i) t
  have hc' : IsLimit c' := (Functor.Initial.isLimitWhiskerEquiv (Over.forget i) c).symm hc
  have (j : Over i) : IsAffine (D.obj j.left) := isAffine_of_isAffineHom (D.map j.hom)
  have (j : Over i) : IsAffine (D'.obj j) := inferInstanceAs (IsAffine (D.obj j.left))
  have {j k : Over i} (q : j ⟶ k) : IsAffineHom (D'.map q) :=
    inferInstanceAs (IsAffineHom (D.map q.left))
  have (j : Over i) : CompactSpace (D'.obj j) := inferInstance
  have (j : Over i) : QuasiSeparatedSpace (D'.obj j) := inferInstance
  have (j : Over i) : IsAffine (((Functor.const (Over i)).obj S).obj j) :=
    inferInstanceAs (IsAffine S)
  have (j : Over i) : LocallyOfFiniteType (t'.app j) := by
    change LocallyOfFiniteType (t.app j.left)
    infer_instance
  have hp' (j : Over i) : c'.π.app j ≫ t'.app j = p := hp j.left
  have ht : ∀ {j k : (Over i)ᵒᵖ} (q : j ⟶ k),
      Function.Surjective ((D'.op ⋙ Scheme.Γ).map q) := by
    intro j k q
    change Function.Surjective (D.map q.unop.left).appTop
    exact (IsClosedImmersion.isAffine_surjective_of_isAffine _).2
  obtain ⟨j, hj⟩ := CommRingCat.exists_surjective_of_isColimit
    (D'.op ⋙ Scheme.Γ) (Scheme.Γ.mapCocone c'.op)
    (nonempty_isColimit_Γ_mapCocone D' c' hc').some (sectionsStructure D' t') p.appTop
    (sectionsStructure_fac D' t' c' p hp') ht
    (IsClosedImmersion.isAffine_surjective_of_isAffine p).2
    (op (Over.mk (𝟙 i)))
    (HasRingHomProperty.appTop @LocallyOfFiniteType (t'.app (Over.mk (𝟙 i))) inferInstance)
  exact ⟨j.right.unop.left, IsClosedImmersion.of_surjective_of_isAffine
    (t'.app j.right.unop) hj⟩

/-- A finite-type map from a qcqs closed-transition limit to a fixed qcqs
scheme is a closed immersion at a stage if it is one at the limit. -/
theorem exists_isClosedImmersion_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {i j} (q : i ⟶ j), IsClosedImmersion (D.map q)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c)
    {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (t : D ⟶ (Functor.const I).obj S) [∀ i, LocallyOfFiniteType (t.app i)]
    (p : c.pt ⟶ S) (hp : ∀ i, c.π.app i ≫ t.app i = p)
    [IsClosedImmersion p] :
    ∃ i, IsClosedImmersion (t.app i) := by
  classical
  let 𝒰 := S.affineCover.finiteSubcover
  have (a : 𝒰.I₀) : IsAffine (𝒰.X a) := inferInstanceAs (IsAffine (Spec _))
  have hlocal (a : 𝒰.I₀) :
      ∃ i, IsClosedImmersion (pullback.snd (t.app i) (𝒰.f a)) := by
    exact exists_isClosedImmersion_of_isLimit_of_isAffine
      (FixedBaseChange.diagram D t (𝒰.f a))
      (FixedBaseChange.cone D t (𝒰.f a) c p hp)
      (FixedBaseChange.isLimitCone D t (𝒰.f a) c p hp hc)
      (FixedBaseChange.baseStructure D t (𝒰.f a)) (pullback.snd p (𝒰.f a))
      (FixedBaseChange.cone_fac D t (𝒰.f a) c p hp)
  choose i hi using hlocal
  obtain ⟨k, hk⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image i)
  let q (a : 𝒰.I₀) : k ⟶ i a := (hk (Finset.mem_image_of_mem i (Finset.mem_univ a))).some
  refine ⟨k, (IsZariskiLocalAtTarget.iff_of_openCover (P := @IsClosedImmersion) 𝒰).mpr ?_⟩
  intro a
  change IsClosedImmersion (pullback.snd (t.app k) (𝒰.f a))
  have hfac : (FixedBaseChange.diagram D t (𝒰.f a)).map (q a) ≫
      pullback.snd (t.app (i a)) (𝒰.f a) = pullback.snd (t.app k) (𝒰.f a) := by
    have h := (FixedBaseChange.baseStructure D t (𝒰.f a)).naturality (q a)
    change (FixedBaseChange.diagram D t (𝒰.f a)).map (q a) ≫
      pullback.snd (t.app (i a)) (𝒰.f a) =
      pullback.snd (t.app k) (𝒰.f a) ≫ 𝟙 _ at h
    simpa only [Category.comp_id] using h
  have : IsClosedImmersion (pullback.snd (t.app (i a)) (𝒰.f a)) := hi a
  rw [← hfac]
  infer_instance

/-- The native over-category form of eventual closedness. The original cone
need only be supplied as a limit after applying the forgetful functor. -/
theorem exists_isClosedImmersion_over_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (D : I ⥤ Over S)
    [∀ {i j} (q : i ⟶ j), IsClosedImmersion (D.map q).left]
    [∀ i, CompactSpace (D.obj i).left] [∀ i, QuasiSeparatedSpace (D.obj i).left]
    [∀ i, LocallyOfFiniteType (D.obj i).hom]
    (c : Cone D) (hc : IsLimit ((Over.forget S).mapCone c))
    [IsClosedImmersion c.pt.hom] :
    ∃ i, IsClosedImmersion (D.obj i).hom := by
  let t : D ⋙ Over.forget S ⟶ (Functor.const I).obj S :=
    { app i := (D.obj i).hom
      naturality i j q := by simp }
  have {i j : I} (q : i ⟶ j) : IsClosedImmersion ((D ⋙ Over.forget S).map q) :=
    inferInstanceAs (IsClosedImmersion (D.map q).left)
  have (i : I) : CompactSpace ((D ⋙ Over.forget S).obj i) :=
    inferInstanceAs (CompactSpace (D.obj i).left)
  have (i : I) : QuasiSeparatedSpace ((D ⋙ Over.forget S).obj i) :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj i).left)
  have (i : I) : LocallyOfFiniteType (t.app i) :=
    inferInstanceAs (LocallyOfFiniteType (D.obj i).hom)
  exact exists_isClosedImmersion_of_isLimit (D ⋙ Over.forget S)
    ((Over.forget S).mapCone c) hc t c.pt.hom (fun i ↦ (c.π.app i).w)

end AlgebraicGeometry.Scheme
