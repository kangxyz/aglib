/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.Diagrams

/-!
# Open models and finite gluing

Quasi-compact opens of an actual base change descend to quasi-compact opens
at a stage, with their literal pullback comparisons. Finite affine gluing
data with quasi-compact overlaps produce finitely presented schemes over
an affine base when the chart structural maps are finitely presented.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits Topology

universe u

namespace AlgebraicGeometry.Scheme

variable {I : Type u} [Category.{u} I]

/-- Every projection of the canonical base-change cone is cartesian over
the corresponding projection of the base cone. -/
lemma isPullback_baseChangeCone (D : I ⥤ Scheme.{u}) (c : Cone D) (i : I)
    {X : Scheme.{u}} (f : X ⟶ D.obj i) (j : Over i) :
    IsPullback ((baseChangeCone D c i f).π.app j)
      (pullback.fst (c.π.app i) f) (pullback.fst (D.map j.hom) f) (c.π.app j.left) := by
  refine IsPullback.of_right (h₁₂ := pullback.snd (D.map j.hom) f) ?_ ?_
    (IsPullback.of_hasPullback (D.map j.hom) f).flip
  · simpa [baseChangeCone, baseChangeDiagram, Functor.comp_map, Over.forget_map,
      Over.pullback_map_left] using
      (IsPullback.of_hasPullback (c.π.app i) f).flip
  · simp [baseChangeCone, baseChangeDiagram, Functor.comp_map, Over.forget_map,
      Over.pullback_map_left]

/-- A quasi-compact open in the base change of a finitely presented model
descends to a finitely presented open model at a later stage. The comparison
is in the over category of the actual limit base. In particular, the open
need not be affine. -/
lemma exists_open_model_of_isLimit [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ j, IsAffine (D.obj j)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    {X : Scheme.{u}} (f : X ⟶ D.obj i)
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (U : (pullback (c.π.app i) f).Opens)
    (hU : IsCompact (U : Set (pullback (C := Scheme) (c.π.app i) f))) :
    ∃ (j : Over i) (V : ((baseChangeDiagram D i f).obj j).Opens),
      IsCompact (V : Set ((baseChangeDiagram D i f).obj j)) ∧
      LocallyOfFinitePresentation (V.ι ≫ pullback.fst (D.map j.hom) f) ∧
      QuasiCompact (V.ι ≫ pullback.fst (D.map j.hom) f) ∧
      QuasiSeparated (V.ι ≫ pullback.fst (D.map j.hom) f) ∧
      Nonempty ((Over.pullback (c.π.app j.left)).obj
        (Over.mk (V.ι ≫ pullback.fst (D.map j.hom) f)) ≅
          Over.mk (U.ι ≫ pullback.fst (c.π.app i) f)) := by
  have {j k : I} (g : j ⟶ k) : IsAffineHom (D.map g) := inferInstance
  obtain ⟨j, V, hV, hVU⟩ := AlgebraicGeometry.exists_preimage_eq
    (baseChangeDiagram D i f) (baseChangeCone D c i f)
    (isLimitBaseChangeCone D c hc i f) U hU
  subst U
  have : CompactSpace V := isCompact_iff_compactSpace.mp hV
  have : QuasiSeparatedSpace ((baseChangeDiagram D i f).obj j) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.fst (D.map j.hom) f)
  have : QuasiSeparatedSpace V := quasiSeparatedSpace_of_quasiSeparated V.ι
  let H := (isPullback_morphismRestrict ((baseChangeCone D c i f).π.app j) V).paste_vert
    (isPullback_baseChangeCone D c i f j)
  refine ⟨j, V, hV, inferInstance, inferInstance, inferInstance,
    ⟨Over.isoMk H.isoPullback.symm ?_⟩⟩
  exact H.isoPullback_inv_snd

@[reassoc (attr := simp)]
lemma baseChangeDiagram_map_fst (D : I ⥤ Scheme.{u}) (i : I)
    {X : Scheme.{u}} (f : X ⟶ D.obj i) {j k : Over i} (q : j ⟶ k) :
    (baseChangeDiagram D i f).map q ≫ pullback.fst (D.map k.hom) f =
      pullback.fst (D.map j.hom) f ≫ D.map q.left := by
  simp [baseChangeDiagram, Functor.comp_map, Over.forget_map, Over.pullback_map_left]

@[reassoc (attr := simp)]
lemma baseChangeDiagram_map_snd (D : I ⥤ Scheme.{u}) (i : I)
    {X : Scheme.{u}} (f : X ⟶ D.obj i) {j k : Over i} (q : j ⟶ k) :
    (baseChangeDiagram D i f).map q ≫ pullback.snd (D.map k.hom) f =
      pullback.snd (D.map j.hom) f := by
  simp [baseChangeDiagram, Functor.comp_map, Over.forget_map, Over.pullback_map_left]

@[reassoc (attr := simp)]
lemma baseChangeCone_π_app_fst (D : I ⥤ Scheme.{u}) (c : Cone D) (i : I)
    {X : Scheme.{u}} (f : X ⟶ D.obj i) (j : Over i) :
    (baseChangeCone D c i f).π.app j ≫ pullback.fst (D.map j.hom) f =
      pullback.fst (c.π.app i) f ≫ c.π.app j.left := by
  simp [baseChangeCone, Functor.comp_map, Over.forget_map, Over.pullback_map_left]

@[reassoc (attr := simp)]
lemma baseChangeCone_π_app_snd (D : I ⥤ Scheme.{u}) (c : Cone D) (i : I)
    {X : Scheme.{u}} (f : X ⟶ D.obj i) (j : Over i) :
    (baseChangeCone D c i f).π.app j ≫ pullback.snd (D.map j.hom) f =
      pullback.snd (c.π.app i) f := by
  simp [baseChangeCone, Functor.comp_map, Over.forget_map, Over.pullback_map_left]

/-- Transport a map of modeled schemes to a later stage using the literal
pullback universal property. -/
def baseChangeDiagramMapHom (D : I ⥤ Scheme.{u}) (i : I)
    {X Y : Scheme.{u}} (f : X ⟶ D.obj i) (g : Y ⟶ D.obj i)
    {j k : Over i} (q : k ⟶ j)
    (a : (baseChangeDiagram D i f).obj j ⟶ (baseChangeDiagram D i g).obj j)
    (ha : a ≫ pullback.fst (D.map j.hom) g = pullback.fst (D.map j.hom) f) :
    (baseChangeDiagram D i f).obj k ⟶ (baseChangeDiagram D i g).obj k :=
  pullback.lift (pullback.fst (D.map k.hom) f)
    ((baseChangeDiagram D i f).map q ≫ a ≫ pullback.snd (D.map j.hom) g) (by
      symm
      simp only [Category.assoc]
      rw [← pullback.condition, reassoc_of% ha, baseChangeDiagram_map_fst_assoc,
        ← D.map_comp, Over.w q]
      rfl)

@[reassoc (attr := simp)]
lemma baseChangeDiagramMapHom_fst (D : I ⥤ Scheme.{u}) (i : I)
    {X Y : Scheme.{u}} (f : X ⟶ D.obj i) (g : Y ⟶ D.obj i)
    {j k : Over i} (q : k ⟶ j)
    (a : (baseChangeDiagram D i f).obj j ⟶ (baseChangeDiagram D i g).obj j)
    (ha : a ≫ pullback.fst (D.map j.hom) g = pullback.fst (D.map j.hom) f) :
    baseChangeDiagramMapHom D i f g q a ha ≫ pullback.fst (D.map k.hom) g =
      pullback.fst (D.map k.hom) f := by
  simp [baseChangeDiagramMapHom]

@[reassoc (attr := simp)]
lemma baseChangeDiagramMapHom_snd (D : I ⥤ Scheme.{u}) (i : I)
    {X Y : Scheme.{u}} (f : X ⟶ D.obj i) (g : Y ⟶ D.obj i)
    {j k : Over i} (q : k ⟶ j)
    (a : (baseChangeDiagram D i f).obj j ⟶ (baseChangeDiagram D i g).obj j)
    (ha : a ≫ pullback.fst (D.map j.hom) g = pullback.fst (D.map j.hom) f) :
    baseChangeDiagramMapHom D i f g q a ha ≫ pullback.snd (D.map k.hom) g =
      (baseChangeDiagram D i f).map q ≫ a ≫ pullback.snd (D.map j.hom) g := by
  simp [baseChangeDiagramMapHom]

@[reassoc]
lemma baseChangeDiagramMapHom_naturality (D : I ⥤ Scheme.{u}) (i : I)
    {X Y : Scheme.{u}} (f : X ⟶ D.obj i) (g : Y ⟶ D.obj i)
    {j k : Over i} (q : k ⟶ j)
    (a : (baseChangeDiagram D i f).obj j ⟶ (baseChangeDiagram D i g).obj j)
    (ha : a ≫ pullback.fst (D.map j.hom) g = pullback.fst (D.map j.hom) f) :
    baseChangeDiagramMapHom D i f g q a ha ≫ (baseChangeDiagram D i g).map q =
      (baseChangeDiagram D i f).map q ≫ a := by
  apply pullback.hom_ext (f := D.map j.hom) (g := g)
  · simp [Category.assoc, ha]
  · simp [Category.assoc]

lemma baseChangeDiagramMapHom_comp_π (D : I ⥤ Scheme.{u}) (c : Cone D) (i : I)
    {X Y : Scheme.{u}} (f : X ⟶ D.obj i) (g : Y ⟶ D.obj i)
    {j k : Over i} (q : k ⟶ j)
    (a : (baseChangeDiagram D i f).obj j ⟶ (baseChangeDiagram D i g).obj j)
    (ha : a ≫ pullback.fst (D.map j.hom) g = pullback.fst (D.map j.hom) f)
    (b : (baseChangeCone D c i f).pt ⟶ (baseChangeCone D c i g).pt)
    (hb : b ≫ pullback.fst (c.π.app i) g = pullback.fst (c.π.app i) f)
    (hcomp : (baseChangeCone D c i f).π.app j ≫ a =
      b ≫ (baseChangeCone D c i g).π.app j) :
    (baseChangeCone D c i f).π.app k ≫ baseChangeDiagramMapHom D i f g q a ha =
      b ≫ (baseChangeCone D c i g).π.app k := by
  apply pullback.hom_ext (f := D.map k.hom) (g := g)
  · simp [Category.assoc, reassoc_of% hb]
  · simp only [Category.assoc, baseChangeDiagramMapHom_snd,
      baseChangeCone_π_app_snd]
    rw [← Category.assoc, (baseChangeCone D c i f).w q]
    simpa only [Category.assoc, baseChangeCone_π_app_snd] using
      congrArg (· ≫ pullback.snd (D.map j.hom) g) hcomp

/-- Equality of two maps of stage schemes is detected at a later stage
by their literal base changes. The target need only be locally of finite
type, and the source structural morphism only quasi-compact. -/
lemma exists_baseChange_map_eq_of_isLimit [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ j, IsAffine (D.obj j)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    {X Y : Scheme.{u}} (f : X ⟶ D.obj i) (g : Y ⟶ D.obj i)
    [QuasiCompact f] [LocallyOfFiniteType g]
    (a b : Over.mk f ⟶ Over.mk g)
    (hab : (Over.pullback (c.π.app i)).map a = (Over.pullback (c.π.app i)).map b) :
    ∃ j : Over i,
      (Over.pullback (D.map j.hom)).map a = (Over.pullback (D.map j.hom)).map b := by
  have {j k : I} (q : j ⟶ k) : IsAffineHom (D.map q) := inferInstance
  have ha : a.left ≫ g = f := Over.w a
  have hb : b.left ≫ g = f := Over.w b
  let t : baseChangeDiagram D i f ⟶ (Functor.const (Over i)).obj (D.obj i) :=
    { app j := pullback.snd (D.map j.hom) f ≫ f
      naturality {j k} q := by
        simp [baseChangeDiagram, Functor.comp_map, Over.forget_map, Over.pullback_map_left] }
  have hlim : pullback.snd (c.π.app i) f ≫ a.left =
      pullback.snd (c.π.app i) f ≫ b.left := by
    have h := congrArg (fun q ↦ (pullbackSymmetry (c.π.app i) f).hom ≫
      q.left ≫ pullback.fst g (c.π.app i)) hab
    simpa [Over.pullback_map_left, Category.assoc] using h
  obtain ⟨j, q, hq⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
    (baseChangeDiagram D i f) t g (baseChangeCone D c i f)
    (isLimitBaseChangeCone D c hc i f) (i := Over.mk (𝟙 i))
    (pullback.snd (D.map (𝟙 i)) f ≫ a.left)
    (pullback.snd (D.map (𝟙 i)) f ≫ b.left)
    (by simp [t, Category.assoc, ha]) (by simp [t, Category.assoc, hb]) (by
      simpa [baseChangeCone, Functor.comp_map, Over.forget_map, Over.pullback_map_left,
        Category.assoc] using hlim)
  have hstage : pullback.snd (D.map j.hom) f ≫ a.left =
      pullback.snd (D.map j.hom) f ≫ b.left := by
    simpa [baseChangeDiagram, Functor.comp_map, Over.forget_map, Over.pullback_map_left,
      Category.assoc] using hq
  have hstage' : pullback.fst f (D.map j.hom) ≫ a.left =
      pullback.fst f (D.map j.hom) ≫ b.left := by
    simpa using congrArg ((pullbackSymmetry f (D.map j.hom)).hom ≫ ·) hstage
  refine ⟨j, Over.OverMorphism.ext ?_⟩
  apply pullback.hom_ext
  · simpa [Over.pullback_map_left] using hstage'
  · simp [Over.pullback_map_left]

/-- An isomorphism at the limit is detected at a stage for a compatible
family of maps between the actual base changes of two finitely presented
models. -/
lemma exists_isIso_baseChangeNatTrans_of_isLimit [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ j, IsAffine (D.obj j)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    {X Y : Scheme.{u}} (f : X ⟶ D.obj i) (g : Y ⟶ D.obj i)
    [LocallyOfFinitePresentation f] [QuasiCompact f]
    [LocallyOfFinitePresentation g] [QuasiCompact g] [QuasiSeparated g]
    (α : baseChangeDiagram D i f ⟶ baseChangeDiagram D i g)
    (hα : ∀ j, α.app j ≫ pullback.fst (D.map j.hom) g = pullback.fst (D.map j.hom) f)
    (e : (baseChangeCone D c i f).pt ≅ (baseChangeCone D c i g).pt)
    (hebase : e.hom ≫ pullback.fst (c.π.app i) g = pullback.fst (c.π.app i) f)
    (he : (baseChangeCone D c i f).π ≫ α =
      (Functor.const (Over i)).map e.hom ≫ (baseChangeCone D c i g).π) :
    ∃ j : Over i, IsIso (α.app j) := by
  have {j k : I} (q : j ⟶ k) : IsAffineHom (D.map q) := inferInstance
  have hinv : e.inv ≫ pullback.fst (c.π.app i) f = pullback.fst (c.π.app i) g := by
    rw [← hebase, Iso.inv_hom_id_assoc]
  obtain ⟨j, b, hb, hbcomp⟩ := exists_hom_between_baseChanges_of_isLimit
    D c hc i g f e.inv hinv
  have he' : (baseChangeCone D c i f).π.app j ≫ α.app j =
      e.hom ≫ (baseChangeCone D c i g).π.app j := NatTrans.congr_app he j
  let tx : baseChangeDiagram D i f ⟶ (Functor.const (Over i)).obj (D.obj i) :=
    { app j := pullback.snd (D.map j.hom) f ≫ f
      naturality {j k} q := by simp }
  let ty : baseChangeDiagram D i g ⟶ (Functor.const (Over i)).obj (D.obj i) :=
    { app j := pullback.snd (D.map j.hom) g ≫ g
      naturality {j k} q := by simp }
  have hbbase : b ≫ pullback.snd (D.map j.hom) f ≫ f =
      pullback.snd (D.map j.hom) g ≫ g := by
    rw [← pullback.condition, reassoc_of% hb, pullback.condition]
  have habase : α.app j ≫ pullback.snd (D.map j.hom) g ≫ g =
      pullback.snd (D.map j.hom) f ≫ f := by
    rw [← pullback.condition, reassoc_of% (hα j), pullback.condition]
  obtain ⟨kx, qx, hx⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
    (baseChangeDiagram D i f) tx f (baseChangeCone D c i f)
    (isLimitBaseChangeCone D c hc i f) (i := j)
    (α.app j ≫ b ≫ pullback.snd (D.map j.hom) f)
    (pullback.snd (D.map j.hom) f)
    (by dsimp [tx]; simp only [Category.assoc, hbbase, habase]) rfl (by
      rw [reassoc_of% he', reassoc_of% hbcomp]
      simp)
  obtain ⟨ky, qy, hy⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
    (baseChangeDiagram D i g) ty g (baseChangeCone D c i g)
    (isLimitBaseChangeCone D c hc i g) (i := j)
    (b ≫ α.app j ≫ pullback.snd (D.map j.hom) g)
    (pullback.snd (D.map j.hom) g)
    (by dsimp [ty]; simp only [Category.assoc, habase, hbbase]) rfl (by
      rw [reassoc_of% hbcomp, reassoc_of% he']
      simp)
  obtain ⟨k, qkx, qky, hqk⟩ := IsCofiltered.cospan qx qy
  let q : k ⟶ j := qkx ≫ qx
  have hqy : q = qky ≫ qy := hqk
  have hx' : (baseChangeDiagram D i f).map q ≫ α.app j ≫ b ≫
      pullback.snd (D.map j.hom) f =
      (baseChangeDiagram D i f).map q ≫ pullback.snd (D.map j.hom) f := by
    simpa [q, Functor.map_comp, Category.assoc] using
      congrArg ((baseChangeDiagram D i f).map qkx ≫ ·) hx
  have hy' : (baseChangeDiagram D i g).map q ≫ b ≫ α.app j ≫
      pullback.snd (D.map j.hom) g =
      (baseChangeDiagram D i g).map q ≫ pullback.snd (D.map j.hom) g := by
    rw [hqy]
    simpa [Functor.map_comp, Category.assoc] using
      congrArg ((baseChangeDiagram D i g).map qky ≫ ·) hy
  let b' := baseChangeDiagramMapHom D i g f q b hb
  refine ⟨k, ⟨⟨b', ?_, ?_⟩⟩⟩
  · apply pullback.hom_ext (f := D.map k.hom) (g := f)
    · simp [b', Category.assoc, hα]
    · simp only [Category.assoc, Category.id_comp]
      calc
        α.app k ≫ b' ≫ pullback.snd (D.map k.hom) f =
            α.app k ≫ (baseChangeDiagram D i g).map q ≫ b ≫
              pullback.snd (D.map j.hom) f := by simp [b']
        _ = (baseChangeDiagram D i f).map q ≫ α.app j ≫ b ≫
              pullback.snd (D.map j.hom) f := by
          simpa only [Category.assoc] using congrArg
            (· ≫ b ≫ pullback.snd (D.map j.hom) f) (α.naturality q).symm
        _ = (baseChangeDiagram D i f).map q ≫ pullback.snd (D.map j.hom) f := hx'
        _ = pullback.snd (D.map k.hom) f := by simp
  · apply pullback.hom_ext (f := D.map k.hom) (g := g)
    · simp [b', Category.assoc, hα]
    · simp only [Category.assoc, Category.id_comp]
      calc
        b' ≫ α.app k ≫ pullback.snd (D.map k.hom) g =
            b' ≫ α.app k ≫ (baseChangeDiagram D i g).map q ≫
              pullback.snd (D.map j.hom) g := by simp
        _ = b' ≫ (baseChangeDiagram D i f).map q ≫ α.app j ≫
              pullback.snd (D.map j.hom) g := by
          rw [← reassoc_of% (α.naturality q)]
        _ = (baseChangeDiagram D i g).map q ≫ b ≫ α.app j ≫
              pullback.snd (D.map j.hom) g := by
          exact baseChangeDiagramMapHom_naturality_assoc D i g f q b hb _
        _ = (baseChangeDiagram D i g).map q ≫ pullback.snd (D.map j.hom) g := hy'
        _ = pullback.snd (D.map k.hom) g := by simp

/-- If the literal base change of a map between finitely presented stage
schemes is an isomorphism at the limit, its literal base change is an
isomorphism at a later stage. -/
lemma exists_isIso_baseChange_map_of_isLimit [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ j, IsAffine (D.obj j)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    {X Y : Scheme.{u}} (f : X ⟶ D.obj i) (g : Y ⟶ D.obj i)
    [LocallyOfFinitePresentation f] [QuasiCompact f]
    [LocallyOfFinitePresentation g] [QuasiCompact g] [QuasiSeparated g]
    (a : Over.mk f ⟶ Over.mk g)
    [IsIso ((Over.pullback (c.π.app i)).map a)] :
    ∃ j : Over i, IsIso ((Over.pullback (D.map j.hom)).map a) := by
  have ha : a.left ≫ g = f := Over.w a
  let α : baseChangeDiagram D i f ⟶ baseChangeDiagram D i g :=
    { app j := pullback.lift (pullback.fst (D.map j.hom) f)
        (pullback.snd (D.map j.hom) f ≫ a.left) (by
          simp only [Category.assoc, ha]
          exact pullback.condition)
      naturality {j k} q := by
        apply pullback.hom_ext (f := D.map k.hom) (g := g) <;> simp [Category.assoc] }
  let e : (baseChangeCone D c i f).pt ≅ (baseChangeCone D c i g).pt :=
    pullbackSymmetry (c.π.app i) f ≪≫
      (Over.forget c.pt).mapIso (asIso ((Over.pullback (c.π.app i)).map a)) ≪≫
      (pullbackSymmetry (c.π.app i) g).symm
  have hefst : e.hom ≫ pullback.fst (c.π.app i) g =
      pullback.fst (c.π.app i) f := by
    simp [e, Over.pullback_map_left, Category.assoc]
  have hesnd : e.hom ≫ pullback.snd (c.π.app i) g =
      pullback.snd (c.π.app i) f ≫ a.left := by
    simp [e, Over.pullback_map_left, Category.assoc]
  have he : (baseChangeCone D c i f).π ≫ α =
      (Functor.const (Over i)).map e.hom ≫ (baseChangeCone D c i g).π := by
    ext j
    apply pullback.hom_ext (f := D.map j.hom) (g := g)
    · simp [α, Category.assoc, reassoc_of% hefst]
    · simp [α, Category.assoc, hesnd]
  obtain ⟨j, hj⟩ := exists_isIso_baseChangeNatTrans_of_isLimit D c hc i f g α
    (fun j ↦ by simp [α]) e hefst he
  have : IsIso (α.app j) := hj
  have hmap : ((Over.pullback (D.map j.hom)).map a).left =
      (pullbackSymmetry (D.map j.hom) f).inv ≫ α.app j ≫
        (pullbackSymmetry (D.map j.hom) g).hom := by
    apply pullback.hom_ext (f := g) (g := D.map j.hom) <;>
      simp [α, Over.pullback_map_left, Category.assoc]
  have hIso : IsIso (((Over.pullback (D.map j.hom)).map a).left) := by
    rw [hmap]
    infer_instance
  have : IsIso ((Over.forget (D.obj j.left)).map ((Over.pullback (D.map j.hom)).map a)) := by
    simpa only [Over.forget_map] using hIso
  exact ⟨j, isIso_of_reflects_iso ((Over.pullback (D.map j.hom)).map a) (Over.forget _)⟩

namespace GlueData

variable (D : Scheme.GlueData.{u})

/-- Finite affine charts give a quasi-compact glued scheme. -/
lemma compactSpace_of_finite [Finite D.J] [∀ i, IsAffine (D.U i)] :
    CompactSpace D.glued := by
  have : Finite D.openCover.I₀ := inferInstanceAs (Finite D.J)
  have (i : D.openCover.I₀) : CompactSpace (D.openCover.X i) :=
    inferInstanceAs (CompactSpace (D.U i))
  exact D.openCover.compactSpace

/-- Affine charts with quasi-compact overlaps give a quasi-separated glued
scheme. No separatedness of the gluing is assumed. -/
lemma quasiSeparatedSpace_of_compact_overlaps [∀ i, IsAffine (D.U i)]
    [∀ i j, CompactSpace (D.V (i, j))] : QuasiSeparatedSpace D.glued := by
  refine Scheme.quasiSeparatedSpace_of_isOpenCover (fun i ↦ (D.ι i).opensRange)
    D.openCover.isOpenCover_opensRange (fun i ↦ isAffineOpen_opensRange (D.ι i)) ?_
  intro i j
  let H : IsPullback (D.f i j) (D.t i j ≫ D.f j i) (D.ι i) (D.ι j) :=
    ⟨⟨by simp⟩, ⟨D.vPullbackConeIsLimit i j⟩⟩
  have : CompactSpace (pullback (C := Scheme) (D.ι i) (D.ι j)) :=
    H.isoPullback.hom.homeomorph.compactSpace
  have h := isCompact_range (pullback.fst (D.ι i) (D.ι j) ≫ D.ι i).continuous
  simpa only [IsOpenImmersion.range_pullback_to_base_of_left,
    Scheme.Hom.coe_opensRange] using h

variable {S : Scheme.{u}} (f : ∀ i, D.U i ⟶ S)
  (hf : ∀ i j, D.f i j ≫ f i = D.t i j ≫ D.f j i ≫ f j)

/-- The structural map obtained by gluing the specified compatible chart
structural maps. -/
def toBase : D.glued ⟶ S :=
  Multicoequalizer.desc D.toGlueData.diagram S f (fun ⟨i, j⟩ ↦ by
    change D.f i j ≫ f i = (D.t i j ≫ D.f j i) ≫ f j
    simpa only [Category.assoc] using hf i j)

@[reassoc (attr := simp)]
lemma ι_toBase (i : D.J) : D.ι i ≫ D.toBase f hf = f i :=
  Multicoequalizer.π_desc D.toGlueData.diagram S f _ i

/-- Gluing preserves the locally finitely presented chart structural maps. -/
lemma locallyOfFinitePresentation_toBase [∀ i, LocallyOfFinitePresentation (f i)] :
    LocallyOfFinitePresentation (D.toBase f hf) := by
  apply IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFinitePresentation) D.openCover
  intro i
  change LocallyOfFinitePresentation (D.ι i ≫ D.toBase f hf)
  rw [D.ι_toBase]
  infer_instance

/-- A finite affine gluing with quasi-compact overlaps and finitely
presented chart maps has a finitely presented structural map. -/
lemma finitePresentation_toBase [IsAffine S] [Finite D.J]
    [∀ i, IsAffine (D.U i)] [∀ i j, CompactSpace (D.V (i, j))]
    [∀ i, LocallyOfFinitePresentation (f i)] :
    LocallyOfFinitePresentation (D.toBase f hf) ∧
      QuasiCompact (D.toBase f hf) ∧ QuasiSeparated (D.toBase f hf) := by
  have : CompactSpace D.glued := D.compactSpace_of_finite
  have : QuasiSeparatedSpace D.glued := D.quasiSeparatedSpace_of_compact_overlaps
  exact ⟨D.locallyOfFinitePresentation_toBase f hf, inferInstance, inferInstance⟩

end GlueData

/-- A stage map compatible with an isomorphism of the original schemes
is an isomorphism after the literal base change, when both specified
comparison squares are cartesian. -/
lemma isIso_overPullback_map_of_isPullback
    {S S₀ X Y X₀ Y₀ : Scheme.{u}} (π : S ⟶ S₀) (f : X₀ ⟶ S₀) (g : Y₀ ⟶ S₀)
    (px : X ⟶ X₀) (tx : X ⟶ S) (py : Y ⟶ Y₀) (ty : Y ⟶ S)
    (hx : IsPullback px tx f π) (hy : IsPullback py ty g π)
    (a : Over.mk f ⟶ Over.mk g) (e : X ≅ Y) (he : e.hom ≫ ty = tx)
    (ha : px ≫ a.left = e.hom ≫ py) : IsIso ((Over.pullback π).map a) := by
  let ex : (Over.pullback π).obj (Over.mk f) ≅ Over.mk tx :=
    Over.isoMk hx.isoPullback.symm hx.isoPullback_inv_snd
  let ey : (Over.pullback π).obj (Over.mk g) ≅ Over.mk ty :=
    Over.isoMk hy.isoPullback.symm hy.isoPullback_inv_snd
  let E := ex ≪≫ (Over.isoMk e he : Over.mk tx ≅ Over.mk ty) ≪≫ ey.symm
  have h : (Over.pullback π).map a = E.hom := by
    apply Over.OverMorphism.ext
    apply (cancel_epi hx.isoPullback.hom).mp
    apply pullback.hom_ext (f := g) (g := π)
    · simp [ex, ey, E, Over.pullback_map_left, Category.assoc, ha]
    · simp [ex, ey, E, Over.pullback_map_left, Category.assoc, he]
  rw [h]
  infer_instance

/-- The literal further base change of a canonical diagram object is the
literal base change along the composite base map. -/
private def baseChangeDiagram_rebaseIso {S S₁ S₂ X : Scheme.{u}}
    (f : X ⟶ S) (g : S₁ ⟶ S) (h : S₂ ⟶ S₁) :
    (Over.pullback h).obj (Over.mk (pullback.fst g f)) ≅
      (Over.pullback (h ≫ g)).obj (Over.mk f) :=
  Over.isoMk
    (pullbackSymmetry (pullback.fst g f) h ≪≫ pullbackRightPullbackFstIso g f h ≪≫
      pullbackSymmetry (h ≫ g) f) (by simp)

/-- An isomorphism between the literal limit base changes of two supplied
finitely presented models yields an actual over-isomorphism between their
literal base changes at one later stage. This is an existence corollary;
it does not assert that a particular choice of the final isomorphism has
the prescribed limit comparison. -/
lemma exists_iso_between_baseChanges_of_isLimit [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ j, IsAffine (D.obj j)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    {X Y : Scheme.{u}} (f : X ⟶ D.obj i) (g : Y ⟶ D.obj i)
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    [LocallyOfFinitePresentation g] [QuasiCompact g] [QuasiSeparated g]
    (e : (Over.pullback (c.π.app i)).obj (Over.mk f) ≅
      (Over.pullback (c.π.app i)).obj (Over.mk g)) :
    ∃ j : Over i, Nonempty ((Over.pullback (D.map j.hom)).obj (Over.mk f) ≅
      (Over.pullback (D.map j.hom)).obj (Over.mk g)) := by
  let E : pullback (c.π.app i) f ≅ pullback (c.π.app i) g :=
    pullbackSymmetry (c.π.app i) f ≪≫ (Over.forget c.pt).mapIso e ≪≫
      (pullbackSymmetry (c.π.app i) g).symm
  have he : e.hom.left ≫ pullback.snd g (c.π.app i) = pullback.snd f (c.π.app i) :=
    Over.w e.hom
  have hE : E.hom ≫ pullback.fst (c.π.app i) g = pullback.fst (c.π.app i) f := by
    simp [E, Category.assoc, he]
  obtain ⟨j, a, ha, hcomp⟩ := exists_hom_between_baseChanges_of_isLimit D c hc i f g E.hom hE
  let a' : Over.mk (pullback.fst (D.map j.hom) f) ⟶
      Over.mk (pullback.fst (D.map j.hom) g) := Over.homMk a ha
  have : IsIso ((Over.pullback (c.π.app j.left)).map a') :=
    isIso_overPullback_map_of_isPullback (c.π.app j.left)
      (pullback.fst (D.map j.hom) f) (pullback.fst (D.map j.hom) g)
      ((baseChangeCone D c i f).π.app j) (pullback.fst (c.π.app i) f)
      ((baseChangeCone D c i g).π.app j) (pullback.fst (c.π.app i) g)
      (isPullback_baseChangeCone D c i f j) (isPullback_baseChangeCone D c i g j)
      a' E hE hcomp
  obtain ⟨k, hk⟩ := exists_isIso_baseChange_map_of_isLimit D c hc j.left
    (pullback.fst (D.map j.hom) f) (pullback.fst (D.map j.hom) g) a'
  have : IsIso ((Over.pullback (D.map k.hom)).map a') := hk
  let l : Over i := Over.mk (k.hom ≫ j.hom)
  have hβ : D.map k.hom ≫ D.map j.hom = D.map l.hom := (D.map_comp _ _).symm
  let result : (Over.pullback (D.map k.hom ≫ D.map j.hom)).obj (Over.mk f) ≅
      (Over.pullback (D.map k.hom ≫ D.map j.hom)).obj (Over.mk g) :=
    (baseChangeDiagram_rebaseIso f (D.map j.hom) (D.map k.hom)).symm ≪≫
      asIso ((Over.pullback (D.map k.hom)).map a') ≪≫
      baseChangeDiagram_rebaseIso g (D.map j.hom) (D.map k.hom)
  let ef := eqToIso (congrArg (fun β : D.obj k.left ⟶ D.obj i ↦
    (Over.pullback β).obj (Over.mk f)) hβ)
  let eg := eqToIso (congrArg (fun β : D.obj k.left ⟶ D.obj i ↦
    (Over.pullback β).obj (Over.mk g)) hβ)
  exact ⟨l, ⟨ef.symm ≪≫ result ≪≫ eg⟩⟩

end AlgebraicGeometry.Scheme
