/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.Ring.Descent.FinitePresentation.Models
public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.Gluing
public import Mathlib.AlgebraicGeometry.RelativeGluing

/-!
# Finite-stage models and diagrams of schemes

Finitely presented schemes over an actual filtered ring colimit descend
to a stage, with an isomorphism from their literal base change to the
original scheme and structural map. The affine construction uses finite
presentation coefficients. Compact-open induction and binary open gluing
give the general construction, including nonseparated schemes. Finite
categories of these objects descend with all arrows, identities and
compositions, and a natural literal-base-change comparison.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits TensorProduct Topology

universe u v

namespace AlgebraicGeometry

section Affine

variable {I : Type u} [Category.{u} I] [IsFiltered I]
  (F : I ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)

include hc

/-- An affine scheme given as a spectrum, with its specified finitely
presented structural map, descends to a filtered stage. The comparison uses
the literal `Over.pullback` along the specified colimit cocone map. -/
lemma Scheme.exists_spec_model_of_isColimit
    {A : CommRingCat.{u}} (φ : c.pt ⟶ A)
    [LocallyOfFinitePresentation (Spec.map φ)] :
    ∃ (i : I) (B : CommRingCat.{u}) (ψ : F.obj i ⟶ B),
      LocallyOfFinitePresentation (Spec.map ψ) ∧
      Nonempty ((Over.pullback (Spec.map (c.ι.app i))).obj
        (Over.mk (Spec.map ψ)) ≅ Over.mk (Spec.map φ)) := by
  let : Algebra c.pt A := φ.hom.toAlgebra
  have : Algebra.FinitePresentation c.pt A :=
    (LocallyOfFinitePresentation.SpecMap_iff φ).mp inferInstance
  obtain ⟨i, B, hB, hAB, hfp, ⟨e⟩⟩ :=
    Algebra.FinitePresentation.exists_model_of_isColimit F c hc A
  let := hB
  let := hAB
  let := hfp
  let : Algebra (F.obj i) c.pt := (c.ι.app i).hom.toAlgebra
  let ψ : F.obj i ⟶ CommRingCat.of B := CommRingCat.ofHom (algebraMap (F.obj i) B)
  have hψ : LocallyOfFinitePresentation (Spec.map ψ) :=
    (LocallyOfFinitePresentation.SpecMap_iff ψ).mpr
      ((RingHom.finitePresentation_algebraMap).mpr hfp)
  let eSpec : Spec (.of (c.pt ⊗[F.obj i] B)) ≅ Spec A :=
    (Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op).symm
  have heSpec : eSpec.hom ≫ Spec.map φ =
      Spec.map (CommRingCat.ofHom (algebraMap c.pt (c.pt ⊗[F.obj i] B))) := by
    change Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ Spec.map φ = _
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    ext x
    exact e.symm.commutes x
  let ePullback : pullback (Spec.map ψ) (Spec.map (c.ι.app i)) ≅ Spec A :=
    pullbackSymmetry _ _ ≪≫ pullbackSpecIso (F.obj i) c.pt B ≪≫ eSpec
  refine ⟨i, .of B, ψ, hψ, ⟨Over.isoMk ePullback ?_⟩⟩
  change ePullback.hom ≫ Spec.map φ = pullback.snd (Spec.map ψ) (Spec.map (c.ι.app i))
  simp only [ePullback, Iso.trans_hom, Category.assoc, heSpec]
  rw [pullbackSpecIso_hom_fst']
  exact pullbackSymmetry_hom_comp_fst _ _

/-- Every finitely presented affine scheme over a filtered ring colimit
has a finitely presented affine model whose actual base change is isomorphic
to the original object in `Over (Spec c.pt)`. -/
lemma Scheme.exists_affine_model_of_isColimit
    {X : Scheme.{u}} [IsAffine X] (f : X ⟶ Spec c.pt) [LocallyOfFinitePresentation f] :
    ∃ (i : I) (Xᵢ : Scheme.{u}) (fᵢ : Xᵢ ⟶ Spec (F.obj i)),
      IsAffine Xᵢ ∧ LocallyOfFinitePresentation fᵢ ∧ QuasiCompact fᵢ ∧ QuasiSeparated fᵢ ∧
      Nonempty ((Over.pullback (Spec.map (c.ι.app i))).obj (Over.mk fᵢ) ≅ Over.mk f) := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.isoSpec.inv ≫ f)
  have : LocallyOfFinitePresentation (Spec.map φ) := by
    rw [hφ]
    infer_instance
  obtain ⟨i, B, ψ, hψ, ⟨e⟩⟩ := Scheme.exists_spec_model_of_isColimit F c hc φ
  refine ⟨i, Spec B, Spec.map ψ, inferInstance, hψ, inferInstance, inferInstance,
    ⟨e ≪≫ Over.isoMk X.isoSpec.symm ?_⟩⟩
  exact hφ.symm

/-- A finite family of affine schemes over the actual ring colimit has
finitely presented affine models at one common stage, with their original
structural maps and literal base-change comparisons. -/
lemma Scheme.exists_common_affine_models_of_isColimit
    {J : Type*} [Finite J] (X : J → Scheme.{u}) [∀ j, IsAffine (X j)]
    (f : ∀ j, X j ⟶ Spec c.pt) [∀ j, LocallyOfFinitePresentation (f j)] :
    ∃ i : I, ∀ j, ∃ (Xᵢ : Scheme.{u}) (fᵢ : Xᵢ ⟶ Spec (F.obj i)),
      IsAffine Xᵢ ∧ LocallyOfFinitePresentation fᵢ ∧ QuasiCompact fᵢ ∧ QuasiSeparated fᵢ ∧
      Nonempty ((Over.pullback (Spec.map (c.ι.app i))).obj (Over.mk fᵢ) ≅ Over.mk (f j)) := by
  classical
  let : Fintype J := Fintype.ofFinite J
  choose i Xi fi hXi hfi hqc hqs he using fun j ↦
    Scheme.exists_affine_model_of_isColimit F c hc (f j)
  obtain ⟨k, hk⟩ := IsFiltered.sup_objs_exists (Finset.univ.image i)
  let q (j : J) : i j ⟶ k := (hk (Finset.mem_image.mpr ⟨j, by simp, rfl⟩)).some
  refine ⟨k, fun j ↦ ?_⟩
  let := hXi j
  let := hfi j
  let := hqc j
  let := hqs j
  let Z : Over (Spec (F.obj (i j))) := Over.mk (fi j)
  let τ := Spec.map (F.map (q j))
  let σ := Spec.map (c.ι.app k)
  let Z' := (Over.pullback τ).obj Z
  have hστ : σ ≫ τ = Spec.map (c.ι.app (i j)) := by
    dsimp [σ, τ]
    rw [← Spec.map_comp, c.w]
  let ebc : (Over.pullback σ).obj Z' ≅
      (Over.pullback (Spec.map (c.ι.app (i j)))).obj Z :=
    ((Over.pullbackComp σ τ).app Z).symm ≪≫
      eqToIso (congrArg (fun h : Spec c.pt ⟶ Spec (F.obj (i j)) ↦
        (Over.pullback h).obj Z) hστ)
  refine ⟨Z'.left, Z'.hom, ?_, ?_, ?_, ?_, ⟨ebc ≪≫ Classical.choice (he j)⟩⟩
  all_goals dsimp [Z', Z, τ]; infer_instance

end Affine

/-- Finitely many actual quasi-compact open subschemes in limit chart
base changes have open models at one common stage. The comparison maps
retain their triangles to the modeled charts and are cartesian over the
actual base cone. -/
lemma Scheme.exists_common_open_chart_models_of_isLimit
    {K : Type u} [Category.{u} K] [IsCofiltered K]
    (D : K ⥤ Scheme.{u}) [∀ k, IsAffine (D.obj k)]
    (c : Cone D) (hc : IsLimit c) (i : K)
    {J : Type*} [Finite J] (X Z : J → Scheme.{u})
    (f : ∀ j, X j ⟶ D.obj i)
    (u : ∀ j, Z j ⟶ pullback (c.π.app i) (f j))
    [∀ j, IsOpenImmersion (u j)] [∀ j, CompactSpace (Z j)] :
    ∃ k : Over i, ∀ j, ∃ (V : ((Scheme.baseChangeDiagram D i (f j)).obj k).Opens)
      (g : Z j ⟶ V),
      IsCompact (V : Set ((Scheme.baseChangeDiagram D i (f j)).obj k)) ∧
      g ≫ V.ι = u j ≫ (Scheme.baseChangeCone D c i (f j)).π.app k ∧
      IsPullback g (u j ≫ pullback.fst (c.π.app i) (f j))
        (V.ι ≫ pullback.fst (D.map k.hom) (f j)) (c.π.app k.left) := by
  classical
  let : Fintype J := Fintype.ofFinite J
  have {j k : K} (q : j ⟶ k) : IsAffineHom (D.map q) := inferInstance
  choose k V hV he using fun j ↦ AlgebraicGeometry.exists_preimage_eq
    (Scheme.baseChangeDiagram D i (f j)) (Scheme.baseChangeCone D c i (f j))
    (Scheme.isLimitBaseChangeCone D c hc i (f j)) (u j).opensRange
    (isCompact_range (u j).continuous)
  obtain ⟨l, hl⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image k)
  let q (j : J) : l ⟶ k j := (hl (Finset.mem_image.mpr ⟨j, by simp, rfl⟩)).some
  refine ⟨l, fun j ↦ ?_⟩
  let W := (Scheme.baseChangeDiagram D i (f j)).map (q j) ⁻¹ᵁ V j
  have hW : IsCompact (W : Set ((Scheme.baseChangeDiagram D i (f j)).obj l)) :=
    QuasiCompact.isCompact_preimage _ (V j).isOpen (hV j)
  have heW : (Scheme.baseChangeCone D c i (f j)).π.app l ⁻¹ᵁ W = (u j).opensRange := by
    simp only [W, ← Scheme.Hom.comp_preimage, Cone.w, he]
  have hrange : Set.range (u j ≫ (Scheme.baseChangeCone D c i (f j)).π.app l) ⊆
      Set.range W.ι := by
    rintro _ ⟨z, rfl⟩
    refine ⟨⟨(u j ≫ (Scheme.baseChangeCone D c i (f j)).π.app l) z, ?_⟩, rfl⟩
    change u j z ∈ (Scheme.baseChangeCone D c i (f j)).π.app l ⁻¹ᵁ W
    rw [heW]
    exact ⟨z, rfl⟩
  let g := IsOpenImmersion.lift W.ι (u j ≫ (Scheme.baseChangeCone D c i (f j)).π.app l) hrange
  have hg : g ≫ W.ι = u j ≫ (Scheme.baseChangeCone D c i (f j)).π.app l :=
    IsOpenImmersion.lift_fac _ _ _
  have H : IsPullback g (u j) W.ι ((Scheme.baseChangeCone D c i (f j)).π.app l) :=
    IsOpenImmersion.isPullback g (u j) W.ι _ hg.symm (by simpa using heW)
  exact ⟨W, g, hW, hg, H.paste_vert (Scheme.isPullback_baseChangeCone D c i (f j) l)⟩

/-- A finite family of actual maps between limit base changes descends
to a single common stage, preserving the base triangles and every limit
comparison. -/
lemma Scheme.exists_common_homs_between_baseChanges_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    {J : Type*} [Finite J] {X Y : J → Scheme.{u}}
    (f : ∀ j, X j ⟶ D.obj i) (g : ∀ j, Y j ⟶ D.obj i)
    [∀ j, QuasiCompact (f j)] [∀ j, QuasiSeparated (f j)]
    [∀ j, LocallyOfFinitePresentation (g j)]
    (a : ∀ j, pullback (c.π.app i) (f j) ⟶ pullback (c.π.app i) (g j))
    (ha : ∀ j, a j ≫ pullback.fst (c.π.app i) (g j) = pullback.fst (c.π.app i) (f j)) :
    ∃ k : Over i, ∀ j, ∃ b : (Scheme.baseChangeDiagram D i (f j)).obj k ⟶
        (Scheme.baseChangeDiagram D i (g j)).obj k,
      b ≫ pullback.fst (D.map k.hom) (g j) = pullback.fst (D.map k.hom) (f j) ∧
      (Scheme.baseChangeCone D c i (f j)).π.app k ≫ b =
        a j ≫ (Scheme.baseChangeCone D c i (g j)).π.app k := by
  classical
  let : Fintype J := Fintype.ofFinite J
  choose k b hb hcomp using fun j ↦ Scheme.exists_hom_between_baseChanges_of_isLimit
    D c hc i (f j) (g j) (a j) (ha j)
  obtain ⟨l, hl⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image k)
  let q (j : J) : l ⟶ k j := (hl (Finset.mem_image.mpr ⟨j, by simp, rfl⟩)).some
  refine ⟨l, fun j ↦ ⟨Scheme.baseChangeDiagramMapHom D i (f j) (g j) (q j) (b j) (hb j),
    Scheme.baseChangeDiagramMapHom_fst D i (f j) (g j) (q j) (b j) (hb j), ?_⟩⟩
  exact Scheme.baseChangeDiagramMapHom_comp_π D c i (f j) (g j) (q j)
    (b j) (hb j) (a j) (ha j) (hcomp j)

/-- Finitely many equalities of actual base-change maps hold at a common
stage. The sources are QC and the targets locally of finite type. -/
lemma Scheme.exists_common_stage_baseChange_map_eq_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    {J : Type*} [Finite J] {X Y : J → Scheme.{u}}
    (f : ∀ j, X j ⟶ D.obj i) (g : ∀ j, Y j ⟶ D.obj i)
    [∀ j, QuasiCompact (f j)] [∀ j, LocallyOfFiniteType (g j)]
    (a b : ∀ j, Over.mk (f j) ⟶ Over.mk (g j))
    (hab : ∀ j, (Over.pullback (c.π.app i)).map (a j) =
      (Over.pullback (c.π.app i)).map (b j)) :
    ∃ k : Over i, ∀ j, (Over.pullback (D.map k.hom)).map (a j) =
      (Over.pullback (D.map k.hom)).map (b j) := by
  classical
  let : Fintype J := Fintype.ofFinite J
  choose k hk using fun j ↦ Scheme.exists_baseChange_map_eq_of_isLimit
    D c hc i (f j) (g j) (a j) (b j) (hab j)
  obtain ⟨l, hl⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image k)
  let q (j : J) : l ⟶ k j := (hl (Finset.mem_image.mpr ⟨j, by simp, rfl⟩)).some
  refine ⟨l, fun j ↦ ?_⟩
  let e := Over.pullbackComp (D.map (q j).left) (D.map (k j).hom)
  have h : (Over.pullback (D.map (q j).left ≫ D.map (k j).hom)).map (a j) =
      (Over.pullback (D.map (q j).left ≫ D.map (k j).hom)).map (b j) := by
    apply (cancel_mono (e.hom.app (Over.mk (g j)))).mp
    rw [e.hom.naturality, e.hom.naturality]
    exact congrArg (e.hom.app (Over.mk (f j)) ≫ ·)
      (congrArg (Over.pullback (D.map (q j).left)).map (hk j))
  have heq : D.map (q j).left ≫ D.map (k j).hom = D.map l.hom := by
    rw [← D.map_comp, Over.w (q j)]
  exact (congrArg (fun τ : D.obj l.left ⟶ D.obj i ↦
    (Over.pullback τ).map (a j) = (Over.pullback τ).map (b j)) heq).mp h

/-- Finitely many given maps of finitely presented models become
isomorphisms at one common stage when their actual limit base changes are
isomorphisms. -/
lemma Scheme.exists_common_stage_isIso_baseChange_maps_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ j, IsAffine (D.obj j)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    {J : Type*} [Finite J] {X Y : J → Scheme.{u}}
    (f : ∀ j, X j ⟶ D.obj i) (g : ∀ j, Y j ⟶ D.obj i)
    [∀ j, LocallyOfFinitePresentation (f j)] [∀ j, QuasiCompact (f j)]
    [∀ j, LocallyOfFinitePresentation (g j)] [∀ j, QuasiCompact (g j)]
    [∀ j, QuasiSeparated (g j)]
    (a : ∀ j, Over.mk (f j) ⟶ Over.mk (g j))
    [∀ j, IsIso ((Over.pullback (c.π.app i)).map (a j))] :
    ∃ k : Over i, ∀ j, IsIso ((Over.pullback (D.map k.hom)).map (a j)) := by
  classical
  let : Fintype J := Fintype.ofFinite J
  choose k hk using fun j ↦ Scheme.exists_isIso_baseChange_map_of_isLimit D c hc i (f j) (g j) (a j)
  obtain ⟨l, hl⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image k)
  let q (j : J) : l ⟶ k j := (hl (Finset.mem_image.mpr ⟨j, by simp, rfl⟩)).some
  refine ⟨l, fun j ↦ ?_⟩
  have : IsIso ((Over.pullback (D.map (k j).hom)).map (a j)) := hk j
  have h : IsIso ((Over.pullback (D.map (q j).left ≫ D.map (k j).hom)).map (a j)) :=
    (NatIso.isIso_map_iff (Over.pullbackComp (D.map (q j).left) (D.map (k j).hom)) (a j)).mpr
      (inferInstanceAs (IsIso ((Over.pullback (D.map (q j).left)).map
        ((Over.pullback (D.map (k j).hom)).map (a j)))))
  have heq : D.map (q j).left ≫ D.map (k j).hom = D.map l.hom := by
    rw [← D.map_comp, Over.w (q j)]
  exact (congrArg (fun τ : D.obj l.left ⟶ D.obj i ↦
    IsIso ((Over.pullback τ).map (a j))) heq).mp h

namespace Scheme.FinitePresentationDescent

/-- An actual finitely presented model of a specified structural map,
with the original scheme at the top left of its cartesian comparison. -/
structure Model {S S₀ Z : Scheme.{u}} (π : S ⟶ S₀) (t : Z ⟶ S) where
  /-- The stage scheme. -/
  X : Scheme.{u}
  /-- The stage structural map. -/
  f : X ⟶ S₀
  /-- Local finite presentation of the stage structural map. -/
  locallyOfFinitePresentation : LocallyOfFinitePresentation f
  /-- Quasi-compactness of the stage structural map. -/
  quasiCompact : QuasiCompact f
  /-- Quasi-separatedness of the stage structural map. -/
  quasiSeparated : QuasiSeparated f
  /-- The specified map from the original scheme to the stage scheme. -/
  p : Z ⟶ X
  /-- The actual cartesian comparison over the specified base map. -/
  square : IsPullback p t f π

attribute [instance] Model.locallyOfFinitePresentation Model.quasiCompact Model.quasiSeparated

namespace Model

variable {S S₀ Z : Scheme.{u}} {π : S ⟶ S₀} {t : Z ⟶ S}

/-- Transport a model to an explicitly identified original source,
retaining its specified structural map. -/
def ofIso (M : Model π t) {W : Scheme.{u}} (s : W ⟶ S)
    (e : W ≅ Z) (he : e.hom ≫ t = s) : Model π s where
  X := M.X
  f := M.f
  locallyOfFinitePresentation := inferInstance
  quasiCompact := inferInstance
  quasiSeparated := inferInstance
  p := e.hom ≫ M.p
  square := M.square.of_iso' e (.refl _) (.refl _) (.refl _)
    (by simp) (by simpa using he) (by simp) (by simp)

/-- Construct cartesian model data from a specified isomorphism of the
literal base change with the original over-object. -/
def ofOverIso {X : Scheme.{u}} (f : X ⟶ S₀)
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (e : (Over.pullback π).obj (Over.mk f) ≅ Over.mk t) : Model π t where
  X := X
  f := f
  locallyOfFinitePresentation := inferInstance
  quasiCompact := inferInstance
  quasiSeparated := inferInstance
  p := e.inv.left ≫ pullback.fst f π
  square := by
    have ht : e.inv.left ≫ pullback.snd f π = t := Over.w e.inv
    refine IsPullback.of_iso_pullback ⟨?_⟩ ((Over.forget S).mapIso e.symm) rfl ht
    rw [Category.assoc, pullback.condition, ← Category.assoc, ht]

/-- The model comparison as an isomorphism of the literal base change
with the specified original over-object. -/
def overIso (M : Model π t) :
    (Over.pullback π).obj (Over.mk M.f) ≅ Over.mk t :=
  Over.isoMk M.square.isoPullback.symm M.square.isoPullback_inv_snd

/-- The comparison with the point of the canonical base-change cone. -/
def rawIso (M : Model π t) : Z ≅ pullback π M.f :=
  M.square.isoPullback ≪≫ pullbackSymmetry M.f π

@[reassoc (attr := simp)]
lemma rawIso_hom_fst (M : Model π t) : M.rawIso.hom ≫ pullback.fst π M.f = t := by
  simp [rawIso]

@[reassoc (attr := simp)]
lemma rawIso_hom_snd (M : Model π t) : M.rawIso.hom ≫ pullback.snd π M.f = M.p := by
  simp [rawIso]

/-- Change a model to a later stage by the literal native pullback.
The original source and structural map are retained. -/
def rebase {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)
    (i : I) {Z : Scheme.{u}} {t : Z ⟶ c.pt} (M : Model (c.π.app i) t) (j : Over i) :
    Model (c.π.app j.left) t := by
  let H : IsPullback M.p t M.f (c.π.app j.left ≫ D.map j.hom) := by
    simpa only [c.w j.hom] using M.square
  let Q := IsPullback.of_hasPullback M.f (D.map j.hom)
  exact
    { X := pullback M.f (D.map j.hom)
      f := pullback.snd M.f (D.map j.hom)
      locallyOfFinitePresentation := inferInstance
      quasiCompact := inferInstance
      quasiSeparated := inferInstance
      p := Q.lift M.p (t ≫ c.π.app j.left) (by simpa only [Category.assoc] using H.w)
      square := H.of_right' Q }

@[reassoc (attr := simp)]
lemma rebase_p_fst {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)
    (i : I) {Z : Scheme.{u}} {t : Z ⟶ c.pt} (M : Model (c.π.app i) t) (j : Over i) :
    (M.rebase D c i j).p ≫ pullback.fst M.f (D.map j.hom) = M.p := by
  simp [rebase]

@[reassoc (attr := simp)]
lemma rebase_p_snd {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)
    (i : I) {Z : Scheme.{u}} {t : Z ⟶ c.pt} (M : Model (c.π.app i) t) (j : Over i) :
    (M.rebase D c i j).p ≫ pullback.snd M.f (D.map j.hom) = t ≫ c.π.app j.left := by
  simp [rebase]

/-- A stage map which represents a specified original isomorphism is an
isomorphism after literal base change to the original base. -/
lemma isIso_baseChange_map {W : Scheme.{u}} {s : W ⟶ S}
    (M : Model π t) (N : Model π s) (a : M.X ⟶ N.X) (ha : a ≫ N.f = M.f)
    (e : Z ≅ W) (he : e.hom ≫ s = t) (hp : M.p ≫ a = e.hom ≫ N.p) :
    IsIso ((Over.pullback π).map (Over.homMk a ha : Over.mk M.f ⟶ Over.mk N.f)) := by
  let E : (Over.pullback π).obj (Over.mk M.f) ≅
      (Over.pullback π).obj (Over.mk N.f) :=
    M.overIso ≪≫ (Over.isoMk e he : Over.mk t ≅ Over.mk s) ≪≫ N.overIso.symm
  have h : (Over.pullback π).map (Over.homMk a ha) = E.hom := by
    apply Over.OverMorphism.ext
    apply (cancel_epi M.square.isoPullback.hom).mp
    apply pullback.hom_ext (f := N.f) (g := π)
    · simp [E, overIso, Over.pullback_map_left, Category.assoc, hp]
    · simp [E, overIso, Over.pullback_map_left, Category.assoc, he]
  rw [h]
  infer_instance

@[reassoc (attr := simp)]
lemma rawIso_inv_struct (M : Model π t) : M.rawIso.inv ≫ t = pullback.fst π M.f := by
  exact (Iso.inv_comp_eq M.rawIso).mpr M.rawIso_hom_fst.symm

@[reassoc]
lemma rebase_p_comp_symmetry_inv {I : Type u} [Category.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (i : I) {Z : Scheme.{u}} {t : Z ⟶ c.pt}
    (M : Model (c.π.app i) t) (j : Over i) :
    (M.rebase D c i j).p ≫ (pullbackSymmetry (D.map j.hom) M.f).inv =
      M.rawIso.hom ≫ (Scheme.baseChangeCone D c i M.f).π.app j := by
  apply pullback.hom_ext (f := D.map j.hom) (g := M.f) <;> simp [Category.assoc]

/-- A map of actual models which represents the specified original map. -/
structure Map {W : Scheme.{u}} {s : W ⟶ S}
    (M : Model π t) (N : Model π s) (m : Over.mk t ⟶ Over.mk s) where
  /-- The actual stage morphism over the stage base. -/
  hom : Over.mk M.f ⟶ Over.mk N.f
  /-- Compatibility with the specified original scheme maps. -/
  comm : M.p ≫ hom.left = m.left ≫ N.p

namespace Map

variable {W V : Scheme.{u}} {s : W ⟶ S} {r : V ⟶ S}
  {M : Model π t} {N : Model π s} {P : Model π r}
  {m : Over.mk t ⟶ Over.mk s} {n : Over.mk s ⟶ Over.mk r}

/-- A compatible map of actual models gives a cartesian square between
the original and stage arrows. -/
lemma isPullback (a : Map M N m) : IsPullback m.left M.p N.p a.hom.left := by
  have hm : m.left ≫ s = t := Over.w m
  have ha : a.hom.left ≫ N.f = M.f := Over.w a.hom
  have H : IsPullback M.p (m.left ≫ s) (a.hom.left ≫ N.f) π := by
    simpa only [hm, ha] using M.square
  exact (H.of_bot a.comm N.square).flip

/-- The literal base-change isomorphisms commute with a map that models
the specified original arrow. -/
@[reassoc]
lemma overIso_naturality (a : Map M N m) :
    (Over.pullback π).map a.hom ≫ N.overIso.hom = M.overIso.hom ≫ m := by
  apply (cancel_epi M.overIso.inv).mp
  apply (cancel_mono N.overIso.inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc]
  apply Over.OverMorphism.ext
  apply pullback.hom_ext (f := N.f) (g := π)
  · simp [overIso, Over.pullback_map_left, Category.assoc, a.comm]
  · have hm : m.left ≫ s = t := Over.w m
    simp [overIso, Over.pullback_map_left, Category.assoc, hm]

/-- The identity map of an actual model. -/
def id (M : Model π t) : Map M M (𝟙 (Over.mk t)) := ⟨𝟙 _, by simp⟩

/-- Compose maps of actual models, preserving the specified original maps. -/
def comp (a : Map M N m) (b : Map N P n) : Map M P (m ≫ n) where
  hom := a.hom ≫ b.hom
  comm := by simp [Category.assoc, reassoc_of% a.comm, b.comm]

/-- Rebase a map using the actual native base-change functor. -/
def rebase {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)
    (i : I) {Z W : Scheme.{u}} {t : Z ⟶ c.pt} {s : W ⟶ c.pt}
    {M : Model (c.π.app i) t} {N : Model (c.π.app i) s}
    {m : Over.mk t ⟶ Over.mk s} (a : Map M N m) (j : Over i) :
    Map (M.rebase D c i j) (N.rebase D c i j) m where
  hom := (Over.pullback (D.map j.hom)).map a.hom
  comm := by
    apply pullback.hom_ext (f := N.f) (g := D.map j.hom)
    · simp [Over.pullback_map_left, Category.assoc, a.comm]
    · have hm : m.left ≫ s = t := Over.w m
      simp [Over.pullback_map_left, Category.assoc, reassoc_of% hm]

/-- Two maps representing the same original map agree after literal base change. -/
lemma baseChange_eq (a b : Map M N m) :
    (Over.pullback π).map a.hom = (Over.pullback π).map b.hom := by
  apply Over.OverMorphism.ext
  apply (cancel_epi M.square.isoPullback.hom).mp
  apply pullback.hom_ext (f := N.f) (g := π)
  · simp [Over.pullback_map_left, Category.assoc, a.comm, b.comm]
  · simp [Over.pullback_map_left, Category.assoc]

/-- A map representing an original isomorphism becomes an isomorphism
under the actual base change. -/
lemma isIso_baseChange (a : Map M N m) [IsIso m] :
    IsIso ((Over.pullback π).map a.hom) := by
  have hm : ((Over.forget S).mapIso (asIso m)).hom ≫ s = t := Over.w m
  simpa only [Over.homMk_eta] using M.isIso_baseChange_map N a.hom.left (Over.w a.hom)
    ((Over.forget S).mapIso (asIso m)) hm a.comm

end Map

/-- Finitely many specified original arrows between modeled objects have
maps of the actual models after one common later base change. -/
lemma exists_common_maps {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    {O A : Type*} [Finite A] (source target : A → O)
    (Z : O → Scheme.{u}) (t : ∀ o, Z o ⟶ c.pt)
    (M : ∀ o, Model (c.π.app i) (t o))
    (m : ∀ a, Over.mk (t (source a)) ⟶ Over.mk (t (target a))) :
    ∃ j : Over i, ∀ a, Nonempty
      (Map ((M (source a)).rebase D c i j) ((M (target a)).rebase D c i j) (m a)) := by
  classical
  let raw (a : A) := (M (source a)).rawIso.inv ≫ (m a).left ≫ (M (target a)).rawIso.hom
  have hm (a : A) : (m a).left ≫ t (target a) = t (source a) := Over.w (m a)
  obtain ⟨j, hj⟩ := Scheme.exists_common_homs_between_baseChanges_of_isLimit D c hc i
    (fun a ↦ (M (source a)).f) (fun a ↦ (M (target a)).f) raw (fun a ↦ by
      simp [raw, Category.assoc, hm a])
  choose b hb hcomp using hj
  refine ⟨j, fun a ↦ ?_⟩
  let b' : ((M (source a)).rebase D c i j).X ⟶ ((M (target a)).rebase D c i j).X :=
    (pullbackSymmetry (D.map j.hom) (M (source a)).f).inv ≫ b a ≫
      (pullbackSymmetry (D.map j.hom) (M (target a)).f).hom
  have hb' : b' ≫ ((M (target a)).rebase D c i j).f = ((M (source a)).rebase D c i j).f := by
    change b' ≫ pullback.snd (M (target a)).f (D.map j.hom) =
      pullback.snd (M (source a)).f (D.map j.hom)
    simpa [b', Category.assoc] using congrArg
      ((pullbackSymmetry (D.map j.hom) (M (source a)).f).inv ≫ ·) (hb a)
  refine ⟨⟨Over.homMk b' hb', ?_⟩⟩
  change ((M (source a)).rebase D c i j).p ≫ b' =
    (m a).left ≫ ((M (target a)).rebase D c i j).p
  apply (cancel_mono (pullbackSymmetry (D.map j.hom) (M (target a)).f).inv).mp
  simp only [b', Category.assoc, Iso.hom_inv_id, Category.comp_id,
    rebase_p_comp_symmetry_inv_assoc, rebase_p_comp_symmetry_inv]
  simpa only [raw, Category.assoc, Iso.hom_inv_id_assoc] using
    congrArg ((M (source a)).rawIso.hom ≫ ·) (hcomp a)

/-- A specified arrow between two original objects admits a map of their
actual models at a later stage, with its original comparison retained. -/
lemma exists_map {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    {Z W : Scheme.{u}} {t : Z ⟶ c.pt} {s : W ⟶ c.pt}
    (M : Model (c.π.app i) t) (N : Model (c.π.app i) s)
    (m : Over.mk t ⟶ Over.mk s) :
    ∃ j : Over i, Nonempty (Map (M.rebase D c i j) (N.rebase D c i j) m) := by
  let Z' : Bool → Scheme.{u} := Bool.rec Z W
  let t' : ∀ b, Z' b ⟶ c.pt := Bool.rec t s
  let M' : ∀ b, Model (c.π.app i) (t' b) := Bool.rec M N
  obtain ⟨j, hj⟩ := exists_common_maps D c hc i
    (fun _ : Unit ↦ false) (fun _ : Unit ↦ true) Z' t' M' (fun _ ↦ m)
  exact ⟨j, hj ()⟩

/-- A finite family of specified quasi-compact open immersions into
modeled objects has actual open submodels at one common later stage.
Each inclusion represents the given original arrow. -/
lemma exists_common_open_submodels {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    {J : Type*} [Finite J] {Z W : J → Scheme.{u}}
    (t : ∀ j, Z j ⟶ c.pt) (s : ∀ j, W j ⟶ c.pt)
    (M : ∀ j, Model (c.π.app i) (t j))
    (m : ∀ j, Over.mk (s j) ⟶ Over.mk (t j))
    [∀ j, IsOpenImmersion (m j).left] [∀ j, CompactSpace (W j)] :
    ∃ k : Over i, ∀ j, ∃ N : Model (c.π.app k.left) (s j),
      ∃ a : Map N ((M j).rebase D c i k) (m j), IsOpenImmersion a.hom.left := by
  let u (j : J) := (m j).left ≫ (M j).rawIso.hom
  have (j : J) : IsOpenImmersion (u j) := inferInstance
  obtain ⟨k, hk⟩ := Scheme.exists_common_open_chart_models_of_isLimit D c hc i
    (fun j ↦ (M j).X) W (fun j ↦ (M j).f) u
  refine ⟨k, fun j ↦ ?_⟩
  obtain ⟨V, p, hV, hcomm, H⟩ := hk j
  have : CompactSpace V := isCompact_iff_compactSpace.mp hV
  have hm : (m j).left ≫ t j = s j := Over.w (m j)
  let N : Model (c.π.app k.left) (s j) :=
    { X := V
      f := V.ι ≫ pullback.fst (D.map k.hom) (M j).f
      locallyOfFinitePresentation := inferInstance
      quasiCompact := inferInstance
      quasiSeparated := inferInstance
      p := p
      square := by simpa only [u, Category.assoc, rawIso_hom_fst, hm] using H }
  let a : N.X ⟶ ((M j).rebase D c i k).X :=
    V.ι ≫ (pullbackSymmetry (D.map k.hom) (M j).f).hom
  have ha : a ≫ ((M j).rebase D c i k).f = N.f := by
    change (V.ι ≫ (pullbackSymmetry _ _).hom) ≫ pullback.snd _ _ = _
    simp [N, Category.assoc]
  have hpa : N.p ≫ a = (m j).left ≫ ((M j).rebase D c i k).p := by
    apply (cancel_mono (pullbackSymmetry (D.map k.hom) (M j).f).inv).mp
    simp only [N, a, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      rebase_p_comp_symmetry_inv]
    simpa only [u, Category.assoc] using hcomm
  exact ⟨N, ⟨Over.homMk a ha, hpa⟩, inferInstanceAs (IsOpenImmersion a)⟩

end Model

/-- A cover by quasi-separated schemes with compact pairwise intersections
gives a quasi-separated scheme. The components need not be affine. -/
lemma quasiSeparatedSpace_of_cover {X : Scheme.{u}} (𝒰 : X.OpenCover)
    [∀ i, QuasiSeparatedSpace (𝒰.X i)]
    [∀ i j, CompactSpace (pullback (C := Scheme) (𝒰.f i) (𝒰.f j))] :
    QuasiSeparatedSpace X := by
  let 𝒱 : X.OpenCover := 𝒰.bind fun i ↦ (𝒰.X i).affineCover
  have (i : 𝒱.I₀) : IsAffine (𝒱.X i) := inferInstanceAs
    (IsAffine (((𝒰.X i.1).affineCover).X i.2))
  refine Scheme.quasiSeparatedSpace_of_isOpenCover (fun i ↦ (𝒱.f i).opensRange)
    𝒱.isOpenCover_opensRange (fun i ↦ isAffineOpen_opensRange (𝒱.f i)) ?_
  intro i j
  let q : pullback (𝒱.f i) (𝒱.f j) ⟶ pullback (𝒰.f i.1) (𝒰.f j.1) :=
    pullback.map _ _ _ _ ((𝒰.X i.1).affineCover.f i.2) ((𝒰.X j.1).affineCover.f j.2)
      (𝟙 X) (by simp [𝒱]) (by simp [𝒱])
  have : QuasiCompact q := MorphismProperty.pullbackMap (P := @QuasiCompact)
    (inferInstanceAs (QuasiCompact ((𝒰.X i.1).affineCover.f i.2)))
    (inferInstanceAs (QuasiCompact ((𝒰.X j.1).affineCover.f j.2))) rfl rfl
  have : CompactSpace (pullback (C := Scheme) (𝒱.f i) (𝒱.f j)) :=
    QuasiCompact.compactSpace_of_compactSpace q
  have h := isCompact_range (pullback.fst (𝒱.f i) (𝒱.f j) ≫ 𝒱.f i).continuous
  simpa only [IsOpenImmersion.range_pullback_to_base_of_left,
    Scheme.Hom.coe_opensRange] using h

namespace Model

/-- Glue a finite locally directed diagram of actual models. The source
cocone is the specified original scheme, and the resulting comparison is
cartesian over the specified base map. This constructor does not assume
that arbitrary schemes already have models. -/
def ofOpenDiagram {S S₀ : Scheme.{u}} [IsAffine S₀] (π : S ⟶ S₀)
    {J : Type v} [SmallCategory J] [Finite J] [Small.{u} J] [Quiver.IsThin J]
    (F G : J ⥤ Scheme.{u})
    [∀ {i j} (a : i ⟶ j), IsOpenImmersion (G.map a)]
    [(G ⋙ Scheme.forget).IsLocallyDirected]
    (s : Cocone F) (hs : IsColimit s) (t : s.pt ⟶ S)
    (g : G ⟶ (Functor.const J).obj S₀) (p : F ⟶ G)
    [∀ j, LocallyOfFinitePresentation (g.app j)]
    [∀ j, QuasiCompact (g.app j)] [∀ j, QuasiSeparated (g.app j)]
    (H : ∀ j, IsPullback (p.app j) (s.ι.app j ≫ t) (g.app j) π) : Model π t := by
  let : HasColimit F := ⟨s, hs⟩
  let 𝒰 : (colimit G).OpenCover :=
    { I₀ := J
      X := G.obj
      f := colimit.ι G
      mem₀ := by
        rw [presieve₀_mem_precoverage_iff]
        exact ⟨Scheme.IsLocallyDirected.ι_jointly_surjective G, inferInstance⟩ }
  let : 𝒰.LocallyDirected :=
    { trans := fun a ↦ G.map a
      directed := by
        intro i j x
        obtain ⟨k, fi, fj, y, hyi, hyj⟩ :=
          (Scheme.IsLocallyDirected.ι_eq_ι_iff G).mp
            (show colimit.ι G i (pullback.fst (𝒰.f i) (𝒰.f j) x) =
              colimit.ι G j (pullback.snd (𝒰.f i) (𝒰.f j) x) from
              congr($(pullback.condition (f := 𝒰.f i) (g := 𝒰.f j)) x))
        refine ⟨k, fi, fj, y, ?_⟩
        apply (pullback.fst (𝒰.f i) (𝒰.f j)).isOpenEmbedding.injective
        simpa only [← Scheme.Hom.comp_apply, pullback.lift_fst] using hyi }
  have (j : J) : IsAffine (((Functor.const J).obj S₀).obj j) := inferInstanceAs (IsAffine S₀)
  have hcomp (j : J) : CompactSpace (G.obj j) :=
    QuasiCompact.compactSpace_of_compactSpace (g.app j)
  have hqs (j : J) : QuasiSeparatedSpace (G.obj j) :=
    quasiSeparatedSpace_of_quasiSeparated (g.app j)
  have : CompactSpace (colimit G : Scheme.{u}) := 𝒰.compactSpace
  have (i j : 𝒰.I₀) : CompactSpace (pullback (C := Scheme) (𝒰.f i) (𝒰.f j)) := by
    let 𝒲 : (pullback (𝒰.f i) (𝒰.f j)).OpenCover := 𝒰.intersectionOfLocallyDirected i j
    have : Finite 𝒲.I₀ := inferInstanceAs (Finite (Σ k : J, (k ⟶ i) × (k ⟶ j)))
    have (k : 𝒲.I₀) : CompactSpace (𝒲.X k) := hcomp k.1
    exact 𝒲.compactSpace
  have : QuasiSeparatedSpace (colimit G : Scheme.{u}) :=
    Scheme.FinitePresentationDescent.quasiSeparatedSpace_of_cover 𝒰
  have hp : p.Equifibered := by
    intro i j a
    have hg : G.map a ≫ g.app j = g.app i := by simp
    have H' : IsPullback (p.app i) (F.map a ≫ (s.ι.app j ≫ t))
        (G.map a ≫ g.app j) π := by
      simpa only [hg, ← Category.assoc, s.w a] using H i
    exact (H'.of_bot (p.naturality a).symm (H j)).flip
  let d : 𝒰.RelativeGluingData :=
    { functor := F
      natTrans := { app := p.app, naturality := p.naturality }
      equifibered := hp }
  let fG : colimit G ⟶ S₀ := colimit.desc G { pt := S₀, ι := g }
  let fF : colimit F ⟶ S := colimit.desc F (s.extend t)
  have hfG (j : J) : colimit.ι G j ≫ fG = g.app j := by simp [fG]
  have hfF (j : J) : colimit.ι F j ≫ fF = s.ι.app j ≫ t := by simp [fF]
  have : LocallyOfFinitePresentation fG := by
    apply IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFinitePresentation) 𝒰
    intro j
    change LocallyOfFinitePresentation (colimit.ι G j ≫ fG)
    rw [hfG]
    infer_instance
  have Hglue : IsPullback d.toBase fF fG π := by
    refine Scheme.isPullback_of_openCover d.toBase fF fG π 𝒰 ?_
    intro j
    let E := (d.isPullback_natTrans_ι_toBase j).flip.isoPullback
    refine (H j).of_iso E (.refl _) (.refl _) (.refl _) ?_ ?_ ?_ ?_
    · simp [E, d, Scheme.Cover.pullbackHom]
    · simp [E, d, fF]
    · simp [𝒰, fG]
    · simp
  let N : Model π fF :=
    { X := colimit G
      f := fG
      locallyOfFinitePresentation := inferInstance
      quasiCompact := inferInstance
      quasiSeparated := inferInstance
      p := d.toBase
      square := Hglue }
  let e := hs.coconePointUniqueUpToIso (colimit.isColimit F)
  apply N.ofIso t e
  apply hs.hom_ext
  intro j
  simp [e, hfF]

end Model

/-- The actual binary open-cover cocone. -/
private def binaryCocone {X W : Scheme.{u}} (U : Bool → Scheme.{u})
    (p : ∀ b, W ⟶ U b) (f : ∀ b, U b ⟶ X)
    (h : p false ≫ f false = p true ≫ f true) :
    Cocone (WidePushoutShape.wideSpan W U p) :=
  WidePushoutShape.mkCocone (p false ≫ f false) f (by
    intro b
    cases b
    · rfl
    · exact h.symm)

/-- Two open subschemes with their actual intersection have the original
covered scheme as their colimit. -/
private def binaryCoconeIsColimit {X W : Scheme.{u}} (U : Bool → Scheme.{u})
    (p : ∀ b, W ⟶ U b) (f : ∀ b, U b ⟶ X)
    [∀ b, IsOpenImmersion (f b)]
    (hcover : ∀ x : X, ∃ b, ∃ y, f b y = x)
    (H : IsPullback (p false) (p true) (f false) (f true)) :
    IsColimit (binaryCocone U p f H.w) := by
  let 𝒰 : X.OpenCover :=
    { I₀ := Bool
      X := U
      f := f
      mem₀ := by rw [presieve₀_mem_precoverage_iff]; exact ⟨hcover, inferInstance⟩ }
  let F := WidePushoutShape.wideSpan W U p
  have hcomp (q : Cocone F) (b c : Bool) :
      pullback.fst (f b) (f c) ≫ q.ι.app (some b) =
        pullback.snd (f b) (f c) ≫ q.ι.app (some c) := by
    cases b <;> cases c
    · rw [(cancel_mono (f false)).mp (pullback.condition (f := f false) (g := f false))]
    · apply (cancel_epi H.isoPullback.hom).mp
      simp only [H.isoPullback_hom_fst_assoc, H.isoPullback_hom_snd_assoc]
      exact (q.w (.init false)).trans (q.w (.init true)).symm
    · apply (cancel_epi H.flip.isoPullback.hom).mp
      simp only [H.flip.isoPullback_hom_fst_assoc, H.flip.isoPullback_hom_snd_assoc]
      exact (q.w (.init true)).trans (q.w (.init false)).symm
    · rw [(cancel_mono (f true)).mp (pullback.condition (f := f true) (g := f true))]
  let desc (q : Cocone F) : X ⟶ q.pt := 𝒰.glueMorphisms (fun b ↦ q.ι.app (some b)) (hcomp q)
  have hdesc (q : Cocone F) (b : Bool) : f b ≫ desc q = q.ι.app (some b) :=
    𝒰.ι_glueMorphisms _ _ b
  refine { desc := desc, fac := ?_, uniq := ?_ }
  · intro q j
    cases j with
    | none =>
      change (p false ≫ f false) ≫ desc q = q.ι.app none
      rw [Category.assoc, hdesc]
      exact q.w (.init false)
    | some b => exact hdesc q b
  · intro q m hm
    apply 𝒰.hom_ext
    intro b
    exact (hm (some b)).trans (hdesc q b).symm

/-- The actual two-open cover of their union. -/
private def supOpenCover {X : Scheme.{u}} (U V : X.Opens) : (U ⊔ V).toScheme.OpenCover where
  I₀ := Bool
  X := Bool.rec U.toScheme V.toScheme
  f := Bool.rec (X.homOfLE le_sup_left) (X.homOfLE le_sup_right)
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨?_, ?_⟩
    · intro x
      rcases x.2 with hx | hx
      · refine ⟨false, ⟨x.1, hx⟩, ?_⟩
        exact X.homOfLE_apply' le_sup_left x.1 hx
      · refine ⟨true, ⟨x.1, hx⟩, ?_⟩
        exact X.homOfLE_apply' le_sup_right x.1 hx
    · intro b
      cases b <;> infer_instance

/-- Models of two open pieces and compactness of their actual intersection
produce a model of the original covered scheme at a later stage. The
overlap is modeled as an actual open on each side, and its identity is
descended before gluing. -/
lemma Model.exists_of_binary_cover {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    {X W : Scheme.{u}} [CompactSpace W] (U : Bool → Scheme.{u})
    (p : ∀ b, W ⟶ U b) (f : ∀ b, U b ⟶ X) [∀ b, IsOpenImmersion (f b)]
    (hcover : ∀ x : X, ∃ b, ∃ y, f b y = x)
    (H : IsPullback (p false) (p true) (f false) (f true))
    (t : X ⟶ c.pt) (M : ∀ b, Model (c.π.app i) (f b ≫ t)) :
    ∃ k : Over i, Nonempty (Model (c.π.app k.left) t) := by
  classical
  let w : W ⟶ c.pt := p false ≫ (f false ≫ t)
  let m (b : Bool) : Over.mk w ⟶ Over.mk (f b ≫ t) := Over.homMk (p b) (by
    cases b
    · rfl
    · change p true ≫ (f true ≫ t) = w
      simpa only [w, Category.assoc] using congrArg (· ≫ t) H.w.symm)
  have (b : Bool) : IsOpenImmersion (m b).left := by
    cases b
    · exact MorphismProperty.of_isPullback (P := @IsOpenImmersion) H.flip inferInstance
    · exact MorphismProperty.of_isPullback (P := @IsOpenImmersion) H inferInstance
  obtain ⟨k, hk⟩ := Model.exists_common_open_submodels D c hc i
    (fun b ↦ f b ≫ t) (fun _ : Bool ↦ w) M m
  choose N A hA using hk
  obtain ⟨j, ⟨a⟩⟩ := Model.exists_map D c hc k.left (N false) (N true) (𝟙 (Over.mk w))
  have : IsIso ((Over.pullback (c.π.app j.left)).map a.hom) := a.isIso_baseChange
  obtain ⟨l, hl⟩ := Scheme.exists_isIso_baseChange_map_of_isLimit D c hc j.left
    ((N false).rebase D c k.left j).f ((N true).rebase D c k.left j).f a.hom
  let M' (b : Bool) := (((M b).rebase D c i k).rebase D c k.left j).rebase D c j.left l
  let N' (b : Bool) := ((N b).rebase D c k.left j).rebase D c j.left l
  let A' (b : Bool) : Model.Map (N' b) (M' b) (m b) :=
    ((A b).rebase D c k.left j).rebase D c j.left l
  let a' : Model.Map (N' false) (N' true) (𝟙 (Over.mk w)) := a.rebase D c j.left l
  have : IsIso a'.hom := hl
  have : IsIso a'.hom.left :=
    inferInstanceAs (IsIso ((Over.forget (D.obj l.left)).map a'.hom))
  have hA' (b : Bool) : IsOpenImmersion (A' b).hom.left :=
    MorphismProperty.overPullbackMap (P := @IsOpenImmersion) (D.map l.hom) _
      (MorphismProperty.overPullbackMap (P := @IsOpenImmersion) (D.map j.hom) _ (hA b))
  let B : ∀ b, Model.Map (N' false) (M' b) (m b) :=
    Bool.rec (A' false) (by simpa only [Category.id_comp] using a'.comp (A' true))
  have (b : Bool) : IsOpenImmersion (B b).hom.left := by
    cases b
    · exact hA' false
    · change IsOpenImmersion (a'.hom.left ≫ (A' true).hom.left)
      have := hA' true
      infer_instance
  let F := WidePushoutShape.wideSpan W U p
  let G := WidePushoutShape.wideSpan (N' false).X (fun b ↦ (M' b).X)
    (fun b ↦ (B b).hom.left)
  have {x y : WidePushoutShape Bool} (h : x ⟶ y) : IsOpenImmersion (G.map h) := by
    cases h with
    | id x =>
      change IsOpenImmersion (𝟙 _)
      infer_instance
    | init b =>
      change IsOpenImmersion (B b).hom.left
      infer_instance
  let g : G ⟶ (Functor.const (WidePushoutShape Bool)).obj (D.obj l.left) :=
    { app := fun q ↦ match q with
        | none => (N' false).f
        | some b => (M' b).f
      naturality := by
        intro x y h
        cases h with
        | id x => simp
        | init b =>
          change (B b).hom.left ≫ (M' b).f = (N' false).f ≫ 𝟙 _
          simpa only [Category.comp_id, Over.mk_hom] using Over.w (B b).hom }
  let p' : F ⟶ G :=
    { app := fun q ↦ match q with
        | none => (N' false).p
        | some b => (M' b).p
      naturality := by
        intro x y h
        cases h with
        | id x => simp
        | init b => exact (B b).comm.symm }
  have (q : WidePushoutShape Bool) : LocallyOfFinitePresentation (g.app q) := by
    cases q with
    | none => exact (N' false).locallyOfFinitePresentation
    | some b => exact (M' b).locallyOfFinitePresentation
  have (q : WidePushoutShape Bool) : QuasiCompact (g.app q) := by
    cases q with
    | none => exact (N' false).quasiCompact
    | some b => exact (M' b).quasiCompact
  have (q : WidePushoutShape Bool) : QuasiSeparated (g.app q) := by
    cases q with
    | none => exact (N' false).quasiSeparated
    | some b => exact (M' b).quasiSeparated
  let s := binaryCocone U p f H.w
  have hs : IsColimit s := binaryCoconeIsColimit U p f hcover H
  have Hp (q : WidePushoutShape Bool) :
      IsPullback (p'.app q) (s.ι.app q ≫ t) (g.app q) (c.π.app l.left) := by
    cases q with
    | none =>
      change IsPullback (N' false).p ((p false ≫ f false) ≫ t) (N' false).f (c.π.app l.left)
      simpa only [w, Category.assoc] using (N' false).square
    | some b => exact (M' b).square
  exact ⟨Over.mk (l.hom ≫ j.hom ≫ k.hom),
    ⟨Model.ofOpenDiagram (c.π.app l.left) F G s hs t g p' Hp⟩⟩

/-- A finite diagram of specified original objects with actual models
descends to a single later stage, including identities, compositions, and
the natural literal-base-change comparison. -/
lemma Model.exists_diagram {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    {J : Type v} [SmallCategory J] [Finite J] [∀ j k : J, Finite (j ⟶ k)]
    (Z : J ⥤ Scheme.{u}) (t : Z ⟶ (Functor.const J).obj c.pt)
    (M : ∀ j, Model (c.π.app i) (t.app j)) :
    ∃ k : Over i, ∃ F : J ⥤ Over (D.obj k.left),
      (∀ j, LocallyOfFinitePresentation (F.obj j).hom) ∧
      (∀ j, QuasiCompact (F.obj j).hom) ∧ (∀ j, QuasiSeparated (F.obj j).hom) ∧
      Nonempty (F ⋙ Over.pullback (c.π.app k.left) ≅ Over.lift Z t) := by
  classical
  let Arrows := Σ j : J, Σ k : J, (j ⟶ k)
  let L := Over.lift Z t
  obtain ⟨j, hj⟩ := Model.exists_common_maps D c hc i
    (fun a : Arrows ↦ a.1) (fun a : Arrows ↦ a.2.1) Z.obj t.app M
    (fun a ↦ L.map a.2.2)
  let N (k : J) := (M k).rebase D c i j
  let a (k l : J) (h : k ⟶ l) : Model.Map (N k) (N l) (L.map h) :=
    Classical.choice (hj ⟨k, l, h⟩)
  let Relations := J ⊕ (Σ k : J, Σ l : J, Σ m : J, (k ⟶ l) × (l ⟶ m))
  let src : Relations → J := Sum.elim id (fun r ↦ r.1)
  let dst : Relations → J := Sum.elim id (fun r ↦ r.2.2.1)
  let lhs : ∀ r, Over.mk (N (src r)).f ⟶ Over.mk (N (dst r)).f := fun r ↦ by
    rcases r with k | ⟨k, l, m, h, q⟩
    · exact (a k k (𝟙 k)).hom
    · exact (a k m (h ≫ q)).hom
  let rhs : ∀ r, Over.mk (N (src r)).f ⟶ Over.mk (N (dst r)).f := fun r ↦ by
    rcases r with k | ⟨k, l, m, h, q⟩
    · exact 𝟙 _
    · exact (a k l h).hom ≫ (a l m q).hom
  have heq (r : Relations) :
      (Over.pullback (c.π.app j.left)).map (lhs r) =
        (Over.pullback (c.π.app j.left)).map (rhs r) := by
    apply (cancel_mono (N (dst r)).overIso.hom).mp
    rcases r with k | ⟨k, l, m, h, q⟩
    · change (Over.pullback (c.π.app j.left)).map (a k k (𝟙 k)).hom ≫
          (N k).overIso.hom = (Over.pullback (c.π.app j.left)).map (𝟙 _) ≫ (N k).overIso.hom
      calc
        _ = (N k).overIso.hom ≫ L.map (𝟙 k) := (a k k (𝟙 k)).overIso_naturality
        _ = (N k).overIso.hom ≫ 𝟙 (L.obj k) :=
          congrArg (fun h : L.obj k ⟶ L.obj k ↦ (N k).overIso.hom ≫ h) (L.map_id k)
        _ = (N k).overIso.hom := Category.comp_id _
        _ = (Over.pullback (c.π.app j.left)).map (𝟙 _) ≫ (N k).overIso.hom :=
          ((congrArg (· ≫ (N k).overIso.hom)
            ((Over.pullback (c.π.app j.left)).map_id (Over.mk (N k).f))).trans
              (Category.id_comp _)).symm
    · change (Over.pullback (c.π.app j.left)).map (a k m (h ≫ q)).hom ≫
          (N m).overIso.hom = (Over.pullback (c.π.app j.left)).map
            ((a k l h).hom ≫ (a l m q).hom) ≫ (N m).overIso.hom
      rw [(a k m (h ≫ q)).overIso_naturality]
      simp only [Functor.map_comp, Category.assoc, (a l m q).overIso_naturality,
        (a k l h).overIso_naturality_assoc]
  obtain ⟨k, hk⟩ := Scheme.exists_common_stage_baseChange_map_eq_of_isLimit D c hc j.left
    (fun r ↦ (N (src r)).f) (fun r ↦ (N (dst r)).f) lhs rhs heq
  let N' (l : J) := (N l).rebase D c j.left k
  let F : J ⥤ Over (D.obj k.left) :=
    { obj := fun l ↦ Over.mk (N' l).f
      map := fun h ↦ (Over.pullback (D.map k.hom)).map (a _ _ h).hom
      map_id := fun l ↦ by
        change (Over.pullback (D.map k.hom)).map (a l l (𝟙 l)).hom =
          𝟙 ((Over.pullback (D.map k.hom)).obj (Over.mk (N l).f))
        have H := hk (.inl l)
        change (Over.pullback (D.map k.hom)).map (a l l (𝟙 l)).hom =
          (Over.pullback (D.map k.hom)).map (𝟙 (Over.mk (N l).f)) at H
        exact H.trans ((Over.pullback (D.map k.hom)).map_id _)
      map_comp := fun h q ↦ by
        simpa only [lhs, rhs, Functor.map_comp] using hk (.inr ⟨_, _, _, h, q⟩) }
  let e : F ⋙ Over.pullback (c.π.app k.left) ≅ L :=
    NatIso.ofComponents (fun l ↦ (N' l).overIso) (fun h ↦
      ((a _ _ h).rebase D c j.left k).overIso_naturality)
  exact ⟨Over.mk (k.hom ≫ j.hom), F, fun l ↦ (N' l).locallyOfFinitePresentation,
    fun l ↦ (N' l).quasiCompact, fun l ↦ (N' l).quasiSeparated, ⟨e⟩⟩


end Scheme.FinitePresentationDescent

/-- Every finitely presented scheme over an actual filtered ring colimit
has a finitely presented stage model. The specified comparison is from
the literal native base change to the original scheme with its original
structural map. No separatedness or injectivity of stage maps is assumed. -/
lemma Scheme.exists_model_of_isColimit
    {I : Type u} [Category.{u} I] [IsFiltered I]
    (F : I ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
    {X : Scheme.{u}} (f : X ⟶ Spec c.pt)
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f] :
    ∃ (i : I) (Xᵢ : Scheme.{u}) (fᵢ : Xᵢ ⟶ Spec (F.obj i)),
      LocallyOfFinitePresentation fᵢ ∧ QuasiCompact fᵢ ∧ QuasiSeparated fᵢ ∧
      Nonempty ((Over.pullback (Spec.map (c.ι.app i))).obj (Over.mk fᵢ) ≅ Over.mk f) := by
  classical
  let D : Iᵒᵖ ⥤ Scheme.{u} := F.op ⋙ Scheme.Spec
  let C : Cone D := Scheme.Spec.mapCone c.op
  have hC : IsLimit C := isLimitOfPreserves Scheme.Spec hc.op
  have (i : Iᵒᵖ) : IsAffine (D.obj i) :=
    inferInstanceAs (IsAffine (Spec (F.obj i.unop)))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  let P (U : X.Opens) : Prop := ∃ i : Iᵒᵖ,
    Nonempty (Scheme.FinitePresentationDescent.Model (C.π.app i) (U.ι ≫ f))
  have haff (U : X.Opens) [IsAffine U.toScheme] : P U := by
    obtain ⟨i, Z, g, hZ, hg, hqc, hqs, ⟨e⟩⟩ :=
      Scheme.exists_affine_model_of_isColimit F c hc (U.ι ≫ f)
    have := hg
    have := hqc
    have := hqs
    exact ⟨Opposite.op i, ⟨Scheme.FinitePresentationDescent.Model.ofOverIso g e⟩⟩
  have htop : P ⊤ := by
    refine compact_open_induction_on (X := X) ⊤ (by simpa using isCompact_univ) ?_ ?_
    · have : IsAffine (⊥ : X.Opens).toScheme := isAffineOpen_bot X
      exact haff ⊥
    · intro U hU V ih
      obtain ⟨i, ⟨M⟩⟩ := ih
      have : IsAffine V.1.toScheme := V.2
      obtain ⟨j, ⟨N⟩⟩ := haff V.1
      let k := IsCofiltered.min i j
      let q : k ⟶ i := IsCofiltered.minToLeft i j
      let r : k ⟶ j := IsCofiltered.minToRight i j
      let M' := M.rebase D C i (Over.mk q)
      let N' := N.rebase D C j (Over.mk r)
      have hUV : IsCompact ((U ⊓ V.1 : X.Opens) : Set X) :=
        hU.inter_of_isOpen V.2.isCompact U.isOpen V.1.isOpen
      have : CompactSpace (U ⊓ V.1).toScheme := isCompact_iff_compactSpace.mp hUV
      let 𝒰 := Scheme.FinitePresentationDescent.supOpenCover U V.1
      let p : ∀ b : Bool, (U ⊓ V.1).toScheme ⟶ 𝒰.X b :=
        Bool.rec (X.homOfLE inf_le_left) (X.homOfLE inf_le_right)
      let t := (U ⊔ V.1).ι ≫ f
      let models : ∀ b : Bool,
          Scheme.FinitePresentationDescent.Model (C.π.app k) (𝒰.f b ≫ t) := by
        intro b
        cases b
        · exact M'.ofIso _ (.refl _) (by simp [𝒰, t,
            Scheme.FinitePresentationDescent.supOpenCover])
        · exact N'.ofIso _ (.refl _) (by simp [𝒰, t,
            Scheme.FinitePresentationDescent.supOpenCover])
      have H : IsPullback (p false) (p true) (𝒰.f false) (𝒰.f true) :=
        isPullback_opens_inf_le le_sup_left le_sup_right
      obtain ⟨l, ⟨L⟩⟩ := Scheme.FinitePresentationDescent.Model.exists_of_binary_cover
        D C hC k 𝒰.X p 𝒰.f (fun x ↦ 𝒰.exists_eq x) H t models
      exact ⟨l.left, ⟨L⟩⟩
  obtain ⟨i, ⟨M⟩⟩ := htop
  let N := M.ofIso f X.topIso.symm (by simp)
  exact ⟨i.unop, N.X, N.f, inferInstance, inferInstance, inferInstance, ⟨N.overIso⟩⟩

/-- A finite diagram of finitely presented schemes over an actual filtered
ring colimit descends to one stage, with a natural isomorphism from its
literal base change to the original diagram and structural maps. -/
lemma Scheme.exists_diagram_model_of_isColimit
    {I : Type u} [Category.{u} I] [IsFiltered I]
    (F : I ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
    {J : Type v} [SmallCategory J] [Finite J] [∀ j k : J, Finite (j ⟶ k)]
    (Z : J ⥤ Scheme.{u}) (t : Z ⟶ (Functor.const J).obj (Spec c.pt))
    [∀ j, LocallyOfFinitePresentation (t.app j)]
    [∀ j, QuasiCompact (t.app j)] [∀ j, QuasiSeparated (t.app j)] :
    ∃ i : I, ∃ G : J ⥤ Over (Spec (F.obj i)),
      (∀ j, LocallyOfFinitePresentation (G.obj j).hom) ∧
      (∀ j, QuasiCompact (G.obj j).hom) ∧ (∀ j, QuasiSeparated (G.obj j).hom) ∧
      Nonempty (G ⋙ Over.pullback (Spec.map (c.ι.app i)) ≅ Over.lift Z t) := by
  classical
  let : Fintype J := Fintype.ofFinite J
  let D : Iᵒᵖ ⥤ Scheme.{u} := F.op ⋙ Scheme.Spec
  let C : Cone D := Scheme.Spec.mapCone c.op
  have hC : IsLimit C := isLimitOfPreserves Scheme.Spec hc.op
  have (i : Iᵒᵖ) : IsAffine (D.obj i) :=
    inferInstanceAs (IsAffine (Spec (F.obj i.unop)))
  choose i Xi fi hfp hqc hqs he using fun j ↦
    Scheme.exists_model_of_isColimit F c hc (t.app j)
  obtain ⟨k, hk⟩ := IsFiltered.sup_objs_exists (Finset.univ.image i)
  let q (j : J) : i j ⟶ k := (hk (Finset.mem_image.mpr ⟨j, by simp, rfl⟩)).some
  have (j : J) : LocallyOfFinitePresentation (fi j) := hfp j
  have (j : J) : QuasiCompact (fi j) := hqc j
  have (j : J) : QuasiSeparated (fi j) := hqs j
  let M (j : J) : Scheme.FinitePresentationDescent.Model (C.π.app (Opposite.op k)) (t.app j) :=
    (Scheme.FinitePresentationDescent.Model.ofOverIso (fi j) (Classical.choice (he j))).rebase
      D C (Opposite.op (i j)) (Over.mk (q j).op)
  obtain ⟨l, G, hGfp, hGqc, hGqs, e⟩ :=
    Scheme.FinitePresentationDescent.Model.exists_diagram D C hC (Opposite.op k) Z t M
  exact ⟨l.left.unop, G, hGfp, hGqc, hGqs, e⟩

end AlgebraicGeometry
