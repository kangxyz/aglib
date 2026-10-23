/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.AffineSchemeCoverModels
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.FiniteMappedModels
/-! # Actual mapped affine cover models for section descent -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleAffineBasis
universe u v

/-- A finite affine cover of an affine limit, together with maps to original
etale coefficient objects, descends to one covering stage. Actual refinement
maps and both original triangles are retained; no section continuity is assumed. -/
theorem exists_mapped_affine_cover_model
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i, IsAffine (D.obj i)] (i : I) {X : Scheme.{u}} (r : D.obj i ⟶ X)
    {J : Type v} [Finite J] (Y : J → Over c.pt)
    [∀ j, IsAffine (Y j).left] [∀ j, Etale (Y j).hom]
    (hcover : ∀ x : c.pt, ∃ j, ∃ y : (Y j).left, (Y j).hom y = x)
    (U : J → X.Etale) (a : ∀ j, (Y j).left ⟶ (U j).left)
    (ha : ∀ j, a j ≫ (U j).hom = (Y j).hom ≫ (c.π.app i ≫ r)) :
    ∃ (k : I) (q : k ⟶ i) (W : J → Over (D.obj k)),
      (∀ j, IsAffine (W j).left) ∧ (∀ j, Etale (W j).hom) ∧
      (∀ x : D.obj k, ∃ j, ∃ y : (W j).left, (W j).hom y = x) ∧
      ∃ (b : ∀ j, (W j).left ⟶ (U j).left)
        (d : ∀ j, pullback (c.π.app k) (W j).hom ⟶ (Y j).left),
        (∀ j, b j ≫ (U j).hom = (W j).hom ≫ (D.map q ≫ r)) ∧
        (∀ j, d j ≫ (Y j).hom = pullback.fst (c.π.app k) (W j).hom) ∧
        ∀ j, d j ≫ a j = pullback.snd (c.π.app k) (W j).hom ≫ b j := by
  classical
  obtain ⟨k, q, Z, hZ, he, hm, hcov⟩ :=
    exists_affineScheme_cover_model_above D c hc i Y hcover
  have (j : J) : IsAffine (Z j).left := hZ j
  have (j : J) : Etale (Z j).hom := he j
  let e (j : J) := Classical.choice (hm j)
  let e' (j : J) : pullback (c.π.app k) (Z j).hom ⟶ (Y j).left :=
    (pullbackSymmetry (c.π.app k) (Z j).hom).hom ≫ (e j).hom.left
  have he' (j : J) : e' j ≫ (Y j).hom = pullback.fst (c.π.app k) (Z j).hom :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun z ↦ (pullbackSymmetry (c.π.app k) (Z j).hom).hom ≫ z)
        (Over.w (e j).hom)).trans (pullbackSymmetry_hom_comp_snd _ _))
  let r' := D.map q ≫ r
  let a' (j : J) := e' j ≫ a j
  have ha' (j : J) : a' j ≫ (U j).hom =
      pullback.snd (c.π.app k) (Z j).hom ≫ (Z j).hom ≫ r' := by
    change (e' j ≫ a j) ≫ (U j).hom = _
    rw [Category.assoc, ha j, ← Category.assoc, he']
    change pullback.fst (c.π.app k) (Z j).hom ≫ (c.π.app i ≫ r) = _
    calc
      _ = pullback.fst (c.π.app k) (Z j).hom ≫ ((c.π.app k ≫ D.map q) ≫ r) :=
        congrArg (fun z ↦ pullback.fst (c.π.app k) (Z j).hom ≫ (z ≫ r)) (c.w q).symm
      _ = (pullback.fst (c.π.app k) (Z j).hom ≫ c.π.app k) ≫ (D.map q ≫ r) := by
        simp only [Category.assoc]
      _ = (pullback.snd (c.π.app k) (Z j).hom ≫ (Z j).hom) ≫ (D.map q ≫ r) :=
        congrArg (fun z ↦ z ≫ (D.map q ≫ r)) pullback.condition
      _ = _ := Category.assoc _ _ _
  have (j : I) : CompactSpace (D.obj j) := inferInstance
  have (j : I) : QuasiSeparatedSpace (D.obj j) := inferInstance
  have {j k : I} (g : j ⟶ k) : IsAffineHom (D.map g) := inferInstance
  have (j : J) : QuasiCompact (Z j).hom := inferInstance
  have (j : J) : QuasiSeparated (Z j).hom := inferInstance
  obtain ⟨l, hb⟩ := exists_common_maps_to_etale_targets D c hc k r' Z U a' ha'
  choose b₀ hb₀ hlimit₀ using hb
  let b (j : J) : pullback (D.map l.hom) (Z j).hom ⟶ (U j).left := b₀ j
  let π (j : J) : pullback (c.π.app k) (Z j).hom ⟶
      pullback (D.map l.hom) (Z j).hom := (Scheme.baseChangeCone D c k (Z j).hom).π.app l
  have hb (j : J) : b j ≫ (U j).hom =
      pullback.snd (D.map l.hom) (Z j).hom ≫ (Z j).hom ≫ r' := hb₀ j
  have hlimit (j : J) : π j ≫ b j = a' j := hlimit₀ j
  let W (j : J) : Over (D.obj l.left) := Over.mk (pullback.fst (D.map l.hom) (Z j).hom)
  let d₀ (j : J) : pullback (c.π.app l.left) (W j).hom ⟶
      pullback (c.π.app k) (Z j).hom :=
    pullback.lift (pullback.fst (c.π.app l.left) (W j).hom)
      (pullback.snd (c.π.app l.left) (W j).hom ≫ pullback.snd (D.map l.hom) (Z j).hom)
      (by
        rw [← c.w l.hom]
        change pullback.fst (c.π.app l.left) (W j).hom ≫
            (c.π.app l.left ≫ D.map l.hom) =
          (pullback.snd (c.π.app l.left) (W j).hom ≫
            pullback.snd (D.map l.hom) (Z j).hom) ≫ (Z j).hom
        exact (Category.assoc _ _ _).symm.trans
          ((congrArg (fun z ↦ z ≫ D.map l.hom) pullback.condition).trans
            ((Category.assoc _ _ _).trans
              ((congrArg (fun z ↦ pullback.snd (c.π.app l.left) (W j).hom ≫ z)
                pullback.condition).trans (Category.assoc _ _ _).symm))))
  have hd₀ (j : J) : d₀ j ≫ π j =
      pullback.snd (c.π.app l.left) (W j).hom := by
    have hfst : π j ≫
        pullback.fst (D.map l.hom) (Z j).hom =
      pullback.fst (c.π.app k) (Z j).hom ≫ c.π.app l.left :=
      pullback.lift_fst _ _ _
    have hsnd : π j ≫
        pullback.snd (D.map l.hom) (Z j).hom =
      pullback.snd (c.π.app k) (Z j).hom :=
      Over.w ((Over.pullback (Z j).hom).map (((Over.conePost D k).obj c).π.app l))
    apply pullback.hom_ext
    · rw [Category.assoc, hfst, ← Category.assoc]
      exact (congrArg (fun z ↦ z ≫ c.π.app l.left) (pullback.lift_fst _ _ _)).trans
        pullback.condition
    · rw [Category.assoc, hsnd]
      exact pullback.lift_snd _ _ _
  refine ⟨l.left, l.hom ≫ q, W, ?_, ?_, ?_, b, fun j ↦ d₀ j ≫ e' j, ?_, ?_, ?_⟩
  · intro j
    change IsAffine (pullback (D.map l.hom) (Z j).hom)
    infer_instance
  · intro j
    change Etale (pullback.fst (D.map l.hom) (Z j).hom)
    infer_instance
  · intro x
    obtain ⟨j, y, hy⟩ := hcov (D.map l.hom x)
    refine ⟨j, ?_⟩
    have hx : x ∈ Set.range (pullback.fst (D.map l.hom) (Z j).hom) := by
      rw [Scheme.Pullback.range_fst]
      exact ⟨y, hy⟩
    exact hx
  · intro j
    change b j ≫ (U j).hom =
      pullback.fst (D.map l.hom) (Z j).hom ≫ (D.map (l.hom ≫ q) ≫ r)
    apply (hb j).trans
    change pullback.snd (D.map l.hom) (Z j).hom ≫ (Z j).hom ≫ (D.map q ≫ r) = _
    rw [D.map_comp]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z ↦ z ≫ (D.map q ≫ r)) pullback.condition.symm).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun z ↦ pullback.fst (D.map l.hom) (Z j).hom ≫ z)
            (Category.assoc _ _ _).symm)))
  · intro j
    rw [Category.assoc, he']
    exact pullback.lift_fst _ _ _
  · intro j
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun z ↦ d₀ j ≫ z) (hlimit j).symm).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (fun z ↦ z ≫ b j) (hd₀ j))))
end AlgebraicGeometry.Scheme.EtaleAffineBasis
