/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Fiber
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange
public import Mathlib.RingTheory.Etale.Field
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Affine

/-!
# Finite étale points under purely inseparable field extension

FE-05 scratch authoring. These are actual point maps, intended for the fibre
compatibility part of purely inseparable invariance. The category equivalence
of finite étale covers is a separate obligation.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.FiniteEtale.PurelyInseparable

universe u v w

section Algebra

variable (K : Type u) (L : Type v) [Field K] [Field L]
  [Algebra K L] [IsPurelyInseparable K L]
  (A : Type w) [CommRing A] [Algebra K A]
  [Module.Finite K A] [Algebra.FormallyUnramified K A]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The image of a finite unramified algebra in a purely inseparable extension
is contained in the base field. -/
theorem algHom_mem_base (f : A →ₐ[K] L) (a : A) :
    f a ∈ (algebraMap K L).range := by
  let : Module.Finite K f.range :=
    Module.Finite.of_surjective f.rangeRestrict.toLinearMap f.rangeRestrict_surjective
  let : Field f.range := fieldOfFiniteDimensional K f.range
  let : Algebra.FormallyUnramified K f.range :=
    Algebra.FormallyUnramified.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  let : Algebra.IsSeparable K f.range := Algebra.FormallyUnramified.isSeparable K f.range
  have hsep : IsSeparable K (f.rangeRestrict a) := Algebra.IsSeparable.isSeparable K _
  have hmap : IsSeparable K (f.range.val (f.rangeRestrict a)) :=
    IsSeparable.map f.range.val Subtype.val_injective hsep
  exact IsPurelyInseparable.inseparable K (f a) hmap

/-- Every point of a finite unramified algebra over a purely inseparable
extension descends uniquely along the actual field inclusion. -/
theorem existsUnique_algHom (f : A →ₐ[K] L) :
    ∃! g : A →ₐ[K] K, (Algebra.ofId K L).comp g = f := by
  choose g hg using fun a ↦ algHom_mem_base K L A f a
  have inj := (algebraMap K L).injective
  let g' : A →ₐ[K] K :=
    { toFun := g
      map_one' := inj (by rw [hg, map_one, map_one])
      map_mul' a b := inj (by simp only [map_mul, hg])
      map_zero' := inj (by rw [hg, map_zero, map_zero])
      map_add' a b := inj (by simp only [map_add, hg])
      commutes' r := inj (by rw [hg, f.commutes]; rfl) }
  refine ⟨g', ?_, ?_⟩
  · ext a
    exact hg a
  · intro g'' h
    ext a
    apply inj
    exact (AlgHom.congr_fun h a).trans (hg a).symm

/-- Postcomposition with `K → L` is a bijection on finite unramified algebra
points. In particular this applies to finite étale algebras, in every characteristic. -/
theorem algHom_comp_bijective :
    Function.Bijective (fun g : A →ₐ[K] K ↦ (Algebra.ofId K L).comp g) := by
  constructor
  · intro g h e
    ext a
    exact (algebraMap K L).injective (AlgHom.congr_fun e a)
  · intro f
    obtain ⟨g, hg, _⟩ := existsUnique_algHom K L A f
    exact ⟨g, hg⟩

end Algebra

section Scheme

open Opposite AlgebraicGeometry.Scheme.FiniteEtale
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (Fiber baseChange fiberBaseChangeEquiv
  fiberBaseChangeEquiv_left fiberToFinite)

variable (K L : Type u) [Field K] [Field L] [Algebra K L]

/-- Any extension of fields induces an epimorphism of spectra. -/
theorem fieldMap_epi : Epi (Spec.algebraMap K L) :=
  Flat.epi_of_flat_of_surjective _

/-- The actual map on fibres induced by extension of the point's residue field. -/
def extendFiber {X : Scheme.{u}} (x : Spec (CommRingCat.of K) ⟶ X)
    (Y : Scheme.FiniteEtale X) (q : Fiber x Y) : Fiber (Spec.algebraMap K L ≫ x) Y :=
  Over.homMk (Spec.algebraMap K L ≫ q.left) (by simp [Over.w q])

@[simp] theorem extendFiber_left {X : Scheme.{u}} (x : Spec (CommRingCat.of K) ⟶ X)
    (Y : Scheme.FiniteEtale X) (q : Fiber x Y) :
    (extendFiber K L x Y q).left = Spec.algebraMap K L ≫ q.left := rfl

theorem extendFiber_injective {X : Scheme.{u}} (x : Spec (CommRingCat.of K) ⟶ X)
    (Y : Scheme.FiniteEtale X) : Function.Injective (extendFiber K L x Y) := by
  let : Epi (Spec.algebraMap K L) := fieldMap_epi K L
  intro q r h
  apply Over.OverMorphism.ext
  exact (cancel_epi (Spec.algebraMap K L)).mp (congrArg (fun f ↦ f.left) h)

variable [IsPurelyInseparable K L]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A point of a finite étale scheme over a purely inseparable extension is
the scalar extension of a base-field section. The two scheme-map identities
are retained explicitly. -/
theorem exists_section_of_field_point (Y : Scheme.FiniteEtale (Spec (CommRingCat.of K)))
    (q : Fiber (Spec.algebraMap K L) Y) :
    ∃ g : Fiber (𝟙 (Spec (CommRingCat.of K))) Y,
      Spec.algebraMap K L ≫ g.left = q.left := by
  let A := finiteEtaleAlgebraOfCover K Y
  let : IsAffine Y.obj.left := isAffine_of_isAffineHom Y.obj.hom
  let e := affineOverSpecIso K Y.obj
  let q' : (algebraSpecOver K).obj (op (CommAlgCat.of K L)) ⟶
      (algebraSpecOver K).obj (op A.obj) := q ≫ e.inv
  let φ : A →ₐ[K] L := ((algebraSpecOverFullyFaithful K).preimage q').unop.hom
  obtain ⟨g, hg, _⟩ := existsUnique_algHom K L A φ
  let m : (algebraSpecOver K).obj (op (CommAlgCat.of K K)) ⟶ Y.obj :=
    (algebraSpecOver K).map (CommAlgCat.ofHom g).op ≫ e.hom
  have hm : m.left ≫ Y.obj.hom = 𝟙 (Spec (CommRingCat.of K)) := by
    have H := Over.w m
    change m.left ≫ Y.obj.hom = Spec.map (𝟙 (CommRingCat.of K)) at H
    simpa only [Spec.map_id] using H
  refine ⟨Over.homMk m.left hm, ?_⟩
  have H : Spec.map (CommRingCat.ofHom φ.toRingHom) = q.left ≫ e.inv.left :=
    congrArg (fun f ↦ f.left) ((algebraSpecOverFullyFaithful K).map_preimage q')
  change Spec.algebraMap K L ≫
    (Spec.map (CommRingCat.ofHom g.toRingHom) ≫ e.hom.left) = q.left
  rw [← Category.assoc, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom ((Algebra.ofId K L).comp g).toRingHom) ≫
    e.hom.left = q.left
  rw [hg, H, Category.assoc]
  have he : e.inv.left ≫ e.hom.left = 𝟙 _ := congrArg (fun f ↦ f.left) e.inv_hom_id
  rw [he, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Purely inseparable extension preserves each actual finite étale fibre. -/
theorem extendFiber_surjective {X : Scheme.{u}} (x : Spec (CommRingCat.of K) ⟶ X)
    (Y : Scheme.FiniteEtale X) : Function.Surjective (extendFiber K L x Y) := by
  intro q
  let q' := fiberBaseChangeEquiv x (Spec.algebraMap K L) Y q
  obtain ⟨g, hg⟩ := exists_section_of_field_point K L ((baseChange x).obj Y) q'
  have hg' : g.left ≫ pullback.snd Y.obj.hom x = 𝟙 (Spec (CommRingCat.of K)) := Over.w g
  let r : Fiber x Y := Over.homMk (g.left ≫ pullback.fst Y.obj.hom x) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hg']
    exact Category.id_comp x)
  refine ⟨r, ?_⟩
  apply Over.OverMorphism.ext
  change Spec.algebraMap K L ≫ (g.left ≫ pullback.fst Y.obj.hom x) = q.left
  rw [← Category.assoc, hg]
  change (fiberBaseChangeEquiv x (Spec.algebraMap K L) Y q).left ≫
    pullback.fst Y.obj.hom x = q.left
  rw [fiberBaseChangeEquiv_left, pullback.lift_fst]

/-- The fiber equivalence induced by precomposition with `Spec L ⟶ Spec K` for a purely
inseparable extension. -/
def fiberEquiv {X : Scheme.{u}} (x : Spec (CommRingCat.of K) ⟶ X) (Y : Scheme.FiniteEtale X) :
    Fiber x Y ≃ Fiber (Spec.algebraMap K L ≫ x) Y :=
  Equiv.ofBijective (extendFiber K L x Y)
    ⟨extendFiber_injective K L x Y, extendFiber_surjective K L x Y⟩

@[simp] theorem fiberEquiv_apply {X : Scheme.{u}} (x : Spec (CommRingCat.of K) ⟶ X)
    (Y : Scheme.FiniteEtale X) (q : Fiber x Y) :
    fiberEquiv K L x Y q = extendFiber K L x Y q := rfl

/-- The purely inseparable fibre comparison is natural on the existing cover
category and uses precomposition by the actual map `Spec L → Spec K`. -/
def fiberToFiniteIso {X : Scheme.{u}} (x : Spec (CommRingCat.of K) ⟶ X) :
    fiberToFinite x ≅ fiberToFinite (Spec.algebraMap K L ≫ x) :=
  NatIso.ofComponents (fun Y ↦ FintypeCat.equivEquivIso (fiberEquiv K L x Y)) (by
    intro Y Z f
    apply FintypeCat.hom_ext
    intro q
    apply Over.OverMorphism.ext
    exact (Category.assoc _ _ _).symm)

end Scheme

end AlgebraicGeometry.Scheme.FiniteEtale.PurelyInseparable

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 09792f42419357d47b72031b394231458ecff4e2adf944188d28dfe2238a4164.
Definitions, hypotheses and universes are retained modulo native names. -/
