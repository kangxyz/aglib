/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Grassmannian.Representability

/-!
# Maps from arbitrary schemes into the Grassmannian

For a scheme `T` over `Spec R`, `algSpecPoints T := (algSpec R).rightOp ⋙ yoneda.obj T` is its
functor of points on `R`-algebras, `A ↦ Hom_{Spec R}(Spec A, T)`. Maps `T ⟶ X` over `Spec R` are
the natural transformations `algSpecPoints T ⟶ algSpecPoints X` (`algSpecPointsEquiv`): a
transformation `α` gives maps on the affine open cover of `T` which glue (`glueHom`), and a map
from an affine scheme is determined by its restrictions to basic opens.

With `Grassmannian.representableIso`, maps from any scheme `T` over `Spec R` into the
Grassmannian are the natural transformations from `algSpecPoints T` to Mathlib's
`Module.Grassmannian.functor` (`Grassmannian.homEquivNatTrans`). So the Grassmannian represents
`Grassmannian.localFunctor R k n`, the extension of Mathlib's functor to all schemes over
`Spec R` by natural transformations from the affine functor of points,
`T ↦ Hom(algSpecPoints T, Module.Grassmannian.functor k)`, which is a right Kan extension along
`algSpec` (`Grassmannian.localFunctorRepresentableBy`, `Grassmannian.localFunctorIso`). Its
identification with the functor of rank-`k` locally free quotients of `O_T^n` on nonaffine `T`
(Stacks, Tag 089T) is not proved here.

## Main results

- `AlgebraicGeometry.algSpecPointsEquiv T X : (T ⟶ X) ≃ (algSpecPoints T ⟶ algSpecPoints X)`.
- `AlgebraicGeometry.Grassmannian.homEquivNatTrans k n T :
  (T ⟶ schemeOver R k n) ≃ (algSpecPoints T ⟶ Module.Grassmannian.functor k)`, natural in `T`
  (`homEquivNatTrans_comp`).
- `AlgebraicGeometry.Grassmannian.localFunctorRepresentableBy R k n :
  (localFunctor R k n).RepresentableBy (schemeOver R k n)`, with values in `Type (u + 1)`, and
  the equivalent `AlgebraicGeometry.Grassmannian.localFunctorIso R k n :
  yoneda.obj (schemeOver R k n) ⋙ uliftFunctor ≅ localFunctor R k n`.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Opposite Limits

namespace AlgebraicGeometry

variable {R : CommRingCat.{u}}

/-- The functor of points on `R`-algebras of a scheme `T` over `Spec R`:
`A ↦ Hom_{Spec R}(Spec A, T)`. -/
abbrev algSpecPoints (T : Over (Spec R)) : CommAlgCat.{u} R ⥤ Type u :=
  (algSpec R).rightOp ⋙ yoneda.obj T

namespace AlgSpecPoints

variable {T X : Over (Spec R)}

/-- A natural transformation of functors of points commutes with precomposition by any map of
affine schemes over `Spec R`. -/
theorem comp_app (α : algSpecPoints T ⟶ algSpecPoints X) {B C : CommAlgCat.{u} R}
    (u : (algSpec R).obj (op B) ⟶ T) (t : (algSpec R).obj (op C) ⟶ (algSpec R).obj (op B)) :
    t ≫ α.app B u = α.app C (t ≫ u) := by
  obtain ⟨ψ, rfl⟩ : ∃ ψ : B ⟶ C, (algSpec R).map ψ.op = t :=
    ⟨((algSpec R).preimage t).unop, by rw [Quiver.Hom.op_unop, Functor.map_preimage]⟩
  exact (NatTrans.naturality_apply α ψ u).symm

/-- Two maps from an affine scheme over `Spec R` agree if they agree on the basic opens of a
family of elements, one outside each prime. -/
theorem eq_of_locAway_comp_eq {C : CommAlgCat.{u} R} {Y : Over (Spec R)}
    {g g' : (algSpec R).obj (op C) ⟶ Y} (r : PrimeSpectrum C → C) (hr : ∀ p, r p ∉ p.asIdeal)
    (H : ∀ p, (algSpec R).map (Grassmannian.locAway (r p)).op ≫ g =
      (algSpec R).map (Grassmannian.locAway (r p)).op ≫ g') :
    g = g' := by
  have hspan := Grassmannian.span_range_eq_top_of_forall_notMem (A := C) r hr
  apply Over.OverMorphism.ext
  refine Scheme.Cover.hom_ext
    (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of C) r hspan).openCover _ _
    fun p ↦ ?_
  change ((algSpec R).map (Grassmannian.locAway (r p)).op).left ≫ g.left =
    ((algSpec R).map (Grassmannian.locAway (r p)).op).left ≫ g'.left
  rw [← Over.comp_left, ← Over.comp_left, H p]

/-- Near a prime mapping into the image of an open immersion, a map from an affine scheme
factors through it on a basic open. -/
theorem exists_locAway_comp_eq {C : CommAlgCat.{u} R} {V : Over (Spec R)} (j : V ⟶ T)
    [IsOpenImmersion j.left] (v : (algSpec R).obj (op C) ⟶ T) (p : PrimeSpectrum C)
    (hp : v.left p ∈ Set.range j.left) :
    ∃ (r : C) (_ : r ∉ p.asIdeal)
      (a : (algSpec R).obj (op (CommAlgCat.of R (Localization.Away r))) ⟶ V),
      (algSpec R).map (Grassmannian.locAway r).op ≫ v = a ≫ j := by
  obtain ⟨y, hy⟩ := hp
  let W := v.left ⁻¹ᵁ j.left.opensRange
  have hW : IsOpen ((W : Set ((algSpec R).obj (op C)).left) : Set (PrimeSpectrum C)) := W.isOpen
  have hpW : p ∈ ((W : Set ((algSpec R).obj (op C)).left) : Set (PrimeSpectrum C)) := ⟨y, hy⟩
  obtain ⟨_, ⟨r, rfl⟩, hpr, hrW⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := C)).exists_subset_of_mem_open hpW hW
  refine ⟨r, hpr, ?_⟩
  have hrange : Set.range (((algSpec R).map (Grassmannian.locAway r).op).left ≫ v.left) ⊆
      Set.range j.left := by
    rintro _ ⟨z, rfl⟩
    have hz : ((algSpec R).map (Grassmannian.locAway r).op).left z ∈
        (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum C)) := by
      have hmem : (Spec.map (CommRingCat.ofHom (algebraMap (CommRingCat.of C)
          (Localization.Away r)))) z ∈ (Spec.map (CommRingCat.ofHom (algebraMap
            (CommRingCat.of C) (Localization.Away r)))).opensRange := ⟨z, rfl⟩
      rw [Scheme.Hom.opensRange_localizationAway] at hmem
      exact hmem
    obtain ⟨y', hy'⟩ := hrW hz
    exact ⟨y', by rw [Scheme.Hom.comp_apply]; exact hy'⟩
  let a := IsOpenImmersion.lift j.left _ hrange
  have h1 : a ≫ j.left = ((algSpec R).map (Grassmannian.locAway r).op).left ≫ v.left :=
    IsOpenImmersion.lift_fac j.left _ hrange
  refine ⟨Over.homMk a ?_, ?_⟩
  · have h2 : j.left ≫ T.hom = V.hom := Over.w j
    have h3 : v.left ≫ T.hom = ((algSpec R).obj (op C)).hom := Over.w v
    have h4 : ((algSpec R).map (Grassmannian.locAway r).op).left ≫
        ((algSpec R).obj (op C)).hom =
          ((algSpec R).obj (op (CommAlgCat.of R (Localization.Away r)))).hom := Over.w _
    exact ((congrArg (fun t ↦ a ≫ t) h2.symm).trans (Category.assoc _ _ _).symm).trans
      ((congrArg (fun t ↦ t ≫ T.hom) h1).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun t ↦ ((algSpec R).map (Grassmannian.locAway r).op).left ≫ t) h3).trans
            h4)))
  · apply Over.OverMorphism.ext
    exact h1.symm

variable (T) in
/-- A component of the chosen affine open cover of `T.left`, as a scheme over `Spec R`. -/
abbrev coverObj (i : T.left.affineOpenCover.I₀) : Over (Spec R) :=
  Over.mk (T.left.affineOpenCover.f i ≫ T.hom)

/-- The inclusion of a component of the affine open cover. -/
abbrev coverι (i : T.left.affineOpenCover.I₀) : coverObj T i ⟶ T :=
  Over.homMk (T.left.affineOpenCover.f i) rfl

instance (i : T.left.affineOpenCover.I₀) : IsOpenImmersion (coverι i).left :=
  (inferInstance : IsOpenImmersion (T.left.affineOpenCover.f i))

theorem essImage_coverObj (i : T.left.affineOpenCover.I₀) :
    (algSpec R).essImage (coverObj T i) :=
  (essImage_algSpec (G := coverObj T i)).mpr
    (inferInstance : IsAffine (Spec (T.left.affineOpenCover.X i)))

/-- The `R`-algebra whose spectrum is a component of the affine open cover. -/
def coverAlg (i : T.left.affineOpenCover.I₀) : CommAlgCat.{u} R :=
  (essImage_coverObj i).witness.unop

/-- The identification of `Spec (coverAlg i)` with the cover component. -/
def coverIso (i : T.left.affineOpenCover.I₀) :
    (algSpec R).obj (op (coverAlg i)) ≅ coverObj T i :=
  (essImage_coverObj i).getIso

/-- The cover component as a map from the affine scheme `Spec (coverAlg i)`. -/
abbrev coverPt (i : T.left.affineOpenCover.I₀) : (algSpec R).obj (op (coverAlg i)) ⟶ T :=
  (coverIso i).hom ≫ coverι i

/-- Maps out of `T` are determined by their composites with maps from affine schemes. -/
theorem hom_ext_of_algSpec {g₁ g₂ : T ⟶ X}
    (h : ∀ (B : CommAlgCat.{u} R) (u : (algSpec R).obj (op B) ⟶ T), u ≫ g₁ = u ≫ g₂) :
    g₁ = g₂ := by
  apply Over.OverMorphism.ext
  refine Scheme.Cover.hom_ext T.left.affineOpenCover.openCover _ _ fun i ↦ ?_
  have h' := h _ (coverPt i)
  rw [Category.assoc, Category.assoc, cancel_epi] at h'
  exact congrArg CommaMorphism.left h'

variable (α : algSpecPoints T ⟶ algSpecPoints X)

/-- The map on a component of the affine open cover of `T` determined by `α`. -/
def localHom (i : T.left.affineOpenCover.I₀) : coverObj T i ⟶ X :=
  (coverIso i).inv ≫ α.app (coverAlg i) (coverPt i)

theorem comp_localHom {C : CommAlgCat.{u} R} (i : T.left.affineOpenCover.I₀)
    (w : (algSpec R).obj (op C) ⟶ coverObj T i) :
    w ≫ localHom α i = α.app C (w ≫ coverι i) := by
  rw [localHom, ← Category.assoc, comp_app]
  simp only [coverPt, Category.assoc, Iso.inv_hom_id_assoc]

theorem localHom_compat (i j : T.left.affineOpenCover.I₀) :
    pullback.fst (T.left.affineOpenCover.openCover.f i) (T.left.affineOpenCover.openCover.f j) ≫
        (localHom α i).left =
      pullback.snd (T.left.affineOpenCover.openCover.f i)
        (T.left.affineOpenCover.openCover.f j) ≫ (localHom α j).left := by
  let P : Over (Spec R) := Over.mk (pullback.fst (T.left.affineOpenCover.openCover.f i)
    (T.left.affineOpenCover.openCover.f j) ≫ (coverObj T i).hom)
  let fstO : P ⟶ coverObj T i := Over.homMk (pullback.fst _ _) rfl
  let sndO : P ⟶ coverObj T j := Over.homMk (pullback.snd _ _)
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ T.hom) pullback.condition.symm).trans (Category.assoc _ _ _)))
  have hcond : fstO ≫ coverι i = sndO ≫ coverι j := Over.OverMorphism.ext pullback.condition
  have key : fstO ≫ localHom α i = sndO ≫ localHom α j := by
    refine hom_ext_of_algSpec fun C w ↦ ?_
    rw [← Category.assoc, ← Category.assoc, comp_localHom, comp_localHom, Category.assoc,
      Category.assoc, hcond]
  exact congrArg CommaMorphism.left key

/-- The map `T ⟶ X` glued from the maps determined by `α` on the affine open cover of `T`. -/
def glueHom : T ⟶ X :=
  Over.homMk (T.left.affineOpenCover.openCover.glueMorphisms (fun i ↦ (localHom α i).left)
    (localHom_compat α)) (by
      refine Scheme.Cover.hom_ext T.left.affineOpenCover.openCover _ _ fun i ↦ ?_
      exact (Scheme.Cover.ι_glueMorphisms_assoc T.left.affineOpenCover.openCover
        (fun i ↦ (localHom α i).left) (localHom_compat α) i _).trans (Over.w (localHom α i)))

theorem coverι_comp_glueHom (i : T.left.affineOpenCover.I₀) :
    coverι i ≫ glueHom α = localHom α i := by
  apply Over.OverMorphism.ext
  exact Scheme.Cover.ι_glueMorphisms T.left.affineOpenCover.openCover _ (localHom_compat α) i

/-- The glued map induces `α` on points with values in `R`-algebras. -/
theorem comp_glueHom {C : CommAlgCat.{u} R} (v : (algSpec R).obj (op C) ⟶ T) :
    v ≫ glueHom α = α.app C v := by
  have H : ∀ p : PrimeSpectrum C, ∃ (r : C) (_ : r ∉ p.asIdeal),
      (algSpec R).map (Grassmannian.locAway r).op ≫ v ≫ glueHom α =
        (algSpec R).map (Grassmannian.locAway r).op ≫ α.app C v := by
    intro p
    obtain ⟨r, hr, a, ha⟩ := exists_locAway_comp_eq (coverι (T.left.affineOpenCover.idx (v.left p)))
      v p (T.left.affineOpenCover.covers (v.left p))
    refine ⟨r, hr, ?_⟩
    rw [← Category.assoc, ha, Category.assoc, coverι_comp_glueHom, comp_localHom, ← ha, comp_app]
  choose r hr H using H
  exact eq_of_locAway_comp_eq r hr H

end AlgSpecPoints

open AlgSpecPoints in
variable (T X : Over (Spec R)) in
/-- Maps `T ⟶ X` over `Spec R` are the natural transformations between the functors of points on
`R`-algebras: the functor `T ↦ algSpecPoints T` is fully faithful. -/
def algSpecPointsEquiv : (T ⟶ X) ≃ (algSpecPoints T ⟶ algSpecPoints X) where
  toFun g := Functor.whiskerLeft (algSpec R).rightOp (yoneda.map g)
  invFun α := glueHom α
  left_inv g := hom_ext_of_algSpec fun _ v ↦ comp_glueHom _ v
  right_inv α := by
    ext C v
    exact comp_glueHom α v

theorem algSpecPointsEquiv_apply {T X : Over (Spec R)} (g : T ⟶ X) :
    algSpecPointsEquiv T X g = Functor.whiskerLeft (algSpec R).rightOp (yoneda.map g) :=
  rfl

namespace Grassmannian

variable {k n : ℕ} [Module.Grassmannian.BaseChangeMkQFormula.{u, u, u} R (Fin n → R)]

set_option hygiene false in
/-- Mathlib's Grassmannian functor `A ↦ G(k, A ⊗[R] (Fin n → R); A)` on `R`-algebras. -/
local notation "𝐆" => Module.Grassmannian.functor.{u, u, u} (R := R) (M := Fin n → R) k

variable (k n) in
/-- **Maps from any scheme over `Spec R` into the Grassmannian** are the natural transformations
from its functor of points on `R`-algebras to Mathlib's Grassmannian functor. -/
def homEquivNatTrans (T : Over (Spec R)) : (T ⟶ schemeOver R k n) ≃ (algSpecPoints T ⟶ 𝐆) :=
  (algSpecPointsEquiv T (schemeOver R k n)).trans
    { toFun := fun α ↦ α ≫ (representableIso R k n).hom
      invFun := fun β ↦ β ≫ (representableIso R k n).inv
      left_inv := fun α ↦ by dsimp only; rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      right_inv := fun β ↦ by dsimp only; rw [Category.assoc, Iso.inv_hom_id, Category.comp_id] }

theorem homEquivNatTrans_apply (T : Over (Spec R)) (g : T ⟶ schemeOver R k n) :
    homEquivNatTrans k n T g =
      Functor.whiskerLeft (algSpec R).rightOp (yoneda.map g) ≫ (representableIso R k n).hom :=
  rfl

/-- Naturality of `homEquivNatTrans` in the test scheme. -/
theorem homEquivNatTrans_comp {T' T : Over (Spec R)} (t : T' ⟶ T) (g : T ⟶ schemeOver R k n) :
    homEquivNatTrans k n T' (t ≫ g) =
      Functor.whiskerLeft (algSpec R).rightOp (yoneda.map t) ≫ homEquivNatTrans k n T g := by
  rw [homEquivNatTrans_apply, homEquivNatTrans_apply, Functor.map_comp,
    Functor.whiskerLeft_comp, Category.assoc]

variable (R k n) in
/-- The extension of Mathlib's Grassmannian functor from affine schemes to all schemes over
`Spec R`: `T ↦ Hom(algSpecPoints T, Module.Grassmannian.functor k)`. -/
def localFunctor : (Over (Spec R))ᵒᵖ ⥤ Type (u + 1) :=
  (yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj (algSpec R).rightOp).op ⋙ yoneda.obj 𝐆

variable (R k n) in
/-- **The Grassmannian represents the extension of Mathlib's functor to all schemes over
`Spec R`.** -/
def localFunctorIso :
    yoneda.obj (schemeOver R k n) ⋙ uliftFunctor.{u + 1} ≅ localFunctor R k n :=
  NatIso.ofComponents (fun T ↦ (Equiv.ulift.trans (homEquivNatTrans k n T.unop)).toIso)
    fun {T T'} t ↦ by
      ext ⟨g⟩
      exact homEquivNatTrans_comp t.unop g

variable (R k n) in
/-- **The Grassmannian represents the extension of Mathlib's functor to all schemes over
`Spec R`**, as a `Functor.RepresentableBy` with values in `Type (u + 1)`. -/
def localFunctorRepresentableBy : (localFunctor R k n).RepresentableBy (schemeOver R k n) :=
  (Functor.RepresentableBy.equivUliftYonedaIso.{u + 1} _ _).symm (localFunctorIso R k n)

end Grassmannian

end AlgebraicGeometry
