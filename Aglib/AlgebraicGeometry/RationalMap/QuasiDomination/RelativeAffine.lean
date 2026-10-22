/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.QuasiAffine.AffineBaseChange
public import Aglib.AlgebraicGeometry.RationalMap.QuasiDomination.QuasiAffineSequence

/-!
# Relative quasi-affine extension from an affine source

A concrete immersion into an affine morphism becomes absolutely quasi-affine
over the affine source. Apply the one-open sequence construction to the actual
pullback target over the source's spectrum of global sections. Canonical
pullback isomorphisms then transport its literal closed graph back to the
original relative product. The base itself need not be affine.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.QuasiDomination

/-- A prescribed partial map to a concrete relative quasi-affine target over
an arbitrary base extends after an admissible sequence on its affine source. -/
theorem exists_relative_quasiDomination_of_isAffine
    {X Y P S : Scheme.{u}} [IsNoetherian X] [IsAffine X]
    (U : X.Opens) (p : X ⟶ S) (e : Y ⟶ P) (a : P ⟶ S)
    [IsImmersion e] [IsAffineHom a] [QuasiCompact (e ≫ a)]
    [LocallyOfFiniteType (e ≫ a)]
    (g : U.toScheme ⟶ Y) (hg : g ≫ (e ≫ a) = U.ι ≫ p) :
    ∃ (B : Scheme.{u}) (β : B ⟶ X) (D : B.Opens)
      (h : D.toScheme ⟶ Y) (j : U.toScheme ⟶ D.toScheme)
      (hw : D.ι ≫ β ≫ p = h ≫ (e ≫ a)),
      Blowup.AdmissibleSequence U β ∧ IsProper β ∧ IsIso (β ∣_ U) ∧
      Dense (D : Set B) ∧ IsSchemeTheoreticallyDominant j ∧
      j ≫ D.ι ≫ β = U.ι ∧ j ≫ h = g ∧
      IsClosedImmersion (pullback.lift D.ι h hw) := by
  let f := e ≫ a
  let Yloc : Scheme.{u} := pullback f p
  let t : Yloc ⟶ X := pullback.snd f p
  let i := X.isoSpec.hom
  let : Yloc.IsQuasiAffine := IsQuasiAffine.pullback_of_immersion_affine e a p
  let gloc : U.toScheme ⟶ Yloc := pullback.lift g U.ι hg
  have hgloc : gloc ≫ (t ≫ i) = U.ι ≫ i := by
    simp only [gloc, t, pullback.lift_snd_assoc]
  obtain ⟨B, β, D, hl, j, hwl, hseq, hβ, hU, hd, hj, hjι, hjh, hgraph⟩ :=
    exists_quasiDomination_sequence_of_isQuasiAffine U i (t ≫ i) gloc hgloc
  let h : D.toScheme ⟶ Y := hl ≫ pullback.fst f p
  have hb : D.ι ≫ β = hl ≫ t := by
    apply (cancel_mono i).mp
    simpa only [Category.assoc] using hwl
  have hw : D.ι ≫ β ≫ p = h ≫ f := by
    calc
      D.ι ≫ β ≫ p = hl ≫ t ≫ p := by rw [← Category.assoc, hb, Category.assoc]
      _ = hl ≫ pullback.fst f p ≫ f := by rw [pullback.condition]
      _ = h ≫ f := by simp only [h, Category.assoc]
  have hjh' : j ≫ h = g := by
    calc
      j ≫ h = (j ≫ hl) ≫ pullback.fst f p := by simp only [h, Category.assoc]
      _ = gloc ≫ pullback.fst f p := by rw [hjh]
      _ = g := pullback.lift_fst _ _ _
  refine ⟨B, β, D, h, j, hw, hseq, hβ, hU, hd, hj, hjι, hjh', ?_⟩
  let K : pullback (β ≫ i) (t ≫ i) ≅ pullback β t :=
    (IsPullback.of_isLimit (pullbackIsPullbackOfCompMono β t i)).isoPullback.symm
  have hK₁ : K.hom ≫ pullback.fst β t = pullback.fst (β ≫ i) (t ≫ i) :=
    (IsPullback.of_isLimit (pullbackIsPullbackOfCompMono β t i)).isoPullback_inv_fst
  have hK₂ : K.hom ≫ pullback.snd β t = pullback.snd (β ≫ i) (t ≫ i) :=
    (IsPullback.of_isLimit (pullbackIsPullbackOfCompMono β t i)).isoPullback_inv_snd
  let L : pullback β t ≅ pullback (β ≫ p) f :=
    pullbackSymmetry β t ≪≫ pullbackLeftPullbackSndIso f p β ≪≫
      pullbackSymmetry f (β ≫ p)
  have hL₁ : L.hom ≫ pullback.fst (β ≫ p) f = pullback.fst β t := by
    simp [L, t, Category.assoc]
  have hL₂ : L.hom ≫ pullback.snd (β ≫ p) f =
      pullback.snd β t ≫ pullback.fst f p := by
    simp [L, t, Category.assoc]
  have hC₁ : K.hom ≫ L.hom ≫ pullback.fst (β ≫ p) f =
      pullback.fst (β ≫ i) (t ≫ i) := by rw [hL₁, hK₁]
  have hC₂ : K.hom ≫ L.hom ≫ pullback.snd (β ≫ p) f =
      pullback.snd (β ≫ i) (t ≫ i) ≫ pullback.fst f p := by
    rw [hL₂, ← Category.assoc, hK₂]
  have htransport : pullback.lift D.ι h hw =
      pullback.lift D.ι hl hwl ≫ K.hom ≫ L.hom := by
    apply pullback.hom_ext
    · simp only [Category.assoc, hC₁, pullback.lift_fst]
    · simp only [Category.assoc, hC₂, pullback.lift_snd, pullback.lift_snd_assoc]
      rfl
  let : IsClosedImmersion (pullback.lift D.ι hl hwl) := hgraph
  rw [htransport]
  infer_instance

end AlgebraicGeometry.Scheme.QuasiDomination
