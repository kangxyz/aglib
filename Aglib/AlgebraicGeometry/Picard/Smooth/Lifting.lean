/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Formal.ProjectiveLine.Cover
public import Aglib.AlgebraicGeometry.Modules.Invertible.Formal.ProjectiveLine.Thickening
public import Aglib.AlgebraicGeometry.Modules.Invertible.SquareZero.TwoAffine
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.InfinitesimalLifting
public import Aglib.AlgebraicGeometry.Picard.Presheaf
public import Aglib.AlgebraicGeometry.Picard.Tangent.Points

/-!
# Lifting of points of a scheme representing the relative Picard functor

Let `K` be a field, `q : Y ⟶ Spec K` a morphism and `P` a locally Noetherian `K`-scheme
representing the relative Picard functor `T ↦ Pic(Y_T) / Pic(T)` (`relativePicardFunctor q`,
Kleiman, *The Picard scheme*, arXiv:math/0504020v1, Def. 2.2, p. 17) on locally Noetherian test
schemes. If `Y` has an affine morphism to the projective line over some ring, then points of `P`
lift along every surjection `A' → A` of `K`-algebras with `A'` Noetherian and square-zero kernel
(`liftsAlongNoetherianSquareZero_of_relativeRepresentableBy_of_isAffineHom_projectiveP1`).

A point of `P` with values in `A` is the class of a line bundle `L` on `Y_A = Y ×_K Spec A`. The
base change `Y_A ⟶ Y_{A'}` of `Spec A ⟶ Spec A'` (`familySpecOverMap`, the map of the
base-change family `familyScheme q` typed between the literal fibre products) is a closed
immersion with square-zero kernel ideal sheaf (`familySpecOverMap_ker_sq`), and `Y_{A'}` is
covered by the two affine inverse images of the charts of the projective line, with affine
intersection (`projectiveLineChartι_cover`). So `L` lifts to `Y_{A'}`
(`exists_lineBundle_lift_twoAffine_of_square_zero`), and its class is the lifted point. This
replaces the truncated exponential sequence and the vanishing of `H^2` in the proof of Kleiman,
Prop. 5.19, p. 47; no Artinian condition on the test rings is needed.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Invertible

namespace AlgebraicGeometry.Scheme

-- Base change of `IsAffineHom` is synthesized with relaxed type transparency, as in Mathlib's
-- `AlgebraicGeometry/Morphisms/Affine.lean`.
set_option backward.isDefEq.respectTransparency.types false in
/-- The projection `X_{A'} ⟶ X` is affine. -/
theorem isAffineHom_pullback_fst_specOver {k : Type u} [CommRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) (A' : Type u) [CommRing A'] [Algebra k A'] :
    IsAffineHom (pullback.fst p (specOver k A').hom) :=
  MorphismProperty.pullback_fst _ _ (inferInstance : IsAffineHom (Spec.algebraMap k A'))

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.RelativePicard

section FamilyMap

variable {k : Type u} [CommRing k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
  {A' A : Type u} [CommRing A'] [CommRing A] [Algebra k A'] [Algebra k A]

/-- The base change `X_A ⟶ X_{A'}` of `Spec g : Spec A ⟶ Spec A'`, the map of the base-change
family `familyScheme p`, typed between the literal fibre products. -/
def familySpecOverMap (g : A' →ₐ[k] A) :
    pullback p (specOver k A).hom ⟶ pullback p (specOver k A').hom :=
  (familyScheme p).map (specOverMap g)

theorem familySpecOverMap_eq (g : A' →ₐ[k] A) :
    familySpecOverMap p g = (familyScheme p).map (specOverMap g) :=
  rfl

/-- The base change `X_A ⟶ X_{A'}` of `Spec g` is a pullback of `Spec g`. -/
theorem familySpecOverMap_isPullback (g : A' →ₐ[k] A) :
    IsPullback (familySpecOverMap p g) (pullback.snd p (specOver k A).hom)
      (pullback.snd p (specOver k A').hom) (Spec.map (CommRingCat.ofHom g.toRingHom)) := by
  have h1 : familySpecOverMap p g ≫ pullback.snd p (specOver k A').hom =
      pullback.snd p (specOver k A).hom ≫ Spec.map (CommRingCat.ofHom g.toRingHom) :=
    familyScheme_map_snd p (specOverMap g)
  have h2 : familySpecOverMap p g ≫ pullback.fst p (specOver k A').hom =
      pullback.fst p (specOver k A).hom :=
    familyScheme_map_fst p (specOverMap g)
  have hs : Spec.map (CommRingCat.ofHom g.toRingHom) ≫ (specOver k A').hom =
      (specOver k A).hom := Spec.map_algHom_algebraMap g
  have H0 : IsPullback (familySpecOverMap p g ≫ pullback.fst p (specOver k A').hom)
      (pullback.snd p (specOver k A).hom) p
      (Spec.map (CommRingCat.ofHom g.toRingHom) ≫ (specOver k A').hom) := by
    rw [h2, hs]
    exact IsPullback.of_hasPullback p (specOver k A).hom
  exact IsPullback.of_right H0 h1 (IsPullback.of_hasPullback p (specOver k A').hom)

/-- For a surjective `g`, the base change `X_A ⟶ X_{A'}` is a closed immersion. -/
theorem familySpecOverMap_isClosedImmersion (g : A' →ₐ[k] A) (hg : Function.Surjective g) :
    IsClosedImmersion (familySpecOverMap p g) := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom g.toRingHom)) :=
    IsClosedImmersion.spec_of_surjective _ hg
  exact MorphismProperty.of_isPullback (familySpecOverMap_isPullback p g).flip inferInstance

/-- For a surjective `g` with square-zero kernel, the base change `X_A ⟶ X_{A'}` has square-zero
kernel ideal sheaf. -/
theorem familySpecOverMap_ker_sq (g : A' →ₐ[k] A) (hg : Function.Surjective g)
    (hK : RingHom.ker g ^ 2 = ⊥) : (familySpecOverMap p g).ker ^ 2 = ⊥ := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom g.toRingHom)) :=
    IsClosedImmersion.spec_of_surjective _ hg
  have hker : (familySpecOverMap p g).ker =
      (Spec.map (CommRingCat.ofHom g.toRingHom)).ker.comap
        (pullback.snd p (specOver k A').hom) := by
    have he := congrArg Scheme.Hom.ker (familySpecOverMap_isPullback p g).isoPullback_hom_fst
    rw [Scheme.Hom.ker_comp_of_isIso] at he
    exact he.symm.trans (Scheme.IdealSheafData.ker_fst_of_isClosedImmersion
      (Spec.map (CommRingCat.ofHom g.toRingHom)) (pullback.snd p (specOver k A').hom))
  rw [hker, ← Scheme.IdealSheafData.comap_pow,
    Scheme.Modules.specMap_kernel_sq (CommRingCat.ofHom g.toRingHom) hK,
    Scheme.IdealSheafData.comap_bot]

end FamilyMap

/-- **Points of a scheme representing the relative Picard functor lift along Noetherian
square-zero thickenings.** Let `K` be a field, `q : Y ⟶ Spec K`, and let `P` represent
`T ↦ Pic(Y_T) / Pic(T)` on locally Noetherian test schemes over `Spec K`. If `Y` has an affine
morphism `ρ` to the projective line over a ring `R₀`, then for every surjection `g : A' → A` of
`K`-algebras with `A'` Noetherian and square-zero kernel, every `A`-point of `P` over `K` lifts
to an `A'`-point. -/
theorem liftsAlongNoetherianSquareZero_of_relativeRepresentableBy_of_isAffineHom_projectiveP1
    {K : Type u} [Field K] {Y : Scheme.{u}} (q : Y ⟶ Spec (.of K))
    {P : LocallyNoetherianOver (Spec (.of K))}
    (R : ((locallyNoetherianOverInclusion (Spec (.of K))).op ⋙ relativePicardFunctor q ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
    {R₀ : Type u} [CommRing R₀] (ρ : Y ⟶ ProjectiveLine.projectiveP1 R₀) [IsAffineHom ρ] :
    P.obj.hom.LiftsAlongNoetherianSquareZero := by
  intro A' A _ _ _ _ _ g hg hK a ha
  have : IsNoetherianRing A := isNoetherianRing_of_surjective A' A g.toRingHom hg
  let t : locallyNoetherianSpecOver K A ⟶ locallyNoetherianSpecOver K A' :=
    locallyNoetherianSpecOverMap g
  let fa : locallyNoetherianSpecOver K A ⟶ P := ObjectProperty.homMk (Over.homMk a ha)
  -- A representative line bundle `L` on `Y_A` of the point `fa`.
  obtain ⟨c, hc⟩ : ∃ c : (familyPicardFunctor q).obj (op (specOver K A)),
      (QuotientAddGroup.mk c : (familyPicardFunctor q).obj (op (specOver K A)) ⧸
        baseImage q (op (specOver K A))) = R.homEquiv fa :=
    QuotientAddGroup.mk_surjective _
  let c' : PicardGroup (pullback q (specOver K A).hom) := c
  obtain ⟨L, hL⟩ := Quotient.exists_rep c'
  -- The thickening `j : Y_A ⟶ Y_{A'}` and the two-affine cover of `Y_{A'}`.
  let j := familySpecOverMap q g
  have : IsClosedImmersion j := familySpecOverMap_isClosedImmersion q g hg
  have hj : j.ker ^ 2 = ⊥ := familySpecOverMap_ker_sq q g hg hK
  let ρ' : pullback q (specOver K A').hom ⟶ ProjectiveLine.projectiveP1 R₀ :=
    pullback.fst _ _ ≫ ρ
  have : IsAffineHom ρ' := by
    have := isAffineHom_pullback_fst_specOver q A'
    exact (inferInstance : IsAffineHom (pullback.fst q (specOver K A').hom ≫ ρ))
  obtain ⟨M, ⟨eM⟩⟩ := exists_lineBundle_lift_twoAffine_of_square_zero j hj
    (projectiveLineChartι ρ' 0) (projectiveLineChartι ρ' 1) (projectiveLineChartι_cover ρ') L
  -- The lifted point.
  obtain ⟨f', hf'R⟩ : ∃ f' : locallyNoetherianSpecOver K A' ⟶ P,
      R.homEquiv f' = (QuotientAddGroup.mk (classOf (pullback q (specOver K A').hom) M) :
        (familyPicardFunctor q).obj (op (specOver K A')) ⧸ baseImage q (op (specOver K A'))) :=
    ⟨R.homEquiv.symm _, R.homEquiv.apply_symm_apply _⟩
  have hcl : pullbackClass j (classOf _ M) = c' := by
    rw [pullbackClass_classOf, ← hL]
    exact Quotient.sound ⟨eM⟩
  have hf' : t ≫ f' = fa := by
    apply R.homEquiv.injective
    rw [homEquiv_comp_apply R t f', hf'R, ← hc]
    exact congrArg (QuotientAddGroup.mk (s := baseImage q (op (specOver K A)))) hcl
  exact ⟨f'.hom.left, Over.w f'.hom, congrArg (fun f => f.hom.left) hf'⟩

end AlgebraicGeometry.Scheme.RelativePicard
