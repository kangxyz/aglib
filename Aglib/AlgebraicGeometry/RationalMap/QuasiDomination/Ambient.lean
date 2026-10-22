/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.QuasiAffine.FiniteType
public import Aglib.AlgebraicGeometry.ProjectiveSpace.FromSections.AffineSpace
public import Aglib.AlgebraicGeometry.RationalMap.ProjectiveExtension.Ambient
public import Aglib.AlgebraicGeometry.RationalMap.QuasiDomination.ImmersionExtension

/-!
# Quasi-affine partial maps over an ambient open

Actual ambient coordinate centres preserve the whole protected ambient open.
The resulting partial map and closed graph live over the inverse image of
the chosen ambient open. Schematic density is asserted only there. Global
closedness in the larger product requires the separate supported-graph
argument; it is not a conclusion of this theorem.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProjectiveSpace.FromSections

universe u

namespace AlgebraicGeometry.Scheme.QuasiDomination

/-- Quasi-affine quasi-domination local to an ambient open, with an actual
proper ambient morphism unchanged on the entire protected open. -/
theorem exists_ambient_quasiDomination_of_isQuasiAffine {R : Type u} [CommRing R]
    {X Y : Scheme.{u}} [IsNoetherian X] [Y.IsQuasiAffine]
    (W V : X.Opens) (p : X ⟶ Spec (.of R)) (f : Y ⟶ Spec (.of R))
    [LocallyOfFiniteType f] (g : (W.ι ⁻¹ᵁ V).toScheme ⟶ Y)
    (hg : g ≫ f = (W.ι ⁻¹ᵁ V).ι ≫ W.ι ≫ p) :
    ∃ (X' : Scheme.{u}) (β : X' ⟶ X) (D : (pullback β W.ι).Opens)
      (h : D.toScheme ⟶ Y)
      (j : ((pullback.snd β W.ι) ⁻¹ᵁ W.ι ⁻¹ᵁ V).toScheme ⟶ D.toScheme)
      (hw : D.ι ≫ pullback.snd β W.ι ≫ W.ι ≫ p = h ≫ f),
      Blowup.AdmissibleSequence V β ∧ IsProper β ∧ IsIso (β ∣_ V) ∧
      (Dense (V : Set X) → Dense ((β ⁻¹ᵁ V : X'.Opens) : Set X')) ∧
      Dense (D : Set ↥(pullback β W.ι : Scheme.{u})) ∧
      IsSchemeTheoreticallyDominant ((pullback.snd β W.ι) ⁻¹ᵁ W.ι ⁻¹ᵁ V).ι ∧
      IsSchemeTheoreticallyDominant j ∧
      j ≫ D.ι = ((pullback.snd β W.ι) ⁻¹ᵁ W.ι ⁻¹ᵁ V).ι ∧
      j ≫ h = ((pullback.snd β W.ι) ∣_ W.ι ⁻¹ᵁ V) ≫ g ∧
      IsClosedImmersion (pullback.lift D.ι h hw) := by
  obtain ⟨I, hI, c, hc, hcf⟩ := exists_projectiveChart_immersion_of_isQuasiAffine f
  let := hI
  let := hc
  let E := standardChartIsoAffineSpace R I
  let a : Y ⟶ AffineSpace I (Spec (.of R)) := c ≫ E.hom
  let e : Y ⟶ ProjectiveSpace R (Option I) :=
    c ≫ (ProjectiveSpace.coordinateOpen R (Option I) none).ι
  have hai : a ≫ affineSpaceInclusion R I = e := by
    dsimp only [a, e, E]
    rw [Category.assoc, standardChartIsoAffineSpace_hom_inclusion]
  have haf : a ≫ AffineSpace I (Spec (.of R)) ↘ Spec (.of R) = f := by
    rw [← affineSpaceInclusion_toSpec, ← Category.assoc, hai]
    exact hcf
  let T := W.ι ⁻¹ᵁ V
  have hga : (g ≫ a) ≫ AffineSpace I (Spec (.of R)) ↘ Spec (.of R) =
      T.ι ≫ W.ι ≫ p := by
    rw [Category.assoc, haf, hg]
  obtain ⟨X', β, F, hseq, hβ, hV, htop, hd, hFp, hF⟩ :=
    RationalCoordinates.exists_ambient_projective_extension W V p
      ((g ≫ a).appTop ∘ AffineSpace.coord (Spec (.of R)))
  let q := pullback.snd β W.ι
  let U := q ⁻¹ᵁ T
  let : IsSchemeTheoreticallyDominant U.ι := hd
  let : QuasiCompact U.ι :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict q T) inferInstance
  let : IsImmersion e := inferInstance
  let g' : U.toScheme ⟶ Y := (q ∣_ T) ≫ g
  have w : U.ι ≫ F = g' ≫ e := by
    have heq := hF.trans (congrArg (fun k ↦ (q ∣_ T) ≫ k)
      (comp_affineSpaceInclusion_of_over (g ≫ a) (T.ι ≫ W.ι ≫ p) hga).symm)
    simpa only [g', Category.assoc, hai] using heq
  let D := immersionExtensionDomain F e
  let h := immersionExtension F e U.ι g' w
  let j := immersionExtensionSource F e U.ι g' w
  have he : e ≫ ProjectiveSpace.toSpec R (Option I) = f := hcf
  have hw : D.ι ≫ q ≫ W.ι ≫ p = h ≫ f := by
    simpa only [hFp, he] using immersionExtension_over F e U.ι g' w
      (ProjectiveSpace.toSpec R (Option I))
  refine ⟨X', β, D, h, j, hw, hseq, hβ, hV, htop,
    immersionExtensionDomain_dense F e U.ι g' w, hd, inferInstance,
    immersionExtensionSource_ι F e U.ι g' w,
    source_immersionExtension F e U.ι g' w, ?_⟩
  let Q := pullback.congrHom hFp he
  have hlift {A B C Z : Scheme.{u}} {a a' : A ⟶ Z} {b b' : B ⟶ Z}
      (ha : a = a') (hb : b = b') (i : C ⟶ A) (k : C ⟶ B)
      (v : i ≫ a = k ≫ b) (v' : i ≫ a' = k ≫ b') :
      pullback.lift i k v' = pullback.lift i k v ≫ (pullback.congrHom ha hb).hom := by
    subst a'
    subst b'
    simp
  have hgraph : pullback.lift D.ι h hw =
      immersionExtensionGraph F e U.ι g' w
        (ProjectiveSpace.toSpec R (Option I)) ≫ Q.hom := by
    exact hlift hFp he D.ι h
      (immersionExtension_over F e U.ι g' w (ProjectiveSpace.toSpec R (Option I))) hw
  rw [hgraph]
  infer_instance

end AlgebraicGeometry.Scheme.QuasiDomination
