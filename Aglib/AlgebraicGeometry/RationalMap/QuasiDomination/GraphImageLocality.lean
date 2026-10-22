/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.RationalMap.QuasiDomination.Basic
public import Aglib.AlgebraicGeometry.IdealSheaf.Closed.OpenRestriction

/-!
# Open projection of a single schematic graph image

Local closed graphs with open domains identify with the open restrictions of the
actual schematic image of the original map. Schematic density is inherited from
the original source by open base change, not by arbitrary comparison maps.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u v

namespace AlgebraicGeometry.Scheme.QuasiDomination

/-- A local closed graph containing the original source determines the actual
open restriction of its schematic image. The original source is schematically
dense over the base; no reducedness or nonflat image comparison is used. -/
theorem isPullback_image_of_local_closedGraph
    {T P B T₀ B₀ D : Scheme.{u}}
    (p : P ⟶ B) (γ : T ⟶ P) (j : T ⟶ B) (hγ : γ ≫ p = j)
    [QuasiCompact γ] [QuasiCompact j] [IsSchemeTheoreticallyDominant j]
    (v : B₀ ⟶ B) [IsOpenImmersion v]
    (t : T₀ ⟶ T) (j₀ : T₀ ⟶ B₀) (H : IsPullback j₀ t v j)
    (d : D ⟶ B₀) [IsOpenImmersion d]
    (c : D ⟶ pullback p v) [IsClosedImmersion c]
    (hc : c ≫ pullback.snd p v = d)
    (r : T₀ ⟶ D) (hr : r ≫ c ≫ pullback.fst p v = t ≫ γ)
    (hrd : r ≫ d = j₀) :
    ∃ k : D ⟶ γ.image, k ≫ γ.imageι = c ≫ pullback.fst p v ∧
      IsPullback d k v (γ.imageι ≫ p) := by
  let : QuasiCompact j₀ := MorphismProperty.of_isPullback H.flip inferInstance
  let : IsSchemeTheoreticallyDominant j₀ :=
    IsSchemeTheoreticallyDominant.of_isPullback H.flip
  have Hr : IsPullback (𝟙 T₀) r j₀ d := by
    apply IsPullback.of_isLimit (c := PullbackCone.mk (𝟙 T₀) r (by simpa using hrd.symm))
    refine PullbackCone.IsLimit.mk _ (fun s => s.fst) ?_ ?_ ?_
    · intro s
      simp
    · intro s
      apply (cancel_mono d).mp
      simpa only [Category.assoc, hrd] using s.condition
    · intro s m hm₁ hm₂
      simpa using hm₁
  let : IsSchemeTheoreticallyDominant r :=
    IsSchemeTheoreticallyDominant.of_isPullback Hr
  have Hγ : IsPullback (r ≫ c) t (pullback.fst p v) γ := by
    have Hout : IsPullback ((r ≫ c) ≫ pullback.snd p v) t v (γ ≫ p) := by
      simpa only [Category.assoc, hc, hrd, hγ] using H
    exact Hout.of_right (by simpa only [Category.assoc] using hr)
      (IsPullback.of_hasPullback p v).flip
  have hker : γ.ker.comap (pullback.fst p v) = c.ker := by
    rw [IdealSheafData.kernel_comap_open_pullback γ (r ≫ c) t
      (pullback.fst p v) Hγ, Hom.ker_comp, r.ker_eq_bot, IdealSheafData.map_bot]
  let k : D ⟶ γ.image := closedTargetLift r γ.imageι
    (c ≫ pullback.fst p v) (t ≫ γ.toImage) (by simpa using hr)
  have hk : k ≫ γ.imageι = c ≫ pullback.fst p v :=
    closedTargetLift_comp r γ.imageι _ _ _
  have Himage : IsPullback c k (pullback.fst p v) γ.imageι :=
    isPullback_of_isClosedImmersion c γ.imageι k (pullback.fst p v) hk.symm
      (by simpa only [Hom.imageι, IdealSheafData.ker_subschemeι] using hker)
  refine ⟨k, hk, ?_⟩
  simpa only [hc] using
    Himage.paste_horiz (IsPullback.of_hasPullback p v).flip

/-- A cover by actual local closed graphs makes the projection from the single
original schematic image an open immersion. The local original sources may be
any specified cartesian representatives. The cover need not be finite. -/
theorem isOpenImmersion_image_projection_of_openCover
    {T P B : Scheme.{u}}
    (p : P ⟶ B) (γ : T ⟶ P) (j : T ⟶ B) (hγ : γ ≫ p = j)
    [QuasiCompact γ] [QuasiCompact j] [IsSchemeTheoreticallyDominant j]
    (C : B.OpenCover.{v})
    (T₀ : C.I₀ → Scheme.{u}) (t : ∀ a, T₀ a ⟶ T)
    (j₀ : ∀ a, T₀ a ⟶ C.X a)
    (H : ∀ a, IsPullback (j₀ a) (t a) (C.f a) j)
    (D : C.I₀ → Scheme.{u}) (d : ∀ a, D a ⟶ C.X a)
    (hd : ∀ a, IsOpenImmersion (d a))
    (c : ∀ a, D a ⟶ pullback p (C.f a))
    (hc : ∀ a, IsClosedImmersion (c a))
    (hcd : ∀ a, c a ≫ pullback.snd p (C.f a) = d a)
    (r : ∀ a, T₀ a ⟶ D a)
    (hr : ∀ a, r a ≫ c a ≫ pullback.fst p (C.f a) = t a ≫ γ)
    (hrd : ∀ a, r a ≫ d a = j₀ a) :
    IsOpenImmersion (γ.imageι ≫ p) := by
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsOpenImmersion) C]
  intro a
  let : IsOpenImmersion (C.f a) := C.map_prop a
  let : IsOpenImmersion (d a) := hd a
  let : IsClosedImmersion (c a) := hc a
  obtain ⟨k, _, Hk⟩ := isPullback_image_of_local_closedGraph p γ j hγ (C.f a)
    (t a) (j₀ a) (H a) (d a) (c a) (hcd a) (r a) (hr a) (hrd a)
  change IsOpenImmersion (pullback.snd (γ.imageι ≫ p) (C.f a))
  rw [← Hk.flip.isoPullback_inv_snd]
  infer_instance

end AlgebraicGeometry.Scheme.QuasiDomination
