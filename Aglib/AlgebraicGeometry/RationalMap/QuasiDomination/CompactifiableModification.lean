/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.RationalMap.QuasiDomination.GeneralRelative
public import Aglib.AlgebraicGeometry.RationalMap.QuasiDomination.ReverseExtension

/-!
# A compactifiable modification from a forward closed graph

A model with a proper ambient scheme supplies, by reverse quasi-domination and
actual sequence extension, an open embedding of a modification of the other
model into a proper scheme. This is a sequence-level compactifiability result;
it asserts neither projectivity nor coalescence to one blowup.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.QuasiDomination

/-- The compactifiability consequence of a forward closed graph. The source
is Noetherian, whereas the proper ambient scheme only needs to be locally
Noetherian for properness of its extended sequence. -/
theorem exists_compactifiable_sequence_of_closedGraph
    {X V Y S : Scheme.{u}} [IsNoetherian X] [IsLocallyNoetherian Y]
    (pX : X ⟶ S) [IsSeparated pX] (pY : Y ⟶ S) [IsProper pY]
    (U : X.Opens) (hU : Dense (U : Set X))
    (φ : V ⟶ X) (v : V ⟶ Y) [IsOpenImmersion v] [QuasiCompact v]
    (hφ : φ ≫ pX = v ≫ pY)
    [IsClosedImmersion (pullback.lift φ v hφ)]
    (u : U.toScheme ⟶ V) [IsOpenImmersion u] [QuasiCompact u]
    [IsSchemeTheoreticallyDominant u] (hu : u ≫ φ = U.ι) :
    ∃ (T Yn : Scheme.{u}) (β : T ⟶ X) (δ : Yn ⟶ Y)
      (i : T ⟶ Yn) (t : U.toScheme ⟶ T),
      Blowup.AdmissibleSequence U β ∧
      Blowup.AdmissibleSequence (u ≫ v).opensRange δ ∧
      IsProper β ∧ IsProper δ ∧ IsProper (δ ≫ pY) ∧
      IsOpenImmersion i ∧ IsSchemeTheoreticallyDominant t ∧
      i ≫ δ ≫ pY = β ≫ pX ∧ t ≫ β = U.ι ∧ t ≫ i ≫ δ = u ≫ v := by
  let : IsProper φ := by
    have : IsProper (pullback.lift φ v hφ ≫ pullback.fst pX pY) := inferInstance
    simpa only [pullback.lift_fst] using this
  have huS : u ≫ (v ≫ pY) = U.ι ≫ pX := by
    rw [← hφ, ← Category.assoc, hu]
  obtain ⟨T, β, W, j, ψ, k, wS, hβ, hβp, hβU, hj, hjdense, hk, hkj, hkψ, hc⟩ :=
    exists_relative_quasiDomination_oneOpen pX (v ≫ pY) U hU u huS
  let : IsOpenImmersion j := hj
  let : IsSchemeTheoreticallyDominant k := hk
  let : IsClosedImmersion (pullback.lift j ψ wS) := hc
  obtain ⟨Yn, δ, r, hδ, hr, hopen, hψp, hψ, hcY⟩ :=
    exists_reverse_open_extension U β hβ pX pY φ v hφ u hu j ψ wS k hkj hkψ
  let : IsOpenImmersion r := hopen
  let : IsProper δ := hδ.isProper
  let : IsClosedImmersion (pullback.lift j (ψ ≫ v)
      (wS.trans (Category.assoc ψ v pY).symm)) := hcY
  let : IsProper j := by
    have : IsProper (pullback.lift j (ψ ≫ v)
        (wS.trans (Category.assoc ψ v pY).symm) ≫
        pullback.fst (β ≫ pX) pY) := inferInstance
    simpa only [pullback.lift_fst] using this
  let : IsDominant j := ⟨hjdense⟩
  let : IsIso j :=
    (isIso_iff_isOpenImmersion_and_surjective j).mpr ⟨inferInstance, inferInstance⟩
  let i := inv j ≫ r
  let t := k ≫ j
  have hrbase : r ≫ δ ≫ pY = j ≫ β ≫ pX := by
    calc
      r ≫ δ ≫ pY = (ψ ≫ v) ≫ pY := by rw [← Category.assoc, hr.w]
      _ = j ≫ β ≫ pX := (Category.assoc ψ v pY).trans wS.symm
  have hibase : i ≫ δ ≫ pY = β ≫ pX := by
    simp only [i, Category.assoc, hrbase, IsIso.inv_hom_id_assoc]
  have hti : t ≫ i ≫ δ = u ≫ v := by
    calc
      t ≫ i ≫ δ = k ≫ r ≫ δ := by simp only [t, i, Category.assoc,
        IsIso.hom_inv_id_assoc]
      _ = k ≫ ψ ≫ v := by
        simpa only [Category.assoc] using congrArg (fun z ↦ k ≫ z) hr.w
      _ = u ≫ v := by rw [← Category.assoc, hkψ]
  exact ⟨T, Yn, β, δ, i, t, hβ, hδ, hβp, inferInstance, inferInstance,
    inferInstance, inferInstance, hibase, hkj, hti⟩

end AlgebraicGeometry.Scheme.QuasiDomination
