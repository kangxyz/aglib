/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.RationalMap.QuasiDomination.Ambient

/-!
# One-open quasi-affine extension with actual blowup provenance

The ambient construction on the top open gives a finite admissible blowup
sequence and a dense partial extension of the prescribed map. The modified
source is its actual pullback along the top-open inclusion, transported only
by the canonical isomorphism. The original open need not be dense: schematic
density is a conclusion of the construction on the modified source.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.QuasiDomination

/-- A quasi-affine partial map extends after an actual admissible blowup
sequence, retaining its literal original map and a closed relative graph. -/
theorem exists_quasiDomination_sequence_of_isQuasiAffine
    {R : Type u} [CommRing R] {X Y : Scheme.{u}} [IsNoetherian X] [Y.IsQuasiAffine]
    (U : X.Opens) (p : X ⟶ Spec (.of R)) (f : Y ⟶ Spec (.of R))
    [LocallyOfFiniteType f] (g : U.toScheme ⟶ Y) (hg : g ≫ f = U.ι ≫ p) :
    ∃ (X' : Scheme.{u}) (β : X' ⟶ X) (D : X'.Opens)
      (h : D.toScheme ⟶ Y) (j : U.toScheme ⟶ D.toScheme)
      (hw : D.ι ≫ β ≫ p = h ≫ f),
      Blowup.AdmissibleSequence U β ∧ IsProper β ∧ IsIso (β ∣_ U) ∧
      Dense (D : Set X') ∧ IsSchemeTheoreticallyDominant j ∧
      j ≫ D.ι ≫ β = U.ι ∧ j ≫ h = g ∧
      IsClosedImmersion (pullback.lift D.ι h hw) := by
  let W : X.Opens := ⊤
  let t := W.ι
  let : IsIso t := by change IsIso X.topIso.hom; infer_instance
  let T := t ⁻¹ᵁ U
  let gT : T.toScheme ⟶ Y := (t ∣_ U) ≫ g
  have hgT : gT ≫ f = T.ι ≫ t ≫ p := by
    simp only [gT, Category.assoc, hg, morphismRestrict_ι_assoc]
    rfl
  obtain ⟨B, β, D, h, j, hw, hseq, hβ, hU, _, hd, _, hj, hjι, hjh, hgraph⟩ :=
    exists_ambient_quasiDomination_of_isQuasiAffine W U p f gT hgT
  let Q : Scheme.{u} := pullback β t
  let b : Q ⟶ B := pullback.fst β t
  let q : Q ⟶ W.toScheme := pullback.snd β t
  let α : Q ⟶ X := q ≫ t
  have hα : α = b ≫ β := pullback.condition.symm
  let : IsProper β := hβ
  let : IsIso (β ∣_ U) := hU
  let : IsIso b := inferInstance
  have hseqα : Blowup.AdmissibleSequence U α := by
    rw [hα]
    exact hseq.iso (asIso b)
  let : IsProper α := by rw [hα]; infer_instance
  let : IsIso (α ∣_ U) := by
    rw [hα, morphismRestrict_comp]
    infer_instance
  let E : (q ⁻¹ᵁ T).toScheme ≅ U.toScheme := asIso (α ∣_ U)
  let J : U.toScheme ⟶ D.toScheme := E.inv ≫ j
  let : IsSchemeTheoreticallyDominant j := hj
  have hJι : J ≫ D.ι ≫ α = U.ι := by
    calc
      J ≫ D.ι ≫ α = E.inv ≫ (j ≫ D.ι) ≫ α := by simp only [J, Category.assoc]
      _ = E.inv ≫ (q ⁻¹ᵁ T).ι ≫ α := by rw [hjι]
      _ = E.inv ≫ (α ∣_ U) ≫ U.ι := by rw [morphismRestrict_ι]; rfl
      _ = U.ι := by simp [E]
  have hJh : J ≫ h = g := by
    calc
      J ≫ h = E.inv ≫ ((q ∣_ T) ≫ (t ∣_ U)) ≫ g := by
        simp only [J, Category.assoc, hjh, gT]
        rfl
      _ = E.inv ≫ (α ∣_ U) ≫ g := by rw [morphismRestrict_comp]
      _ = g := by simp [E]
  have hw' : D.ι ≫ α ≫ p = h ≫ f := by
    simpa only [α, Category.assoc] using hw
  refine ⟨Q, α, D, h, J, hw', hseqα, inferInstance, inferInstance,
    hd, inferInstance, hJι, hJh, ?_⟩
  have hlift {A B C Z : Scheme.{u}} {a a' : A ⟶ Z} {b b' : B ⟶ Z}
      (ha : a = a') (hb : b = b') (i : C ⟶ A) (k : C ⟶ B)
      (v : i ≫ a = k ≫ b) (v' : i ≫ a' = k ≫ b') :
      pullback.lift i k v' = pullback.lift i k v ≫ (pullback.congrHom ha hb).hom := by
    subst a'
    subst b'
    simp
  have hbase : q ≫ t ≫ p = α ≫ p := (Category.assoc q t p).symm
  have htransport : pullback.lift D.ι h hw' =
      pullback.lift D.ι h hw ≫ (pullback.congrHom hbase (rfl : f = f)).hom :=
    hlift hbase rfl D.ι h hw hw'
  let : IsClosedImmersion (pullback.lift D.ι h hw) := hgraph
  rw [htransport]
  infer_instance

end AlgebraicGeometry.Scheme.QuasiDomination
