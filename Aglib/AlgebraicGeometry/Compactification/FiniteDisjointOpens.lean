/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.DisjointOpens
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Finite disjoint enlargement of a compactifiable open

Finite induction combines actual compactifications of disjoint open pieces.
The initial compactifiable open supplies the empty induction case, and the
final native image factor supplies schematic density.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A finite disjoint enlargement of a compactifiable open is compactifiable,
with its literal structural map and a schematically dense source. -/
theorem exists_schematicallyDense_compactification_sup_iSup
    {X S : Scheme.{u}} [NoetherianSpace X] (p : X ⟶ S)
    (V : X.Opens) {A : Type u} [Finite A] (W : A → X.Opens)
    (hW : Pairwise (fun a b => Disjoint (W a) (W b)))
    (hV : Disjoint V (⨆ a, W a))
    (C : Compactification (V.ι ≫ p)) (CW : ∀ a, Compactification ((W a).ι ≫ p)) :
    ∃ E : Compactification ((V ⊔ ⨆ a, W a).ι ≫ p),
      IsSchemeTheoreticallyDominant E.j := by
  classical
  let : Fintype A := Fintype.ofFinite A
  let (O : X.Opens) : NoetherianSpace O.toScheme := by
    change NoetherianSpace (O : Set X)
    infer_instance
  have transport (O O' : X.Opens) (h : O = O') :
      Nonempty (Compactification (O.ι ≫ p)) → Nonempty (Compactification (O'.ι ≫ p)) := by
    subst O'
    exact id
  have H (s : Finset A) : Nonempty (Compactification ((V ⊔ s.sup W).ι ≫ p)) := by
    induction s using Finset.induction_on with
    | empty =>
      exact transport _ _ (show V ⊔ (∅ : Finset A).sup W = V by simp).symm ⟨C⟩
    | @insert a s ha ih =>
      obtain ⟨Cs⟩ := ih
      have hd : Disjoint (V ⊔ s.sup W) (W a) := by
        rw [disjoint_sup_left, Finset.disjoint_sup_left]
        refine ⟨hV.mono_right (le_iSup W a), ?_⟩
        intro b hb
        apply hW
        intro hba
        exact ha (hba ▸ hb)
      obtain ⟨E, _⟩ := exists_schematicallyDense_compactification_sup_of_disjoint
        p (V ⊔ s.sup W) (W a) hd Cs (CW a)
      have he : V ⊔ (insert a s).sup W = (V ⊔ s.sup W) ⊔ W a := by
        simp only [Finset.sup_insert, sup_left_comm, sup_comm]
      exact transport _ _ he.symm ⟨E⟩
  have Htop : Nonempty (Compactification ((V ⊔ ⨆ a, W a).ι ≫ p)) := by
    have he : V ⊔ Finset.univ.sup W = V ⊔ ⨆ a, W a := by
      simp only [Finset.sup_eq_iSup, Finset.mem_univ, iSup_pos]
    exact transport _ _ he (H Finset.univ)
  obtain ⟨E⟩ := Htop
  exact ⟨Compactification.ofImmersion _ E.j E.p E.fac, inferInstance⟩

end AlgebraicGeometry.Scheme.Hom
