/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.StrictlyLocal.Splitting

/-! # Splitting at the actual terminal object of the small etale site -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.StrictlyLocal

universe u

variable (R : Type u) [CommRing R]

/-- The actual identity scheme in the original small etale category. -/
abbrev terminalObject : (Spec (.of R)).Etale := Scheme.Etale.mk (𝟙 _)

/-- The identity etale object is terminal in the actual small etale site. -/
def terminalIsTerminal : IsTerminal (terminalObject R) :=
  IsTerminal.ofUniqueHom
    (fun Y => MorphismProperty.Over.homMk Y.hom (Category.comp_id Y.hom))
    (fun Y f => by
      apply MorphismProperty.Over.Hom.ext
      change f.left = Y.hom
      have h := MorphismProperty.Over.w f
      change f.left ≫ 𝟙 (Spec (.of R)) = Y.hom at h
      exact (Category.comp_id (f.left : Y.left ⟶ Spec (.of R))).symm.trans h)

variable [HenselianLocalRing R] [IsSepClosed (IsLocalRing.ResidueField R)]

/-- Every covering sieve of the terminal etale object contains an actual
split arrow. No splitting at other objects is asserted. -/
theorem exists_split_arrow_of_covering_sieve
    (W : Sieve (terminalObject R))
    (hW : W ∈ Scheme.smallEtaleTopology (Spec (.of R)) (terminalObject R)) :
    ∃ (V : (Spec (.of R)).Etale) (f : V ⟶ terminalObject R)
      (s : terminalObject R ⟶ V), W f ∧ s ≫ f = 𝟙 _ := by
  obtain ⟨𝒰, hOver, hEtale, hle⟩ :=
    (Scheme.mem_smallGrothendieckTopology (terminalObject R) W).mp hW
  let := hOver
  have (i : 𝒰.I₀) : Etale (𝒰.X i ↘ Spec (.of R)) := hEtale i
  obtain ⟨i, σ, hσ⟩ := exists_section_of_etale_family R 𝒰.X 𝒰.f
    (fun x => 𝒰.exists_eq x)
  have hstruct : 𝒰.f i = (𝒰.X i ↘ Spec (.of R)) := by
    have h := HomIsOver.comp_over (f := 𝒰.f i) (S := Spec (.of R))
    change 𝒰.f i ≫ 𝟙 (Spec (.of R)) = (𝒰.X i ↘ Spec (.of R)) at h
    exact (Category.comp_id (𝒰.f i : 𝒰.X i ⟶ Spec (.of R))).symm.trans h
  let V := (𝒰.X i).asOverProp (Spec (.of R)) (hEtale i)
  let f : V ⟶ terminalObject R := (𝒰.f i).asOverProp (Spec (.of R))
  let s : terminalObject R ⟶ V := MorphismProperty.Over.homMk σ (by
    change σ ≫ (𝒰.X i ↘ Spec (.of R)) = 𝟙 (Spec (.of R))
    rw [← hstruct]
    exact hσ)
  refine ⟨V, f, s, hle _ _ ⟨i⟩, ?_⟩
  exact (terminalIsTerminal R).hom_ext _ _

/-- The terminal etale object has no proper covering sieve. -/
theorem covering_sieve_eq_top
    (W : Sieve (terminalObject R))
    (hW : W ∈ Scheme.smallEtaleTopology (Spec (.of R)) (terminalObject R)) : W = ⊤ := by
  obtain ⟨V, f, s, hf, hs⟩ := exists_split_arrow_of_covering_sieve R W hW
  apply Sieve.id_mem_iff_eq_top.mp
  simpa only [hs] using W.downward_closed hf s

end AlgebraicGeometry.Scheme.EtaleCohomology.StrictlyLocal
