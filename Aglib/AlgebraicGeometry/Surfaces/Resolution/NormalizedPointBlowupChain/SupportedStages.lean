/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Resolution.NormalizedPointBlowupChain.Stages
public import Aglib.AlgebraicGeometry.Descent.LocalModification.ChainProperness
public import Aglib.AlgebraicGeometry.Morphisms.Proper.BirationalDVR

/-!
# Proper original prefixes and their unchanged opens

Properness of the actual total normalized-point chain supplies properness
of its native prefixes and suffixes. An original nonempty open on which
the total map is an isomorphism is unchanged by every actual prefix.
The section uses the same total inverse, open inclusion and suffix arrow.
No surface, normality, Nagata or cohomology premise is involved.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Blowup.NormalizedPointBlowupChain

/-- The proper total map forces both original factors at every native cut
to be proper. The empty-chain case needs no integrality premise. -/
theorem isProper_toBase_and_fromTop
    {Z X : Scheme.{u}} {f : Z ⟶ X} (c : NormalizedPointBlowupChain f)
    [hNoeth : IsLocallyNoetherian X] [hf : IsProper f]
    (i : Fin (c.length + 1)) :
    IsProper (c.toBase i) ∧ IsProper (c.fromTop i) := by
  revert hNoeth hf i
  induction c with
  | refl X =>
    intro _ _ i
    change IsProper (𝟙 X) ∧ IsProper (𝟙 X)
    exact ⟨inferInstance, inferInstance⟩
  | @cons X Z hX x hx hne g tail ih =>
    intro hNoeth hf i
    let : IsLocallyNoetherian X := hNoeth
    let : IsProper (g ≫ normalizedPointBlowupMap X x hx hne) := hf
    have hp := firstStep_and_tail_isProper_of_proper_chain x hx hne g tail
    let : IsProper (normalizedPointBlowupMap X x hx hne) := hp.1
    let hN : IsLocallyNoetherian (normalizedPointBlowup X x hx hne) :=
      LocallyOfFiniteType.isLocallyNoetherian (normalizedPointBlowupMap X x hx hne)
    change Fin (tail.length + 1 + 1) at i
    induction i using Fin.cases with
    | zero =>
      change IsProper (𝟙 X) ∧ IsProper (g ≫ normalizedPointBlowupMap X x hx hne)
      exact ⟨inferInstance, hf⟩
    | succ i =>
      change IsProper (tail.toBase i ≫ normalizedPointBlowupMap X x hx hne) ∧
        IsProper (tail.fromTop i)
      have ht := @ih hN hp.2 i
      let : IsProper (tail.toBase i) := ht.1
      exact ⟨inferInstance, ht.2⟩

/-- A genuine nonempty original open unchanged by the total proper chain
is unchanged by each original prefix. The inverse is derived from the
same total restriction and the same suffix, not supplied separately. -/
theorem isIso_toBase_restrict
    {Z X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {f : Z ⟶ X} (c : NormalizedPointBlowupChain f) [IsProper f]
    (U : X.Opens) (hUne : Nonempty U) (hU : IsIso (f ∣_ U))
    (i : Fin (c.length + 1)) : IsIso (c.toBase i ∣_ U) := by
  let : IsIntegral Z := c.isIntegral inferInstance
  let : IsIntegral (c.stage i) := (c.«prefix» i).isIntegral inferInstance
  let : IsDominant (c.fromTop i) := (c.suffix i).isDominant inferInstance
  let : IsProper (c.toBase i) := (c.isProper_toBase_and_fromTop i).1
  let : IsIso (f ∣_ U) := hU
  let V := f ⁻¹ᵁ U
  let u : U.toScheme := Classical.choice hUne
  let v : V.toScheme := inv (f ∣_ U) u
  have hVne : (V : Set Z).Nonempty := ⟨v.1, v.2⟩
  let : IsDominant V.ι := Opens.isDominant_ι (V.isOpen.dense hVne)
  let s : U.toScheme ⟶ c.stage i := inv (f ∣_ U) ≫ V.ι ≫ c.fromTop i
  let : IsDominant s := by dsimp only [s]; infer_instance
  apply isIso_restrict_of_dominant_section (c.toBase i) U s
  change (inv (f ∣_ U) ≫ V.ι ≫ c.fromTop i) ≫ c.toBase i = U.ι
  calc
    (inv (f ∣_ U) ≫ V.ι ≫ c.fromTop i) ≫ c.toBase i =
        inv (f ∣_ U) ≫ V.ι ≫ f := by
      rw [Category.assoc, Category.assoc, c.fromTop_toBase i]
    _ = inv (f ∣_ U) ≫ (f ∣_ U) ≫ U.ι :=
      congrArg (fun k => inv (f ∣_ U) ≫ k) (morphismRestrict_ι f U).symm
    _ = U.ι := IsIso.inv_hom_id_assoc (f ∣_ U) U.ι

end AlgebraicGeometry.Scheme.Blowup.NormalizedPointBlowupChain
