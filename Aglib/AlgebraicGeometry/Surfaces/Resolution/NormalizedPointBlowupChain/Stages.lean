/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Resolution.NormalizedPointBlowupChain

/-!
# The actual stages of a native normalized-point chain

The finite indices select the scheme expressions, centres and arrows already
present in the given chain. Prefix and suffix chains retain their original
composite triangle and exact lengths. No replacement scheme, properness,
embedding or cohomology data is supplied to these accessors.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Blowup.NormalizedPointBlowupChain

/-- The actual scheme at a cut of the prescribed native chain. -/
def stage : {Z X : Scheme.{u}} → {f : Z ⟶ X} →
    (c : NormalizedPointBlowupChain f) → Fin (c.length + 1) → Scheme.{u}
  | _, _, _, .refl X => fun _ => X
  | _, _, _, @NormalizedPointBlowupChain.cons X _ _ _ _ _ _ tail =>
      Fin.cases X (stage tail)

/-- The actual prefix structural arrow, not a chosen comparison morphism. -/
def toBase : {Z X : Scheme.{u}} → {f : Z ⟶ X} →
    (c : NormalizedPointBlowupChain f) → (i : Fin (c.length + 1)) → stage c i ⟶ X
  | _, _, _, .refl X => fun _ => 𝟙 X
  | _, _, _, @NormalizedPointBlowupChain.cons X _ hX x hx hne _ tail =>
      letI := hX
      Fin.cases (𝟙 X) (fun i => toBase tail i ≫ normalizedPointBlowupMap X x hx hne)

/-- The actual suffix arrow from the unchanged original terminal scheme. -/
def fromTop : {Z X : Scheme.{u}} → {f : Z ⟶ X} →
    (c : NormalizedPointBlowupChain f) → (i : Fin (c.length + 1)) → Z ⟶ stage c i
  | _, _, _, .refl X => fun _ => 𝟙 X
  | _, _, _, @NormalizedPointBlowupChain.cons X _ hX x hx hne g tail =>
      letI := hX
      Fin.cases (g ≫ normalizedPointBlowupMap X x hx hne) (fromTop tail)

/-- The original initial segment, built only with the native constructors. -/
def «prefix» : {Z X : Scheme.{u}} → {f : Z ⟶ X} →
    (c : NormalizedPointBlowupChain f) → (i : Fin (c.length + 1)) →
      NormalizedPointBlowupChain (toBase c i)
  | _, _, _, .refl X => fun _ => .refl X
  | _, _, _, @NormalizedPointBlowupChain.cons X _ hX x hx hne _ tail =>
      letI := hX
      Fin.cases (.refl X) (fun i => .cons x hx hne (toBase tail i) («prefix» tail i))

/-- The original final segment; the zero cut returns the given chain itself. -/
def suffix : {Z X : Scheme.{u}} → {f : Z ⟶ X} →
    (c : NormalizedPointBlowupChain f) → (i : Fin (c.length + 1)) →
      NormalizedPointBlowupChain (fromTop c i)
  | _, _, _, .refl X => fun _ => .refl X
  | _, _, _, @NormalizedPointBlowupChain.cons X Z hX x hx hne g tail =>
      letI := hX
      Fin.cases (.cons x hx hne g tail) (suffix tail)

/-- Each cut retains the exact original total structural triangle. -/
theorem fromTop_toBase {Z X : Scheme.{u}} {f : Z ⟶ X}
    (c : NormalizedPointBlowupChain f) (i : Fin (c.length + 1)) :
    fromTop c i ≫ toBase c i = f := by
  revert i
  induction c with
  | refl X => intro i; exact Category.id_comp (𝟙 X)
  | @cons X Z hX x hx hne g tail ih =>
    intro i
    change Fin (tail.length + 1 + 1) at i
    induction i using Fin.cases with
    | zero => exact Category.comp_id _
    | succ i =>
      change fromTop tail i ≫ (toBase tail i ≫ normalizedPointBlowupMap X x hx hne) = _
      rw [← Category.assoc, ih]

/-- The prefix length is precisely the cut index. -/
theorem length_prefix {Z X : Scheme.{u}} {f : Z ⟶ X}
    (c : NormalizedPointBlowupChain f) (i : Fin (c.length + 1)) :
    («prefix» c i).length = i.val := by
  revert i
  induction c with
  | refl X =>
    intro i
    change Fin 1 at i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  | @cons X Z hX x hx hne g tail ih =>
    intro i
    change Fin (tail.length + 1 + 1) at i
    induction i using Fin.cases with
    | zero => rfl
    | succ i =>
      change («prefix» tail i).length + 1 = i.val + 1
      exact congrArg (· + 1) (ih i)

/-- The suffix has exactly the remaining prescribed number of steps. -/
theorem length_suffix {Z X : Scheme.{u}} {f : Z ⟶ X}
    (c : NormalizedPointBlowupChain f) (i : Fin (c.length + 1)) :
    (suffix c i).length = c.length - i.val := by
  revert i
  induction c with
  | refl X =>
    intro i
    change Fin 1 at i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  | @cons X Z hX x hx hne g tail ih =>
    intro i
    change Fin (tail.length + 1 + 1) at i
    induction i using Fin.cases with
    | zero => rfl
    | succ i =>
      change (suffix tail i).length = (tail.length + 1) - (i.val + 1)
      rw [ih, Nat.add_sub_add_right]

/-- The first accessor is the literal original base scheme. -/
theorem stage_zero {Z X : Scheme.{u}} {f : Z ⟶ X}
    (c : NormalizedPointBlowupChain f) : stage c 0 = X := by
  cases c <;> rfl

/-- The last accessor is the literal original terminal scheme. -/
theorem stage_last {Z X : Scheme.{u}} {f : Z ⟶ X}
    (c : NormalizedPointBlowupChain f) : stage c (Fin.last c.length) = Z := by
  induction c with
  | refl X => rfl
  | @cons X Z hX x hx hne g tail ih => exact ih

/-- At the zero cut the prefix is the canonical equality transport. -/
theorem toBase_zero {Z X : Scheme.{u}} {f : Z ⟶ X}
    (c : NormalizedPointBlowupChain f) : toBase c 0 = eqToHom (stage_zero c) := by
  cases c <;> rfl

/-- The suffix at the zero cut is the given original arrow. -/
theorem fromTop_zero {Z X : Scheme.{u}} {f : Z ⟶ X}
    (c : NormalizedPointBlowupChain f) :
    fromTop c 0 ≫ eqToHom (stage_zero c) = f := by
  rw [← toBase_zero]
  exact fromTop_toBase c 0

/-- At the last cut the suffix is only the native endpoint equality transport. -/
theorem fromTop_last {Z X : Scheme.{u}} {f : Z ⟶ X}
    (c : NormalizedPointBlowupChain f) :
    fromTop c (Fin.last c.length) = eqToHom (stage_last c).symm := by
  induction c with
  | refl X => rfl
  | @cons X Z hX x hx hne g tail ih => exact ih

/-- The final prefix retains the original arrow under that same endpoint equality. -/
theorem toBase_last {Z X : Scheme.{u}} {f : Z ⟶ X}
    (c : NormalizedPointBlowupChain f) :
    eqToHom (stage_last c).symm ≫ toBase c (Fin.last c.length) = f := by
  rw [← fromTop_last]
  exact fromTop_toBase c (Fin.last c.length)

/-- Integrality at a prescribed centre is the instance stored by its cons step. -/
theorem stepIntegral : {Z X : Scheme.{u}} → {f : Z ⟶ X} →
    (c : NormalizedPointBlowupChain f) → (i : Fin c.length) →
      IsIntegral (stage c i.castSucc)
  | _, _, _, .refl _ => fun i => Fin.elim0 i
  | _, _, _, @NormalizedPointBlowupChain.cons _ _ hX _ _ _ _ tail =>
      Fin.cases hX (stepIntegral tail)

/-- The original centre stored at the selected native step. -/
def center : {Z X : Scheme.{u}} → {f : Z ⟶ X} →
    (c : NormalizedPointBlowupChain f) → (i : Fin c.length) → stage c i.castSucc
  | _, _, _, .refl _ => fun i => Fin.elim0 i
  | _, _, _, @NormalizedPointBlowupChain.cons _ _ _ x _ _ _ tail =>
      Fin.cases x (center tail)

/-- Closedness is the original centre proof, with no Jacobson premise. -/
theorem center_isClosed : {Z X : Scheme.{u}} → {f : Z ⟶ X} →
    (c : NormalizedPointBlowupChain f) → (i : Fin c.length) →
      IsClosed ({center c i} : Set (stage c i.castSucc))
  | _, _, _, .refl _ => fun i => Fin.elim0 i
  | _, _, _, @NormalizedPointBlowupChain.cons _ _ _ _ hx _ _ tail =>
      Fin.cases hx (center_isClosed tail)

/-- The nongeneric centre proof belongs to the same original integral stage. -/
theorem center_ne_genericPoint : {Z X : Scheme.{u}} → {f : Z ⟶ X} →
    (c : NormalizedPointBlowupChain f) → (i : Fin c.length) →
      letI := stepIntegral c i
      center c i ≠ genericPoint (stage c i.castSucc)
  | _, _, _, .refl _ => fun i => Fin.elim0 i
  | _, _, _, @NormalizedPointBlowupChain.cons _ _ _ _ _ hne _ tail =>
      Fin.cases hne (center_ne_genericPoint tail)

/-- The original one-step composite between consecutive stage expressions. -/
def step : {Z X : Scheme.{u}} → {f : Z ⟶ X} →
    (c : NormalizedPointBlowupChain f) → (i : Fin c.length) →
      stage c i.succ ⟶ stage c i.castSucc
  | _, _, _, .refl _ => fun i => Fin.elim0 i
  | _, _, _, @NormalizedPointBlowupChain.cons X _ hX x hx hne _ tail =>
      letI := hX
      Fin.cases (eqToHom (stage_zero tail) ≫ normalizedPointBlowupMap X x hx hne)
        (step tail)

/-- The next stage is the constructed normalization, not an arbitrary isomorphic model. -/
theorem stage_succ : {Z X : Scheme.{u}} → {f : Z ⟶ X} →
    (c : NormalizedPointBlowupChain f) → (i : Fin c.length) →
      letI := stepIntegral c i
      stage c i.succ = normalizedPointBlowup (stage c i.castSucc) (center c i)
        (center_isClosed c i) (center_ne_genericPoint c i)
  | _, _, _, .refl _ => fun i => Fin.elim0 i
  | _, _, _, @NormalizedPointBlowupChain.cons _ _ _ _ _ _ _ tail =>
      Fin.cases (stage_zero tail) (stage_succ tail)

/-- The one-step arrow is the literal normalized blowdown under only endpoint equality. -/
theorem step_eq_normalizedPointBlowupMap : {Z X : Scheme.{u}} → {f : Z ⟶ X} →
    (c : NormalizedPointBlowupChain f) → (i : Fin c.length) →
      letI := stepIntegral c i
      step c i = eqToHom (stage_succ c i) ≫
        normalizedPointBlowupMap (stage c i.castSucc) (center c i)
          (center_isClosed c i) (center_ne_genericPoint c i)
  | _, _, _, .refl _ => fun i => Fin.elim0 i
  | _, _, _, @NormalizedPointBlowupChain.cons _ _ _ _ _ _ _ tail => by
      apply Fin.cases
      · rfl
      · exact step_eq_normalizedPointBlowupMap tail

/-- Consecutive original prefixes commute with the actual step. -/
theorem step_toBase {Z X : Scheme.{u}} {f : Z ⟶ X}
    (c : NormalizedPointBlowupChain f) (i : Fin c.length) :
    step c i ≫ toBase c i.castSucc = toBase c i.succ := by
  revert i
  induction c with
  | refl X => intro i; exact Fin.elim0 i
  | @cons X Z hX x hx hne g tail ih =>
    intro i
    change Fin (tail.length + 1) at i
    induction i using Fin.cases with
    | zero =>
      change (eqToHom (stage_zero tail) ≫ normalizedPointBlowupMap X x hx hne) ≫ 𝟙 X =
        toBase tail 0 ≫ normalizedPointBlowupMap X x hx hne
      rw [Category.comp_id, toBase_zero]
    | succ i =>
      change step tail i ≫ (toBase tail i.castSucc ≫ normalizedPointBlowupMap X x hx hne) = _
      rw [← Category.assoc, ih]
      rfl

/-- Consecutive original suffixes retain the original structural factorization. -/
theorem fromTop_step {Z X : Scheme.{u}} {f : Z ⟶ X}
    (c : NormalizedPointBlowupChain f) (i : Fin c.length) :
    fromTop c i.succ ≫ step c i = fromTop c i.castSucc := by
  revert i
  induction c with
  | refl X => intro i; exact Fin.elim0 i
  | @cons X Z hX x hx hne g tail ih =>
    intro i
    change Fin (tail.length + 1) at i
    induction i using Fin.cases with
    | zero =>
      change fromTop tail 0 ≫ (eqToHom (stage_zero tail) ≫
        normalizedPointBlowupMap X x hx hne) = g ≫ normalizedPointBlowupMap X x hx hne
      rw [← Category.assoc, fromTop_zero]
    | succ i => exact ih i

/-- The ordinary blowup datum already selected by the actual centre. -/
abbrev ordinaryDatum {Z X : Scheme.{u}} {f : Z ⟶ X}
    (c : NormalizedPointBlowupChain f) (i : Fin c.length) :=
  blowupDatum ((stage c i.castSucc).fromSpecResidueField (center c i)).ker

/-- The original normalization arrow, with only its native endpoint transport. -/
def normalizationMap {Z X : Scheme.{u}} {f : Z ⟶ X}
    (c : NormalizedPointBlowupChain f) (i : Fin c.length) :
    stage c i.succ ⟶ (ordinaryDatum c i).Y := by
  letI := stepIntegral c i
  letI := pointBlowup_isIntegral (stage c i.castSucc) (center c i)
    (center_isClosed c i) (center_ne_genericPoint c i)
  exact eqToHom (stage_succ c i) ≫
    ((ordinaryDatum c i).Y.fromSpecStalk (genericPoint (ordinaryDatum c i).Y)).fromNormalization

/-- The original normalization and ordinary blowdown compose to the selected step. -/
theorem normalizationMap_comp {Z X : Scheme.{u}} {f : Z ⟶ X}
    (c : NormalizedPointBlowupChain f) (i : Fin c.length) :
    normalizationMap c i ≫ (ordinaryDatum c i).map = step c i := by
  let := stepIntegral c i
  rw [step_eq_normalizedPointBlowupMap]
  exact Category.assoc _ _ _

end AlgebraicGeometry.Scheme.Blowup.NormalizedPointBlowupChain
