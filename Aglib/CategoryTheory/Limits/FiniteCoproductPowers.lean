/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Extensive
public import Mathlib.Data.Fin.Tuple.Basic

/-! # Finite powers of finite coproducts

In a finitary pre-extensive category, the actual maps `Pi.map Sigma.ι`
exhibit each finite power of a finite coproduct as the coproduct of the tuple
products. The proof includes the empty power and empty cover index.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits

universe c h w

variable {C : Type c} [Category.{h} C] [HasFiniteProducts C]

/-- Split a nonempty finite product into its head and tail over the terminal
object, using the original product projections. -/
def finProductPullbackCone {n : ℕ} (V : Fin (n + 1) → C) :
    PullbackCone (terminal.from (V 0))
      (terminal.from (∏ᶜ fun k : Fin n => V k.succ)) :=
  PullbackCone.mk (Pi.π V 0) (Pi.lift fun k => Pi.π V k.succ)
    (terminalIsTerminal.hom_ext _ _)

/-- The head/tail product cone is an actual pullback cone. -/
def finProductPullbackConeIsLimit {n : ℕ} (V : Fin (n + 1) → C) :
    IsLimit (finProductPullbackCone V) := by
  refine PullbackCone.IsLimit.mk _
    (fun s => Pi.lift (Fin.cases s.fst (fun k => s.snd ≫ Pi.π _ k))) ?_ ?_ ?_
  · intro s
    simp
  · intro s
    apply Pi.hom_ext
    intro k
    simp
  · intro s m h₁ h₂
    apply Pi.hom_ext
    intro k
    refine Fin.cases ?_ (fun j => ?_) k
    · simpa [finProductPullbackCone] using h₁
    · simpa [finProductPullbackCone] using congrArg (fun f => f ≫ Pi.π _ j) h₂

variable [HasFiniteCoproducts C] [HasPullbacks C] [FinitaryPreExtensive C]
  {ι : Type w} [Finite ι] (U : ι → C)

/-- The canonical tuple-component cofan of a finite power of a coproduct is
colimiting. This is geometric finite distribution, not a cohomology assumption. -/
def isColimitFiniteCoproductPower (n : ℕ) :
    IsColimit (Cofan.mk (∏ᶜ fun _ : Fin n => ∐ U)
      (fun s : Fin n → ι => Pi.map (fun k => Sigma.ι U (s k)))) := by
  induction n with
  | zero =>
      let s₀ : Fin 0 → ι := Fin.elim0
      let f₀ : (∏ᶜ fun k : Fin 0 => U (s₀ k)) ⟶ ∏ᶜ fun _ : Fin 0 => ∐ U :=
        Pi.map fun k => Sigma.ι U (s₀ k)
      letI : ∀ k : Fin 0, IsIso (Sigma.ι U (s₀ k)) := fun k => Fin.elim0 k
      letI : IsIso f₀ := by dsimp [f₀]; infer_instance
      refine Cofan.IsColimit.mk _ (fun s => inv f₀ ≫ s.inj s₀) ?_ ?_
      · intro s i
        obtain rfl : i = s₀ := Subsingleton.elim _ _
        change f₀ ≫ inv f₀ ≫ s.inj s₀ = s.inj s₀
        simp
      · intro s m hm
        apply (cancel_epi f₀).1
        simpa using hm s₀
  | succ n ih =>
      let e : (ι × (Fin n → ι)) ≃ (Fin (n + 1) → ι) :=
        Fin.consEquiv (fun _ : Fin (n + 1) => ι)
      let d : Cofan (fun p : ι × (Fin n → ι) =>
          ∏ᶜ fun k : Fin (n + 1) => U (e p k)) :=
        Cofan.mk
          (f := fun p : ι × (Fin n → ι) =>
            ∏ᶜ fun k : Fin (n + 1) => U (e p k))
          (∏ᶜ fun _ : Fin (n + 1) => ∐ U)
          (fun (p : ι × (Fin n → ι)) =>
            Pi.map (f := fun k : Fin (n + 1) => U (e p k))
              (g := fun _ : Fin (n + 1) => ∐ U)
              (fun k => Sigma.ι U (e p k)))
      have hd : Nonempty (IsColimit d) := by
        refine IsUniversalColimit.nonempty_isColimit_prod_of_pullbackCone
          (FinitaryPreExtensive.isUniversal_finiteCoproducts (coproductIsCoproduct U))
          (FinitaryPreExtensive.isUniversal_finiteCoproducts ih)
          (fun i => terminal.from (U i))
          (fun s : Fin n → ι => terminal.from (∏ᶜ fun k => U (s k)))
          (terminal.from (∐ U)) (terminal.from (∏ᶜ fun _ : Fin n => ∐ U))
          (fun (i : ι) (s : Fin n → ι) =>
            finProductPullbackCone (n := n) (fun k => U (e (i, s) k)))
          (fun (i : ι) (s : Fin n → ι) =>
            finProductPullbackConeIsLimit (n := n) (fun k => U (e (i, s) k)))
          (finProductPullbackCone (fun _ : Fin (n + 1) => ∐ U))
          (finProductPullbackConeIsLimit (fun _ : Fin (n + 1) => ∐ U))
          (d := d) (Iso.refl (∏ᶜ fun _ : Fin (n + 1) => ∐ U)) ?_ ?_ ?_ ?_
        · intro i
          apply terminalIsTerminal.hom_ext
        · intro s
          apply terminalIsTerminal.hom_ext
        · intro i s
          simp [d, e, finProductPullbackCone, Fin.cons]
        · intro i s
          apply Pi.hom_ext
          intro k
          simp [d, e, finProductPullbackCone, Fin.cons]
      exact (Cofan.isColimitEquivOfEquiv (Fin.consEquiv (fun _ : Fin (n + 1) => ι))
        (Cofan.mk (∏ᶜ fun _ : Fin (n + 1) => ∐ U)
          (fun s : Fin (n + 1) → ι => Pi.map fun k => Sigma.ι U (s k)))).symm hd.some

/-- The literal distribution map from tuple products to the power of a finite
coproduct is an isomorphism. -/
instance isIso_finiteCoproductPowerComparison (n : ℕ) :
    IsIso (Sigma.desc (fun s : Fin n → ι => Pi.map (fun k => Sigma.ι U (s k)))) :=
  (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc _).mp ⟨isColimitFiniteCoproductPower U n⟩

end CategoryTheory.Limits
