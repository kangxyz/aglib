/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsion.Colimit
public import Aglib.CategoryTheory.Sites.Torsion.Devissage
public import Aglib.CategoryTheory.Sites.Torsion.ZMod.Sheaf

/-!
# Reduction of torsion-sheaf properties to prime module coefficients

An isomorphism-invariant property stable under short exact extensions and
countable filtered colimits reduces from internal torsion to prime-annihilated
coefficients. At the actual coefficient universe, the prime tests can be
formulated on genuine ZMod-module-valued sheaves with their original underlying
abelian sheaves. Cohomological stability is an application obligation.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory.Sheaf

universe u v w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}]

/-- Local torsion reduces to prime-annihilated sheaves for a property with actual stability. -/
theorem property_of_isTorsion (P : Sheaf J AddCommGrpCat.{w} → Prop)
    (hiso : ∀ {F G : Sheaf J AddCommGrpCat.{w}}, (F ≅ G) → P F → P G)
    (hzero : ∀ F, IsZero F → P F)
    (hprime : ∀ F (p : ℕ), p.Prime → p • 𝟙 F = 0 → P F)
    (hext : ∀ (S : ShortComplex (Sheaf J AddCommGrpCat.{w})), S.ShortExact →
      P S.X₁ → P S.X₃ → P S.X₂)
    (hcolim : ∀ D : ℕ ⥤ Sheaf J AddCommGrpCat.{w}, (∀ n, P (D.obj n)) → P (colimit D))
    (F : Sheaf J AddCommGrpCat.{w}) (hF : IsTorsion F) : P F := by
  apply hiso (factorialAnnihilatorColimitIso F hF)
  apply hcolim (factorialAnnihilatorDiagram F)
  intro n
  exact property_of_prime_annihilators P hzero hprime hext
    ((factorialAnnihilatorDiagram F).obj n) (n + 1).factorial
    (Nat.factorial_pos _) (factorialAnnihilatorDiagram_annihilated F n)

/-- Prime tests on genuine module-valued sheaves retain original abelian coefficients. -/
theorem property_of_prime_module_coefficients [UnivLE.{max u v, w}]
    (P : Sheaf J AddCommGrpCat.{w} → Prop)
    (hiso : ∀ {F G : Sheaf J AddCommGrpCat.{w}}, (F ≅ G) → P F → P G)
    (hzero : ∀ F, IsZero F → P F)
    (hprime : ∀ (p : ℕ), p.Prime → ∀ M : Sheaf J (ModuleCat.{w} (ZMod p)),
      P ((sheafCompose J (forget₂ (ModuleCat.{w} (ZMod p)) AddCommGrpCat.{w})).obj M))
    (hext : ∀ (S : ShortComplex (Sheaf J AddCommGrpCat.{w})), S.ShortExact →
      P S.X₁ → P S.X₃ → P S.X₂)
    (hcolim : ∀ D : ℕ ⥤ Sheaf J AddCommGrpCat.{w}, (∀ n, P (D.obj n)) → P (colimit D))
    (F : Sheaf J AddCommGrpCat.{w}) (hF : IsTorsion F) : P F := by
  apply property_of_isTorsion P hiso hzero ?_ hext hcolim F hF
  intro G p hp hG
  exact hiso (TorsionZMod.sheafUnderlyingIso J p G hG)
    (hprime p hp (TorsionZMod.sheaf J p G hG))

end CategoryTheory.Sheaf
