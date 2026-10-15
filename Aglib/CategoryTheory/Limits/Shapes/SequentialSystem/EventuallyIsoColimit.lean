/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Limits.Shapes.SequentialSystem.IsoColimit
public import Aglib.CategoryTheory.Limits.Shapes.SequentialSystem.TailColimit

/-!
# Original colimit legs of eventually invertible sequences

If the original successor maps are invertible from stage `i` onward, the
original colimit inclusion at `i` is invertible. No condition is imposed on
any earlier transition. The proof uses the tail beginning at `i` itself.

Source: `Quillen/CategoryTheory/Limits/SequentialEventuallyIsoColimit.lean`
from the supplied Quillen archive.
Source SHA-256: `8230116e6ee81bc7fb4ebe699d351ebe224fad7787079daf738a6daa1ca77dd0`.
All declarations are migrated with their original hypotheses and maps.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
namespace CategoryTheory.Limits.SequentialSystem

/-- The actual stage-zero leg is inverse to the successor-inverse comparison. -/
theorem colimit_ι_zero_eq_inv {C : Type u} [Category.{v} C]
    (F : ℕ ⥤ C) [HasColimit F]
    [∀ n, IsIso (F.map (homOfLE (Nat.le_succ n)))] :
    colimit.ι F 0 = (colimitIsoOfSucc F).inv := by
  apply (cancel_mono (colimitIsoOfSucc F).hom).mp
  simp [toZeroIso]

/-- The original stage `i` inclusion is invertible once all successors from `i` are. -/
theorem colimit_ι_isIso_of_tail {C : Type u} [Category.{v} C]
    (F : ℕ ⥤ C) [HasColimit F] (i : ℕ)
    (h : ∀ n, i ≤ n → IsIso (F.map (homOfLE (Nat.le_succ n)))) :
    IsIso (colimit.ι F i) := by
  let G := shiftFunctor i ⋙ F
  let (n : ℕ) : IsIso (G.map (homOfLE (Nat.le_succ n))) :=
    h (i + n) (Nat.le_add_right i n)
  have hzero : IsIso (colimit.ι G 0) := by
    rw [colimit_ι_zero_eq_inv G]
    infer_instance
  have hleg : colimit.ι G 0 ≫ (tailColimitIso F i).hom = colimit.ι F i := by
    simpa only [Nat.add_zero] using tailColimitIso_ι_hom F i 0
  rw [← hleg]
  exact IsIso.comp_isIso' hzero (tailColimitIso F i).isIso_hom

end CategoryTheory.Limits.SequentialSystem
