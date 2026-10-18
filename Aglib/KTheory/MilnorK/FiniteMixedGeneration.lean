/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.SplitPolynomialGeneration
public import Aglib.FieldTheory.CoprimeIrreducibility
public import Aglib.FieldTheory.FiniteCoprimeSplitting

/-!
# Classwise mixed generation over a finite prime-to-prime extension

For a prime-degree polynomial over a perfect field, each actual Milnor class
becomes a finite signed sum of mixed symbols after a finite coefficient
extension of degree prime to that prime. The extension splits only the finitely
many reduced polynomial witnesses extracted from that class. Coprime degrees
prove that the original polynomial itself remains irreducible.

This is a finite classwise statement. It makes no global degree-gap claim and
constructs neither a special closure nor a presentation-independent norm.
-/

@[expose] public noncomputable section

namespace MilnorK

open Polynomial PolynomialResidue Polynomial.LocalResidue

universe u

/-- Every class of a prime-degree root field has an actual finite mixed
expansion after some finite separable prime-to-prime coefficient extension.
The target polynomial is exactly the coefficient image of the original one,
not an arbitrary lower-degree factor. Perfectness is used only to obtain the
finite Galois splitting overfield of the extracted witnesses. -/
theorem exists_finite_coprime_mixed_expansion {k : Type u} [Field k] [PerfectField k]
    (p : MonicIrreducible k) (hp : p.val.natDegree.Prime)
    (m : ℕ) (x : K (AdjoinRoot p.val) (m + 1)) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L),
      FiniteDimensional k L ∧ Algebra.IsSeparable k L ∧
      p.val.natDegree.Coprime (Module.finrank k L) ∧
      ∃ q : MonicIrreducible L, q.val = p.val.map (algebraMap k L) ∧
        ∃ hq : q.val ∣ p.val.map (algebraMap k L),
          ∃ c : (SymbolTuple L m × (AdjoinRoot q.val)ˣ) →₀ ℤ,
            (c.sum fun ab z => z • symbol (Fin.snoc
              (Units.map (algebraMap L (AdjoinRoot q.val)).toMonoidHom ∘ ab.1) ab.2)) =
                map (m + 1) (adjoinRootMap (algebraMap k L) p.val q.val hq) x := by
  obtain ⟨s, hs, hgen⟩ := exists_finite_reduced_mixed_expansion.{u, u} p m x
  let : Fact p.val.natDegree.Prime := ⟨hp⟩
  obtain ⟨S, hfd, hcop, hsplit⟩ :=
    IntermediateField.exists_coprime_splitting_field_of_finset p.val.natDegree s
      (fun r hr => (hs r hr).1) (fun r hr => (hs r hr).2)
  let := hfd
  let q : MonicIrreducible S := ⟨p.val.map (algebraMap k S),
    p.property.1.map _, p.property.1.irreducible_map_of_natDegree_coprime p.property.2 hcop⟩
  refine ⟨S, inferInstance, inferInstance, hfd, inferInstance, hcop, q, rfl, dvd_rfl, ?_⟩
  exact hgen S (algebraMap k S) q dvd_rfl hsplit

end MilnorK
