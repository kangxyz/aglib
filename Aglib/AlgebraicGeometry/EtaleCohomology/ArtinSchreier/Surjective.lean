/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.ArtinSchreier.Frobenius
public import Aglib.AlgebraicGeometry.EtaleCohomology.ArtinSchreier.RootCover
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Etale-local surjectivity of the actual Artin--Schreier map

The original root algebra gives a finite etale surjective cover of every test
scheme on which its prescribed global section has a root. Thus the literal
power-minus-identity map on the actual additive structure sheaf is an
epimorphism whenever the prime is zero in global sections, including for the
empty scheme. No assertion about its constant kernel is needed here.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

/-- Every actual additive section has an Artin--Schreier preimage etale locally. -/
theorem artinSchreierMap_isLocallySurjective (X : Scheme.{u}) (p : ℕ) (hp : p.Prime)
    (hX : (p : Γ(X, ⊤)) = 0) :
    Presheaf.IsLocallySurjective (Scheme.smallEtaleTopology X)
      (artinSchreierMap X p hp hX).hom := by
  constructor
  intro U a
  let a₀ : Γ(U.left, ⊤) := a.down
  have hU : (p : Γ(U.left, ⊤)) = 0 := primeCast_eq_zero_on_test X p hX (op U)
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨Y, f, _, hf, hs, b, hb⟩ := ArtinSchreier.exists_finiteEtale_root U.left p a₀ hU
  let := hf
  let := hs
  let V : X.Etale := Scheme.Etale.mk (f ≫ U.hom)
  let q : V ⟶ U := MorphismProperty.Over.homMk f rfl
  have hc : Sieve.ofArrows (fun _ : PUnit.{1} => V) (fun _ => q) ∈
      Scheme.smallEtaleTopology X U := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    change (⋃ _ : PUnit.{1}, Set.range f) = Set.univ
    simp only [Set.iUnion_const]
    exact Set.range_eq_univ.mpr hs.surj
  apply (Scheme.smallEtaleTopology X).superset_covering ?_ hc
  rw [Sieve.ofArrows, Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
  intro _
  change ∃ t, (artinSchreierMap X p hp hX).hom.app (op V) t =
    (additiveStructurePresheaf X).map q.op a
  refine ⟨ULift.up b, ?_⟩
  apply ULift.ext
  change b ^ p - b = f.appTop.hom a₀
  exact hb

/-- The actual Artin--Schreier endomorphism is an epimorphism of abelian sheaves. -/
theorem artinSchreierMap_epi (X : Scheme.{u}) (p : ℕ) (hp : p.Prime)
    (hX : (p : Γ(X, ⊤)) = 0) : Epi (artinSchreierMap X p hp hX) := by
  let := artinSchreierMap_isLocallySurjective X p hp hX
  exact inferInstance

end AlgebraicGeometry.Scheme.EtaleCohomology
