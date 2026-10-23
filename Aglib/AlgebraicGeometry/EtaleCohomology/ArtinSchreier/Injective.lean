/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.ArtinSchreier.Constants
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Injectivity of the original prime-field sheaf map

The residue scalar map is injective on every nonempty etale test scheme.
The empty test scheme has the empty covering. Thus the original constant
presheaf map is locally injective, and its actual sheafified map is a mono.
No exact-characteristic assertion is imposed on empty section rings.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

/-- The original residue-constant presheaf map is locally injective on the etale site. -/
theorem primeFieldPresheafMap_isLocallyInjective (X : Scheme.{u}) (p : ℕ)
    (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0) :
    Presheaf.IsLocallyInjective (Scheme.smallEtaleTopology X)
      (primeFieldPresheafMap X p hX) := by
  let : Fact p.Prime := ⟨hp⟩
  constructor
  intro U x y h
  cases isEmpty_or_nonempty U.unop.left with
  | inl he =>
    let Z : PEmpty.{1} → X.Etale := fun i => i.elim
    let f : ∀ i, Z i ⟶ U.unop := fun i => i.elim
    have hc : Sieve.ofArrows Z f ∈ Scheme.smallEtaleTopology X U.unop := by
      rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
      ext t
      exact isEmptyElim t
    apply (Scheme.smallEtaleTopology X).superset_covering ?_ hc
    rw [Sieve.ofArrows, Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    exact fun i => i.elim
  | inr hn =>
    obtain ⟨t⟩ := hn
    let : Nonempty (⊤ : U.unop.left.Opens) := ⟨⟨t, trivial⟩⟩
    let : Nontrivial ((structurePresheaf X).obj U) := by
      change Nontrivial Γ(U.unop.left, ⊤)
      infer_instance
    let r : ZMod p →+* (structurePresheaf X).obj U :=
      ZMod.castHom (ringChar.dvd (primeCast_eq_zero_on_test X p hX U)) _
    have hscalar : r x.down = r y.down := congrArg ULift.down h
    have hxy : x = y := by
      apply ULift.ext
      exact r.injective hscalar
    subst y
    simpa only [Presheaf.equalizerSieve_self_eq_top] using
      (Scheme.smallEtaleTopology X).top_mem U.unop

/-- The actual map from the constant prime-field sheaf to additive sections is mono. -/
theorem primeFieldToStructure_mono (X : Scheme.{u}) (p : ℕ) (hp : p.Prime)
    (hX : (p : Γ(X, ⊤)) = 0) : Mono (primeFieldToStructure X p hX) := by
  let := primeFieldPresheafMap_isLocallyInjective X p hp hX
  have : Presheaf.IsLocallyInjective (Scheme.smallEtaleTopology X)
      (primeFieldToStructure X p hX).hom :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac
      (Scheme.smallEtaleTopology X) (primeFieldPresheafMap X p hX)
      (toSheafify_primeFieldToStructure X p hX)
  exact Sheaf.mono_of_isLocallyInjective _

end AlgebraicGeometry.Scheme.EtaleCohomology
