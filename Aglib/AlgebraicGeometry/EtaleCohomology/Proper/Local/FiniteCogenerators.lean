/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.Spectrum
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Local.AnnihilatorProducts

/-! # Genuine module cogenerators from the original finite embedding

The test class consists of genuine module sheaves whose original underlying
coefficient is the annihilator of an actual finite product of finite direct
images of finite constants. This is geometric data, independent of a desired
cohomology comparison. The original finite-product embedding constructs a
monomorphism into this class, preserving its entire index and family.

Global existence of the original finite-product embedding remains a separate
input. No injectivity after forgetting scalars is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper

universe u

attribute [local instance] hasSheafifyLarge TorsionZMod.hasSheafifyStandard

variable (X : Scheme.{u}) (n : ℕ)

/-- The actual geometric test class for genuine module coefficients. Its
definition imposes no cohomological property and allows zero or one modulus. -/
def IsFiniteConstantAnnihilator (M : Reduction.ZModSheaf X n) : Prop :=
  ∃ (I : Type u) (_ : Finite I) (Y : I → Scheme.{u})
    (f : ∀ i, Y i ⟶ X) (A : I → AddCommGrpCat.{u}),
    (∀ i, IsFinite (f i)) ∧ (∀ i, Finite (A i)) ∧
      Nonempty ((Reduction.zmodUnderlying X n).obj M ≅
        Sheaf.annihilator (∏ᶜ fun i => (directImage (f i)).obj
          (ConstantFinite.coefficient (A i) (Y i))) n)

/-- A given original finite constant product embedding yields an actual
genuine module monomorphism into the geometric annihilator test class. The
index, finite schemes, original maps and finite values are retained. -/
theorem exists_mono_finiteConstantAnnihilator
    (M : Reduction.ZModSheaf X n)
    (t : FiniteConstantProductEmbedding ((Reduction.zmodUnderlying X n).obj M)) :
    ∃ (N : Reduction.ZModSheaf X n) (a : M ⟶ N),
      Mono a ∧ IsFiniteConstantAnnihilator X n N := by
  let G : AbelianSheaf.{u, u + 1} X := ∏ᶜ fun i =>
    (directImage (t.morphism i)).obj (ConstantFinite.coefficient (t.value i) (t.source i))
  refine ⟨zmodAnnihilator X n G, zmodAnnihilatorLift X n M G t.map,
    mono_zmodAnnihilatorLift X n M G t.map, ?_⟩
  exact ⟨t.index, t.finite_index, t.source, t.morphism, t.value,
    t.finite_morphism, t.finite_value, ⟨zmodAnnihilatorUnderlyingIso X n G⟩⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper
