/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor.Monoidal.Braided
public import Aglib.CategoryTheory.Monoidal.UnitMultiplication
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Hom.Sections

/-!
# Multiplication by global twist sections as whiskering

A global section `s` of `O(a)` is a morphism `twistingSectionUnitHom s : 𝟙_ ⟶ O(a)` out of
the monoidal unit (`twistingGlobalSectionsUnitHomEquiv`, through the existing
`unitHomGlobalSectionsEquiv`). It multiplies every module `F` by
`unitMultiply (twistingSectionUnitHom s) F = (λ_ F).inv ≫ twistingSectionUnitHom s ▷ F :
F ⟶ O(a) ⊗ F`. On a twist, followed by the tensorator of the twisting functor, this is the
existing multiplication morphism (`twistingMultiplyGlobal_eq_unitMultiply`):

`twistingMultiplyGlobal a b s = (λ_ _).inv ≫ twistingSectionUnitHom s ▷ O(b) ≫ μ_{a,b}`,

so the additive equivalence `twistingGlobalSectionsHomAddEquiv` is whiskering followed by `μ`.
The leaf evaluates sections only in this bridge and in its input
`twistingSectionUnitHom_app_one` (the unit morphism sends `1` to the restricted section). The
outer and inner multiplication laws `twistingMultiplyGlobal_whiskerRight_tensorMap` and
`whiskerLeft_twistingMultiplyGlobal_tensorMap` then follow from the coherence lemmas
`Functor.LaxMonoidal.unitMultiply_μ_whiskerRight` and
`Functor.LaxBraided.whiskerLeft_unitMultiply_μ` applied to the braided twisting functor; the
degree equalities enter only as `eqToHom` with a free proof.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory MonoidalCategory Opposite

namespace AlgebraicGeometry.ProjectiveSpace

open AlgebraicGeometry.Scheme.Modules

variable (R : Type u) [CommRing R] (ι : Type u)

/-- Global sections of `O(a)` are the morphisms out of the monoidal unit. -/
def twistingGlobalSectionsUnitHomEquiv (a : ℤ) :
    Γ(twistingSheaf R ι a, ⊤) ≃ (𝟙_ (ProjectiveSpace R ι).Modules ⟶ twistingSheaf R ι a) :=
  (unitHomGlobalSectionsEquiv (ProjectiveSpace R ι) (twistingSheaf R ι a)).symm

variable {R ι} in
/-- The morphism `𝟙_ ⟶ O(a)` of a global section of `O(a)`. -/
def twistingSectionUnitHom {a : ℤ} (s : Γ(twistingSheaf R ι a, ⊤)) :
    𝟙_ (ProjectiveSpace R ι).Modules ⟶ twistingSheaf R ι a :=
  twistingGlobalSectionsUnitHomEquiv R ι a s

theorem twistingGlobalSectionsUnitHomEquiv_apply (a : ℤ) (s : Γ(twistingSheaf R ι a, ⊤)) :
    twistingGlobalSectionsUnitHomEquiv R ι a s = twistingSectionUnitHom s :=
  rfl

-- The section lemmas of the twists are stated for the `X.ringCatSheaf` spelling of the
-- structure sheaf, which agrees with the module-sheaf spelling only after unfolding; this needs
-- the transparency override, as in the twisting leaves.
set_option backward.isDefEq.respectTransparency false in
/-- The morphism of a global section evaluates the constant `1` to the restricted section. -/
theorem twistingSectionUnitHom_app_one {a : ℤ} (s : Γ(twistingSheaf R ι a, ⊤))
    (V : (ProjectiveSpace R ι).Opens) :
    (twistingSectionUnitHom s).val.app (op V) (1 : Γ(ProjectiveSpace R ι, V)) =
      (twistingSheaf R ι a).val.map (homOfLE (le_top : V ≤ ⊤)).op s := by
  have h := unitHomGlobalSectionsEquiv_symm_app (ProjectiveSpace R ι) (twistingSheaf R ι a) s V 1
  rw [one_smul] at h
  exact h

-- The section lemmas of the twists are stated for the `X.ringCatSheaf` spelling of the
-- structure sheaf, which agrees with the module-sheaf spelling only after unfolding; this needs
-- the transparency override, as in the twisting leaves.
set_option backward.isDefEq.respectTransparency false in
/-- Multiplication by a global section is whiskering of its unit morphism, followed by the
tensorator: `twistingMultiplyGlobal a b s = (λ_ _).inv ≫ σ ▷ O(b) ≫ μ_{a,b}`. -/
theorem twistingMultiplyGlobal_eq_unitMultiply (a b : ℤ) (s : Γ(twistingSheaf R ι a, ⊤)) :
    twistingMultiplyGlobal R ι a b s =
      unitMultiply (twistingSectionUnitHom s) (twistingSheaf R ι b) ≫
        twistingTensorMap R ι a b := by
  ext V t
  change twistingSectionMul R ι a b V ((twistingSheaf R ι a).val.map (homOfLE le_top).op s) t =
    (twistingTensorMap R ι a b).val.app (op V)
      ((twistingSectionUnitHom s ▷ twistingSheaf R ι b).val.app (op V)
        ((λ_ (twistingSheaf R ι b)).inv.val.app (op V) t))
  rw [leftUnitor_inv_moduleTensorSection]
  -- The unit is spelled `𝟙_` in the whiskering and `SheafOfModules.unit` in the section; no
  -- `eqToHom` occurs in this goal.
  erw [whiskerRight_moduleTensorSection]
  rw [twistingSectionUnitHom_app_one, twistingTensorMap_section]

/-- The bridge in the notation of the twisting functor. -/
theorem twistingMultiplyGlobal_eq (a b : ℤ) (s : Γ(twistingSheaf R ι a, ⊤)) :
    twistingMultiplyGlobal R ι a b s =
      (λ_ (twistingSheaf R ι b)).inv ≫ twistingSectionUnitHom s ▷ twistingSheaf R ι b ≫
        Functor.LaxMonoidal.μ (twistingFunctor R ι) ⟨a⟩ ⟨b⟩ :=
  (twistingMultiplyGlobal_eq_unitMultiply R ι a b s).trans (Category.assoc _ _ _)

/-- The additive Hom comparison of global sections is whiskering followed by the tensorator. -/
theorem twistingGlobalSectionsHomAddEquiv_apply_eq_unitMultiply (a b : ℤ)
    (s : Γ(twistingSheaf R ι a, ⊤)) :
    twistingGlobalSectionsHomAddEquiv R ι a b s =
      unitMultiply (twistingSectionUnitHom s) (twistingSheaf R ι b) ≫
        twistingTensorMap R ι a b :=
  twistingMultiplyGlobal_eq_unitMultiply R ι a b s

/-! ### Multiplication on tensor factors, by coherence -/

-- The source of `twistingTensorMap a b` is spelled `(moduleTensorLeftFunctor _ O(a)).obj O(b)`,
-- the monoidal operations produce `O(a) ⊗ O(b)`; rewriting across the two spellings needs the
-- transparency override.
set_option backward.isDefEq.respectTransparency false in
/-- Multiplication by `s` on the outer factor of `O(d) ⊗ O(b)`, followed by twist
multiplication, is twist multiplication followed by multiplication by `s` and the transport
along `a + (d + b) = a + d + b`. -/
theorem twistingMultiplyGlobal_whiskerRight_tensorMap (a d b : ℤ)
    (s : Γ(twistingSheaf R ι a, ⊤)) (h : a + (d + b) = a + d + b) :
    twistingMultiplyGlobal R ι a d s ▷ twistingSheaf R ι b ≫ twistingTensorMap R ι (a + d) b =
      twistingTensorMap R ι d b ≫ twistingMultiplyGlobal R ι a (d + b) s ≫
        eqToHom (congrArg (twistingSheaf R ι) h) := by
  -- The coherence lemma for the monoidal twisting functor, read in the twisting spelling.
  have key : ((unitMultiply (twistingSectionUnitHom s) (twistingSheaf R ι d) ≫
      twistingTensorMap R ι a d) ▷ twistingSheaf R ι b ≫ twistingTensorMap R ι (a + d) b) ≫
        eqToHom (congrArg (twistingSheaf R ι) h.symm) =
      twistingTensorMap R ι d b ≫
        (unitMultiply (twistingSectionUnitHom s) (twistingSheaf R ι (d + b)) ≫
          twistingTensorMap R ι a (d + b)) :=
    (Category.assoc _ _ _).trans
      (Functor.LaxMonoidal.unitMultiply_μ_whiskerRight (twistingFunctor R ι)
        (twistingSectionUnitHom s) ⟨d⟩ ⟨b⟩)
  rw [← twistingMultiplyGlobal_eq_unitMultiply, ← twistingMultiplyGlobal_eq_unitMultiply] at key
  rw [← Category.assoc]
  exact (comp_eqToHom_iff _ _ _).mp key

-- The source of `twistingTensorMap a b` is spelled `(moduleTensorLeftFunctor _ O(a)).obj O(b)`,
-- the monoidal operations produce `O(a) ⊗ O(b)`; rewriting across the two spellings needs the
-- transparency override.
set_option backward.isDefEq.respectTransparency false in
/-- Multiplication by `s` on the inner factor of `O(e) ⊗ O(b)`, followed by twist
multiplication, is twist multiplication followed by multiplication by `s` and the transport
along `a + (e + b) = e + (a + b)`. The proof uses the braiding of the twisting functor. -/
theorem whiskerLeft_twistingMultiplyGlobal_tensorMap (a e b : ℤ)
    (s : Γ(twistingSheaf R ι a, ⊤)) (h : a + (e + b) = e + (a + b)) :
    twistingSheaf R ι e ◁ twistingMultiplyGlobal R ι a b s ≫ twistingTensorMap R ι e (a + b) =
      twistingTensorMap R ι e b ≫ twistingMultiplyGlobal R ι a (e + b) s ≫
        eqToHom (congrArg (twistingSheaf R ι) h) := by
  -- The braided coherence lemma for the twisting functor, read in the twisting spelling.
  have key : twistingSheaf R ι e ◁ (unitMultiply (twistingSectionUnitHom s) (twistingSheaf R ι b) ≫
      twistingTensorMap R ι a b) ≫ twistingTensorMap R ι e (a + b) =
      twistingTensorMap R ι e b ≫
        (unitMultiply (twistingSectionUnitHom s) (twistingSheaf R ι (e + b)) ≫
          twistingTensorMap R ι a (e + b)) ≫ eqToHom (congrArg (twistingSheaf R ι) h) :=
    (Functor.LaxBraided.whiskerLeft_unitMultiply_μ (twistingFunctor R ι)
      (twistingSectionUnitHom s) ⟨b⟩ ⟨e⟩).trans (by rw [Category.assoc]; rfl)
  rw [← twistingMultiplyGlobal_eq_unitMultiply, ← twistingMultiplyGlobal_eq_unitMultiply] at key
  exact key

end AlgebraicGeometry.ProjectiveSpace
