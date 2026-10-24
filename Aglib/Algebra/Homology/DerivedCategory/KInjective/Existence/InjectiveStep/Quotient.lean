/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.InjectiveStep.Contractible
public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone

/-!
# The actual quotient and cone comparison for the injective step

The quotient is the cokernel of the original natural monomorphism into the
contractible injective complex. The comparison from its mapping cone is a
genuine quasi-isomorphism supplied by the native short-exact-sequence theorem.
The mapping cocone of the quotient projection and its original augmentation
are also constructed. Quasi-isomorphism of that augmentation is a separate
obligation, not an input field or an assertion of this file.
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.IsGrothendieckAbelian

namespace CochainComplex

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

/-- The original contractible embedding as a functor to the arrow category. -/
def injectiveStepArrow : CochainComplex C ℤ ⥤ Arrow (CochainComplex C ℤ) where
  obj K := Arrow.mk (injectiveStepContractibleι K)
  map f := Arrow.homMk f ((injectiveStepContractible C).map f)
    (injectiveStepContractibleι_naturality f)
  map_id K := by
    apply Arrow.hom_ext
    · rfl
    · exact (injectiveStepContractible C).map_id K
  map_comp f g := by
    apply Arrow.hom_ext
    · rfl
    · exact (injectiveStepContractible C).map_comp f g

/-- The actual cokernel functor, with no independent quotient carrier. -/
abbrev injectiveStepQuotient : CochainComplex C ℤ ⥤ CochainComplex C ℤ :=
  injectiveStepArrow C ⋙ coker (CochainComplex C ℤ)

variable {C}

/-- The original quotient projection. -/
abbrev injectiveStepQuotientπ (K : CochainComplex C ℤ) :
    (injectiveStepContractible C).obj K ⟶ (injectiveStepQuotient C).obj K :=
  cokernel.π (injectiveStepContractibleι K)

@[reassoc (attr := simp)]
lemma injectiveStepQuotient_condition (K : CochainComplex C ℤ) :
    injectiveStepContractibleι K ≫ injectiveStepQuotientπ K = 0 :=
  cokernel.condition _

/-- The actual short exact sequence defining the quotient. -/
def injectiveStepShortComplex (K : CochainComplex C ℤ) :
    ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk (injectiveStepContractibleι K) (injectiveStepQuotientπ K)
    (injectiveStepQuotient_condition K)

lemma injectiveStepShortComplex_shortExact (K : CochainComplex C ℤ) :
    (injectiveStepShortComplex K).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)
  mono_f := inferInstanceAs (Mono (injectiveStepContractibleι K))
  epi_g := inferInstanceAs (Epi (cokernel.π (injectiveStepContractibleι K)))

/-- The native cone-to-quotient comparison, with its original projection. -/
def injectiveStepConeComparison (K : CochainComplex C ℤ) :
    mappingCone (injectiveStepContractibleι K) ⟶ (injectiveStepQuotient C).obj K :=
  mappingCone.descShortComplex (injectiveStepShortComplex K)

instance injectiveStepConeComparison_quasiIso (K : CochainComplex C ℤ) :
    QuasiIso (injectiveStepConeComparison K) :=
  mappingCone.quasiIso_descShortComplex (injectiveStepShortComplex_shortExact K)

@[reassoc (attr := simp)]
lemma injectiveStepConeComparison_inr (K : CochainComplex C ℤ) :
    mappingCone.inr (injectiveStepContractibleι K) ≫ injectiveStepConeComparison K =
      injectiveStepQuotientπ K :=
  mappingCone.inr_descShortComplex (injectiveStepShortComplex K)

/-- The next injective-step object is the native mapping cocone of the quotient. -/
abbrev injectiveStepCocone (K : CochainComplex C ℤ) : CochainComplex C ℤ :=
  mappingCocone (injectiveStepQuotientπ K)

/-- The original augmentation into the quotient's mapping cocone. -/
def injectiveStepCoconeι (K : CochainComplex C ℤ) : K ⟶ injectiveStepCocone K :=
  mappingCocone.lift (injectiveStepQuotientπ K) (injectiveStepContractibleι K) 0 (by simp)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma injectiveStepCoconeι_fst (K : CochainComplex C ℤ) :
    injectiveStepCoconeι K ≫ mappingCocone.fst (injectiveStepQuotientπ K) =
      injectiveStepContractibleι K := by
  simp [injectiveStepCoconeι]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma injectiveStepCoconeι_f_fst_f (K : CochainComplex C ℤ) (n : ℤ) :
    (injectiveStepCoconeι K).f n ≫ (mappingCocone.fst (injectiveStepQuotientπ K)).f n =
      (injectiveStepContractibleι K).f n := by
  simp [injectiveStepCoconeι]

set_option backward.isDefEq.respectTransparency false in
instance injectiveStepCoconeι_mono_f (K : CochainComplex C ℤ) (n : ℤ) :
    Mono ((injectiveStepCoconeι K).f n) :=
  mono_of_mono_fac (injectiveStepCoconeι_f_fst_f K n)

instance injectiveStepCoconeι_mono (K : CochainComplex C ℤ) :
    Mono (injectiveStepCoconeι K) :=
  HomologicalComplex.mono_of_mono_f _ inferInstance

set_option backward.isDefEq.respectTransparency false in
/-- Each augmentation component factors through the original injective target term. -/
lemma injectiveStepCoconeι_factor (K : CochainComplex C ℤ) (n : ℤ) :
    (injectiveStepCoconeι K).f n =
      (injectiveStepContractibleι K).f n ≫
        (mappingCocone.inl (injectiveStepQuotientπ K)).v n n (add_zero n) := by
  calc
    (injectiveStepCoconeι K).f n = (injectiveStepCoconeι K).f n ≫
        ((mappingCocone.fst (injectiveStepQuotientπ K)).f n ≫
          (mappingCocone.inl (injectiveStepQuotientπ K)).v n n (add_zero n) +
        (mappingCocone.snd (injectiveStepQuotientπ K)).v n (n - 1) (by lia) ≫
          (mappingCocone.inr (injectiveStepQuotientπ K)).1.v (n - 1) n (by lia)) := by
      rw [mappingCocone.id_X]
      simp
    _ = _ := by simp [Preadditive.comp_add, injectiveStepCoconeι]

set_option backward.isDefEq.respectTransparency false in
/-- The term through which the augmentation factors is an injective subobject. -/
lemma injectiveStepCoconeι_injectiveFactor (K : CochainComplex C ℤ) (n : ℤ) :
    ∃ (I : C) (_ : Injective I) (a : K.X n ⟶ I)
      (b : I ⟶ (injectiveStepCocone K).X n), Mono b ∧
        (injectiveStepCoconeι K).f n = a ≫ b := by
  refine ⟨((injectiveStepContractible C).obj K).X n, inferInstance,
    (injectiveStepContractibleι K).f n,
    (mappingCocone.inl (injectiveStepQuotientπ K)).v n n (add_zero n), ?_,
    injectiveStepCoconeι_factor K n⟩
  exact mono_of_mono_fac (mappingCocone.inl_v_fst_f (injectiveStepQuotientπ K) n)

end CochainComplex
