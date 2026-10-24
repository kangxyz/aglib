/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.InjectiveStep.Objects
public import Aglib.Algebra.Homology.MappingCone.Identity
public import Aglib.Algebra.Homology.MappingCocone.Map

/-!
# A functorial monomorphism into a contractible injective complex

This is the lower contractible-complex construction for Stacks 079N. The cone
and its lift use the construction of `Mathlib.Algebra.Homology.Factorizations.CM5b`
by Joël Riou, replacing the individual injective embeddings by the native
Grothendieck functorial embeddings. No boundedness condition is imposed.
The monomorphism into this contractible complex is not claimed to be a
quasi-isomorphism. The quotient-cone step is a separate construction.
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.IsGrothendieckAbelian

namespace CochainComplex

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

/-- The zero-differential complex of functorial injective objects. -/
def injectiveStepGraded (K : CochainComplex C ℤ) : CochainComplex C ℤ where
  X n := (injectiveStepObjects C).obj (K.X n)
  d _ _ := 0

/-- The zero-differential construction is functorial without additivity. -/
abbrev injectiveStepGradedFunctor : CochainComplex C ℤ ⥤ CochainComplex C ℤ where
  obj := injectiveStepGraded C
  map f :=
    { f n := (injectiveStepObjects C).map (f.f n)
      comm' := by intros; simp [injectiveStepGraded] }
  map_id K := by ext n; exact (injectiveStepObjects C).map_id (K.X n)
  map_comp f g := by ext n; exact (injectiveStepObjects C).map_comp (f.f n) (g.f n)

/-- The actual identity cone, not a new complex carrier. -/
abbrev injectiveStepContractible : CochainComplex C ℤ ⥤ CochainComplex C ℤ :=
  injectiveStepGradedFunctor C ⋙ identityConeFunctor

variable {C}

instance injectiveStepGraded_injective (K : CochainComplex C ℤ) (n : ℤ) :
    Injective ((injectiveStepGraded C K).X n) := by
  dsimp [injectiveStepGraded]
  infer_instance

instance injectiveStepContractible_injective (K : CochainComplex C ℤ) (n : ℤ) :
    Injective (((injectiveStepContractible C).obj K).X n) :=
  Injective.of_iso
    (HomologicalComplex.homotopyCofiber.XIsoBiprod
      (𝟙 (injectiveStepGraded C K)) n (n + 1) rfl).symm inferInstance

set_option backward.isDefEq.respectTransparency false in
/-- The actual lift of the original componentwise injective embeddings. -/
def injectiveStepContractibleι (K : CochainComplex C ℤ) :
    K ⟶ (injectiveStepContractible C).obj K :=
  mappingCone.lift (𝟙 (injectiveStepGraded C K))
    (HomComplex.Cocycle.mk
      (HomComplex.Cochain.mk (fun p q _ =>
        K.d p q ≫ (injectiveStepObjectsι C).app (K.X q))) 2
      (by lia) (by
        ext p q hpq
        simp [HomComplex.δ_v 1 2 (by lia) _ p q hpq
          (p + 1) (p + 1) (by lia) rfl, injectiveStepGraded,
          -injectiveStepObjectsι_naturality, -injectiveStepObjectsι_naturality_assoc]))
    (HomComplex.Cochain.ofHoms (fun n => (injectiveStepObjectsι C).app (K.X n)))
    (by
      ext p q hpq
      subst q
      simp [HomComplex.δ_v 0 1 (by lia) _ p (p + 1) rfl p (p + 1) (by lia) rfl,
        injectiveStepGraded, -injectiveStepObjectsι_naturality,
        -injectiveStepObjectsι_naturality_assoc])

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma injectiveStepContractibleι_snd (K : CochainComplex C ℤ) (n : ℤ) :
    (injectiveStepContractibleι K).f n ≫
      (mappingCone.snd (𝟙 (injectiveStepGraded C K))).v n n (add_zero n) =
        (injectiveStepObjectsι C).app (K.X n) := by
  simp [injectiveStepContractibleι]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma injectiveStepContractibleι_fst (K : CochainComplex C ℤ) (n : ℤ) :
    (injectiveStepContractibleι K).f n ≫
      (mappingCone.fst (𝟙 (injectiveStepGraded C K))).1.v n (n + 1) rfl =
        K.d n (n + 1) ≫ (injectiveStepObjectsι C).app (K.X (n + 1)) := by
  simp [injectiveStepContractibleι]

set_option backward.isDefEq.respectTransparency false in
instance injectiveStepContractibleι_mono_f (K : CochainComplex C ℤ) (n : ℤ) :
    Mono ((injectiveStepContractibleι K).f n) := by
  have : Mono ((injectiveStepObjectsι C).app (K.X n)) :=
    injectiveStepObjectsι_mono C (K.X n)
  exact mono_of_mono_fac (injectiveStepContractibleι_snd K n)

instance injectiveStepContractibleι_mono (K : CochainComplex C ℤ) :
    Mono (injectiveStepContractibleι K) :=
  HomologicalComplex.mono_of_mono_f _ inferInstance

set_option backward.isDefEq.respectTransparency false in
/-- The original embedding commutes with every original complex morphism. -/
@[reassoc]
lemma injectiveStepContractibleι_naturality {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    f ≫ injectiveStepContractibleι L =
      injectiveStepContractibleι K ≫ (injectiveStepContractible C).map f := by
  ext n
  apply mappingCone.ext_to (𝟙 (injectiveStepGraded C L)) n (n + 1) rfl
  · simp only [HomologicalComplex.comp_f, Category.assoc]
    change f.f n ≫ (injectiveStepContractibleι L).f n ≫
        (mappingCone.fst (𝟙 (injectiveStepGraded C L))).1.v n (n + 1) rfl =
      (injectiveStepContractibleι K).f n ≫
        (mappingCone.map (𝟙 (injectiveStepGraded C K)) (𝟙 (injectiveStepGraded C L))
          ((injectiveStepGradedFunctor C).map f) ((injectiveStepGradedFunctor C).map f)
          (by simp)).f n ≫
        (mappingCone.fst (𝟙 (injectiveStepGraded C L))).1.v n (n + 1) rfl
    rw [mappingCone.map_f_fst_v]
    simp only [injectiveStepContractibleι_fst, injectiveStepContractibleι_fst_assoc]
    change f.f n ≫ L.d n (n + 1) ≫ (injectiveStepObjectsι C).app (L.X (n + 1)) =
      K.d n (n + 1) ≫ (injectiveStepObjectsι C).app (K.X (n + 1)) ≫
        (injectiveStepObjects C).map (f.f (n + 1))
    rw [← injectiveStepObjectsι_naturality, ← f.comm_assoc]
  · simp only [HomologicalComplex.comp_f, Category.assoc]
    change f.f n ≫ (injectiveStepContractibleι L).f n ≫
        (mappingCone.snd (𝟙 (injectiveStepGraded C L))).v n n (add_zero n) =
      (injectiveStepContractibleι K).f n ≫
        (mappingCone.map (𝟙 (injectiveStepGraded C K)) (𝟙 (injectiveStepGraded C L))
          ((injectiveStepGradedFunctor C).map f) ((injectiveStepGradedFunctor C).map f)
          (by simp)).f n ≫
        (mappingCone.snd (𝟙 (injectiveStepGraded C L))).v n n (add_zero n)
    rw [mappingCone.map_f_snd_v]
    simp only [injectiveStepContractibleι_snd, injectiveStepContractibleι_snd_assoc]
    exact injectiveStepObjectsι_naturality C (f.f n)

/-- The actual natural monomorphism into the contractible target functor. -/
def injectiveStepContractibleUnit : 𝟭 (CochainComplex C ℤ) ⟶
    injectiveStepContractible C where
  app := injectiveStepContractibleι
  naturality {_K _L} f := injectiveStepContractibleι_naturality f

/-- A specified contraction of the actual target identity cone. -/
def injectiveStepContractibleHomotopy (K : CochainComplex C ℤ) :
    Homotopy (𝟙 ((injectiveStepContractible C).obj K)) 0 := by
  change Homotopy (𝟙 (mappingCone (𝟙 (injectiveStepGraded C K)))) 0
  exact mappingCone.liftHomotopy _ _ _ (mappingCone.snd _) 0 (by simp) (by simp)

end CochainComplex
