/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.RepresentedDiagram
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.InjectiveDiagram.Cokernel
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.ShortComplexColimit
public import Aglib.Algebra.Homology.DerivedCategory.Ext.ShortExactComparison

/-!
# Connecting maps and exact fragments of represented Ext diagrams

The connecting homomorphism is native Yoneda postcomposition with the original
short exact sequence's extension class. Its naturality uses the actual three
left-transition maps of the cokernel sequence. Evaluation detects exactness of
the represented row; its colimit is exact under the stated exact-colimit
hypothesis. No geometric continuity or injective-existence premise is used.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory

universe uC vC uB vB e

section ExactTransport

variable {C : Type uC} [Category.{vC} C] [Abelian C] [HasExt.{e} C]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasExt.{e} B]
  (L : C ⥤ B) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  {X : C} {V : B} (a : V ⟶ L.obj X)
  {T : ShortComplex C} {S : ShortComplex B}
  (hT : T.ShortExact) (hS : S.ShortExact) (α : T.map L ⟶ S) (n : ℕ)

/-- Exact source transport and the actual sequence morphism respect the original
connecting extension classes, with the Ext universe independent of the coefficient categories. -/
lemma Functor.extPrecompMap_connecting_naturality :
    AddCommGrpCat.ofHom (hT.extClass.postcomp X (show n + 1 = n + 1 from rfl)) ≫
        AddCommGrpCat.ofHom
          (((Ext.mk₀ α.τ₁).postcomp V (add_zero (n + 1))).comp
            (L.extPrecompMap a T.X₁ (n + 1))) =
      AddCommGrpCat.ofHom
          (((Ext.mk₀ α.τ₃).postcomp V (add_zero n)).comp
            (L.extPrecompMap a T.X₃ n)) ≫
        AddCommGrpCat.ofHom (hS.extClass.postcomp V (show n + 1 = n + 1 from rfl)) := by
  ext x
  change (L.extPrecompMap a T.X₁ (n + 1) (x.comp hT.extClass rfl)).comp
      (Ext.mk₀ α.τ₁) (add_zero (n + 1)) =
    ((L.extPrecompMap a T.X₃ n x).comp (Ext.mk₀ α.τ₃) (add_zero n)).comp
      hS.extClass rfl
  have hx := congrArg (fun f => f x) (L.extPrecompMap_connecting a T hT n)
  change (L.extPrecompMap a T.X₃ n x).comp (hT.map_of_exact L).extClass rfl =
    L.extPrecompMap a T.X₁ (n + 1) (x.comp hT.extClass rfl) at hx
  rw [← hx, Ext.comp_assoc_of_third_deg_zero,
    ShortComplex.ShortExact.extClass_naturality (hT.map_of_exact L) hS α,
    Ext.comp_assoc_of_second_deg_zero]

end ExactTransport

section ColimitLeg

universe uJ vJ

variable {J : Type uJ} [Category.{vJ} J]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasColimitsOfShape J B]

/-- The three actual colimit injections form a morphism from an evaluated
sequence to its colimit sequence. -/
def ShortComplex.evaluationToColimit (T : ShortComplex (J ⥤ B)) (i : J) :
    T.map ((CategoryTheory.evaluation J B).obj i) ⟶ T.map colim where
  τ₁ := colimit.ι T.X₁ i
  τ₂ := colimit.ι T.X₂ i
  τ₃ := colimit.ι T.X₃ i
  comm₁₂ := colimit.ι_map T.f i
  comm₂₃ := colimit.ι_map T.g i

end ColimitLeg

section NativeRow

variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasExt.{e} B]
  (V : B) {S : ShortComplex B} (hS : S.ShortExact) (n : ℕ)

/-- The actual native fragment Extⁿ(V,S₂) → Extⁿ(V,S₃) → Extⁿ⁺¹(V,S₁). -/
def representedExtConnectingComplex : ShortComplex AddCommGrpCat.{e} :=
  ShortComplex.mk
    (AddCommGrpCat.ofHom ((Ext.mk₀ S.g).postcomp V (add_zero n)))
    (AddCommGrpCat.ofHom (hS.extClass.postcomp V (show n + 1 = n + 1 from rfl)))
    ((Ext.covariantSequence_exact V hS n (n + 1) rfl).zero 1)

/-- Exactness is the native covariant Ext sequence. -/
lemma representedExtConnectingComplex_exact :
    (representedExtConnectingComplex V hS n).Exact :=
  Ext.covariant_sequence_exact₃' V hS n (n + 1) rfl

end NativeRow

section ExactTransportRow

variable {C : Type uC} [Category.{vC} C] [Abelian C] [HasExt.{e} C]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasExt.{e} B]
  (L : C ⥤ B) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  {X : C} {V : B} (a : V ⟶ L.obj X)
  {T : ShortComplex C} {S : ShortComplex B}
  (hT : T.ShortExact) (hS : S.ShortExact) (α : T.map L ⟶ S) (n : ℕ)

/-- The actual sequence morphism and source transport give a morphism of the
native represented Ext fragments. -/
def Functor.extPrecompMap_connectingComplexHom :
    representedExtConnectingComplex X hT n ⟶ representedExtConnectingComplex V hS n where
  τ₁ := AddCommGrpCat.ofHom
    (((Ext.mk₀ α.τ₂).postcomp V (add_zero n)).comp (L.extPrecompMap a T.X₂ n))
  τ₂ := AddCommGrpCat.ofHom
    (((Ext.mk₀ α.τ₃).postcomp V (add_zero n)).comp (L.extPrecompMap a T.X₃ n))
  τ₃ := AddCommGrpCat.ofHom
    (((Ext.mk₀ α.τ₁).postcomp V (add_zero (n + 1))).comp
      (L.extPrecompMap a T.X₁ (n + 1)))
  comm₁₂ := by
    have h (x : Ext X T.X₂ n) :
        ((L.extPrecompMap a T.X₂ n x).comp (Ext.mk₀ α.τ₂) (add_zero n)).comp
            (Ext.mk₀ S.g) (add_zero n) =
          (L.extPrecompMap a T.X₃ n (x.comp (Ext.mk₀ T.g) (add_zero n))).comp
            (Ext.mk₀ α.τ₃) (add_zero n) := by
      rw [Functor.extPrecompMap_comp, Ext.mapExactFunctor_mk₀]
      simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]
      rw [α.comm₂₃]
      simp only [ShortComplex.map_g]
    ext x
    exact h x
  comm₂₃ := (L.extPrecompMap_connecting_naturality a hT hS α n).symm

end ExactTransportRow

namespace InjectiveSystem

universe uI vI uA vA

variable {I : Type uI} [Category.{vI} I]
  {A : I → Type uA} [∀ i, Category.{vA} (A i)] (D : AdjunctionData A)
  [∀ i, Abelian (A i)] {F Q : System D} (η : System.Hom D F Q)

/-- The actual left transitions of all three coefficient systems form a
morphism of the original pointwise cokernel sequences. -/
def System.cokernelLeftTransition {i j : I} (a : i ⟶ j)
    [(D.left a).PreservesZeroMorphisms] :
    (System.cokernelShortComplex D η i).map (D.left a) ⟶
      System.cokernelShortComplex D η j where
  τ₁ := F.leftMap D a
  τ₂ := Q.leftMap D a
  τ₃ := (System.cokernel D η).leftMap D a
  comm₁₂ := (System.Hom.leftMap_naturality D η a).symm
  comm₂₃ := (System.Hom.leftMap_naturality D (System.cokernelπ D η) a).symm

/-- Pointwise monicity supplies the native short exact certificate at each
index, with no condition on injective objects. -/
lemma System.cokernelShortComplex_shortExact_of_mono
    (hη : ∀ i, Mono (η.app i)) (i : I) :
    (System.cokernelShortComplex D η i).ShortExact := by
  let : Mono (η.app i) := hη i
  exact System.cokernelShortComplex_shortExact D η i

variable (U : System D)
  [∀ {i j : I} (a : i ⟶ j), IsIso (U.leftMap D a)]
  [∀ i, HasExt.{e} (A i)]
  [∀ {i j : I} (a : i ⟶ j), (D.left a).Additive]
  [∀ {i j : I} (a : i ⟶ j), PreservesFiniteLimits (D.left a)]
  [∀ {i j : I} (a : i ⟶ j), PreservesFiniteColimits (D.left a)]
  (hη : ∀ i, Mono (η.app i)) (n : ℕ)

/-- The represented connecting transformation has the literal component
`x ↦ x.comp hᵢ.extClass rfl`. -/
def representedCohomologyConnecting :
    representedCohomologyFunctor D U (System.cokernel D η) n ⟶
      representedCohomologyFunctor D U F (n + 1) where
  app i := AddCommGrpCat.ofHom
    ((System.cokernelShortComplex_shortExact_of_mono D η hη i).extClass.postcomp
      (U.obj i) (show n + 1 = n + 1 from rfl))
  naturality i j a :=
    (Functor.extPrecompMap_connecting_naturality (D.left a)
      (inv (U.leftMap D a))
      (System.cokernelShortComplex_shortExact_of_mono D η hη i)
      (System.cokernelShortComplex_shortExact_of_mono D η hη j)
      (System.cokernelLeftTransition D η a) n).symm

/-- The represented row retains the original quotient coefficient map and
the original connecting extension class. -/
def representedCohomologyConnectingComplex : ShortComplex (I ⥤ AddCommGrpCat.{e}) where
  f := representedCohomologyNatTrans D U (System.cokernelπ D η) n
  g := representedCohomologyConnecting D η U hη n
  zero := by
    apply NatTrans.ext
    funext i
    exact (Ext.covariantSequence_exact (U.obj i)
      (System.cokernelShortComplex_shortExact_of_mono D η hη i) n (n + 1) rfl).zero 1

/-- Evaluation of the represented row is the native exact Ext fragment. -/
lemma representedCohomologyConnectingComplex_exact :
    (representedCohomologyConnectingComplex D η U hη n).Exact := by
  apply ShortComplex.exact_of_evaluation
  intro i
  exact Ext.covariant_sequence_exact₃' (U.obj i)
    (System.cokernelShortComplex_shortExact_of_mono D η hη i) n (n + 1) rfl

section ColimitComparison

variable [HasColimitsOfShape I AddCommGrpCat.{e}]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasExt.{e} B]
  (L : ∀ i, A i ⥤ B) [∀ i, (L i).Additive]
  [∀ i, PreservesFiniteLimits (L i)] [∀ i, PreservesFiniteColimits (L i)]
  (V : B) (a : ∀ i, V ⟶ (L i).obj (U.obj i))
  {S : ShortComplex B} (hS : S.ShortExact)
  (α : ∀ i, (System.cokernelShortComplex D η i).map (L i) ⟶ S)

/-- The original comparison maps commute with the connecting maps when their
colimit legs are the actual exact-functor and sequence-morphism maps. The
connecting law is proved from those maps, not assumed for the comparisons. -/
lemma representedCohomologyConnecting_colimit_connecting
    (p₁ : colimit (representedCohomologyFunctor D U F (n + 1)) ⟶
      AddCommGrpCat.of (Ext V S.X₁ (n + 1)))
    (p₃ : colimit (representedCohomologyFunctor D U (System.cokernel D η) n) ⟶
      AddCommGrpCat.of (Ext V S.X₃ n))
    (h₁ : ∀ i, colimit.ι (representedCohomologyFunctor D U F (n + 1)) i ≫ p₁ =
      ((L i).extPrecompMap_connectingComplexHom (a i)
        (System.cokernelShortComplex_shortExact_of_mono D η hη i) hS (α i) n).τ₃)
    (h₃ : ∀ i,
      colimit.ι (representedCohomologyFunctor D U (System.cokernel D η) n) i ≫ p₃ =
        ((L i).extPrecompMap_connectingComplexHom (a i)
          (System.cokernelShortComplex_shortExact_of_mono D η hη i) hS (α i) n).τ₂) :
    colim.map (representedCohomologyConnecting D η U hη n) ≫ p₁ =
      p₃ ≫ AddCommGrpCat.ofHom
        (hS.extClass.postcomp V (show n + 1 = n + 1 from rfl)) := by
  apply colimit.hom_ext
  intro i
  rw [colimit.ι_map_assoc, h₁, ← Category.assoc, h₃]
  exact ((L i).extPrecompMap_connectingComplexHom (a i)
    (System.cokernelShortComplex_shortExact_of_mono D η hη i) hS (α i) n).comm₂₃.symm

/-- The three original comparison maps form a morphism of the actual
represented rows. Both squares follow from the stage sequence morphisms and
the literal colimit-leg equations. -/
def representedCohomologyConnectingComparison
    (p₂ : colimit (representedCohomologyFunctor D U Q n) ⟶
      AddCommGrpCat.of (Ext V S.X₂ n))
    (p₃ : colimit (representedCohomologyFunctor D U (System.cokernel D η) n) ⟶
      AddCommGrpCat.of (Ext V S.X₃ n))
    (p₁ : colimit (representedCohomologyFunctor D U F (n + 1)) ⟶
      AddCommGrpCat.of (Ext V S.X₁ (n + 1)))
    (h₂ : ∀ i, colimit.ι (representedCohomologyFunctor D U Q n) i ≫ p₂ =
      ((L i).extPrecompMap_connectingComplexHom (a i)
        (System.cokernelShortComplex_shortExact_of_mono D η hη i) hS (α i) n).τ₁)
    (h₃ : ∀ i,
      colimit.ι (representedCohomologyFunctor D U (System.cokernel D η) n) i ≫ p₃ =
        ((L i).extPrecompMap_connectingComplexHom (a i)
          (System.cokernelShortComplex_shortExact_of_mono D η hη i) hS (α i) n).τ₂)
    (h₁ : ∀ i, colimit.ι (representedCohomologyFunctor D U F (n + 1)) i ≫ p₁ =
      ((L i).extPrecompMap_connectingComplexHom (a i)
        (System.cokernelShortComplex_shortExact_of_mono D η hη i) hS (α i) n).τ₃) :
    (representedCohomologyConnectingComplex D η U hη n).map colim ⟶
      representedExtConnectingComplex V hS n where
  τ₁ := p₂
  τ₂ := p₃
  τ₃ := p₁
  comm₁₂ := by
    have h : p₂ ≫ AddCommGrpCat.ofHom ((Ext.mk₀ S.g).postcomp V (add_zero n)) =
        colim.map (representedCohomologyNatTrans D U (System.cokernelπ D η) n) ≫ p₃ := by
      apply colimit.hom_ext
      intro i
      rw [← Category.assoc, h₂, colimit.ι_map_assoc, h₃]
      exact ((L i).extPrecompMap_connectingComplexHom (a i)
        (System.cokernelShortComplex_shortExact_of_mono D η hη i) hS (α i) n).comm₁₂
    exact h
  comm₂₃ := (representedCohomologyConnecting_colimit_connecting D η U hη n
    L V a hS α p₁ p₃ h₁ h₃).symm

end ColimitComparison

variable [HasColimitsOfShape I AddCommGrpCat.{e}]
  [HasExactColimitsOfShape I AddCommGrpCat.{e}]

/-- The actual colimit row is exact when colimits of this precise shape are
exact in the original Ext-value category. -/
lemma representedCohomologyConnectingComplex_colimit_exact :
    ((representedCohomologyConnectingComplex D η U hη n).map colim).Exact :=
  (representedCohomologyConnectingComplex_exact D η U hη n).map colim

end InjectiveSystem

end CategoryTheory
