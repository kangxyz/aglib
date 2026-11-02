/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Topology.Sheaves.Cech.Restriction
public import Aglib.AlgebraicGeometry.Modules.Generators.OpenFreeStalk
public import Aglib.AlgebraicGeometry.Modules.Locality.Isomorphisms
public import Aglib.CategoryTheory.Sites.SheafCohomology.Cech.Comparison
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
public import Mathlib.CategoryTheory.Abelian.Injective.Basic
/-!
# Exactness of the original Cech complexes with injective coefficients

On an arbitrary scheme, `openFreeCechComplex` is the actual chain complex
obtained by opposing mathlib's Cech construction on open-free generators.
It is exact in every positive degree for any family of opens. The proof
uses the original module stalk functors, contraction at a member containing
the point, and zero stalks outside the union.

The original additive section-representing equivalence then proves
`injectiveCech_exact_succ`: injective module sheaves have exact original
Cech cochain complexes in every positive degree. Empty families and families
whose union is a proper open are allowed. No quasicoherence is assumed.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe w v v' v'' u u' u''
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open CategoryTheory.ExactCategory
open scoped Simplicial
open CategoryTheory.Cech
namespace AlgebraicGeometry.Scheme.Modules

lemma openFree_stalkCech_exact_succ (X : Scheme.{u}) (x : X)
    {ι : Type u} (U : ι → X.Opens) (i₀ : ι) (hx : x ∈ U i₀) (n : ℕ) :
    ((cechComplexFunctor U).obj (openFreeFunctor X ⋙ moduleStalk X x).op).ExactAt
      (n + 1) := by
  let Q := openFreeFunctor X ⋙ moduleStalk X x
  let p : Q.op ⟶ (intersectFunctor (U i₀)).op ⋙ Q.op :=
    NatTrans.op (Functor.whiskerRight (intersectToId (U i₀)) Q)
  have hp (V : X.Opensᵒᵖ) : IsIso (p.app V) := by
    change IsIso (((moduleStalk X x).map ((openFreeFunctor X).map
      (homOfLE (show V.unop ⊓ U i₀ ≤ V.unop from inf_le_left)))).op)
    have := openFreeStalk_map_isIso X x
      (homOfLE (show V.unop ⊓ U i₀ ≤ V.unop from inf_le_left)) (fun hv => ⟨hv, hx⟩)
    infer_instance
  let : IsIso p := NatIso.isIso_of_isIso_app p
  exact (restrictedCech_exactAt_succ U Q.op i₀ n).of_iso
    ((cechComplexFunctor U).mapIso (asIso p)).symm

lemma shortComplex_exact_of_moduleStalk {X : Scheme.{u}} (S : ShortComplex X.Modules)
    (h : ∀ x, (S.map (moduleStalk X x)).Exact) : S.Exact := by
  let hF : JointlyReflectIsomorphisms (fun x : X => moduleStalk X x) := by
    refine ⟨?_⟩
    intro M N f hf
    apply (moduleSheaf_isIso_iff_stalks f).mpr
    intro x
    let : IsIso ((moduleStalk X x).map f) := hf x
    exact (NatIso.isIso_map_iff (moduleStalkForgetIso X x) f).mp
      (inferInstanceAs (IsIso
        ((forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat.{u}).map
          ((moduleStalk X x).map f))))
  exact (hF.exact_iff S).mpr h

/-- The actual Cech chain complex of open-free module sheaves, obtained by
opposing mathlib's original Cech cochain construction. -/
abbrev openFreeCechComplex (X : Scheme.{u}) {ι : Type u} (U : ι → X.Opens) :=
  ((cechComplexFunctor U).obj (openFreeFunctor X).op).unop

lemma openFree_stalk_isZero_of_not_mem (X : Scheme.{u}) (x : X) (U : X.Opens)
    (hx : x ∉ U) : IsZero ((moduleStalk X x).obj (openFree X U)) := by
  let : IsEmpty (ULift.{u} (PLift (x ∈ U))) := ⟨fun h => hx h.down.down⟩
  let : Subsingleton ((ModuleCat.free (X.presheaf.stalk x)).obj
      (ULift.{u} (PLift (x ∈ U)))) :=
    inferInstanceAs (Subsingleton (ULift.{u} (PLift (x ∈ U)) →₀ X.presheaf.stalk x))
  exact (ModuleCat.isZero_of_subsingleton _).of_iso (openFreeStalkIso X x U)

lemma openFree_stalkCech_exact_succ_any (X : Scheme.{u}) (x : X)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ) :
    ((cechComplexFunctor U).obj (openFreeFunctor X ⋙ moduleStalk X x).op).ExactAt
      (n + 1) := by
  classical
  by_cases h : ∃ i, x ∈ U i
  · obtain ⟨i, hi⟩ := h
    exact openFree_stalkCech_exact_succ X x U i hi n
  · apply HomologicalComplex.ExactAt.of_isZero
    rw [IsZero.iff_id_eq_zero]
    apply Pi.hom_ext
    intro a
    have hx : x ∉ (∏ᶜ fun k : Fin (n + 2) => U (a k)) := by
      intro ha
      exact h ⟨a 0, (leOfHom (Pi.π (fun k : Fin (n + 2) => U (a k)) 0)) ha⟩
    exact (openFree_stalk_isZero_of_not_mem X x _ hx).op.eq_of_tgt _ _

lemma openFreeCechComplex_exact_succ (X : Scheme.{u}) {ι : Type u}
    (U : ι → X.Opens) (n : ℕ) : (openFreeCechComplex X U).ExactAt (n + 1) := by
  apply shortComplex_exact_of_moduleStalk
  intro x
  have h := (openFree_stalkCech_exact_succ_any X x U n).of_iso
    (cechComplexCoefficientIso (moduleStalk X x).op U (openFreeFunctor X).op).symm
  exact h.unop

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

lemma openFreeHomEquiv_add (X : Scheme.{u}) (U : X.Opens) (M : X.Modules)
    (p q : openFree X U ⟶ M) :
    openFreeHomEquiv X U M (p + q) =
      openFreeHomEquiv X U M p + openFreeHomEquiv X U M q := by
  let : (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).Additive :=
    Functor.additive_of_preserves_binary_products _
  let adj := _root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  have H := adj.homAddEquiv_add ((_root_.PresheafOfModules.free _).obj (yoneda.obj U)) M p q
  change _root_.PresheafOfModules.freeYonedaEquiv (adj.homEquiv _ _ (p + q)) =
    _root_.PresheafOfModules.freeYonedaEquiv (adj.homEquiv _ _ p) +
      _root_.PresheafOfModules.freeYonedaEquiv (adj.homEquiv _ _ q)
  rw [H]
  rfl

/-- The additive equivalence between morphisms from the open-free module sheaf on `U` to `M` and
sections of `M` over `U`. -/
def openFreeHomAddEquiv (X : Scheme.{u}) (U : X.Opens) (M : X.Modules) :
    (openFree X U ⟶ M) ≃+ Γ(M, U) :=
  { openFreeHomEquiv X U M with map_add' := openFreeHomEquiv_add X U M }

/-- The natural isomorphism from the additive Hom presheaf represented by the open-free generators
to the underlying section presheaf of `M`. -/
def openFreeYonedaIso (X : Scheme.{u}) (M : X.Modules) :
    (openFreeFunctor X).op ⋙ preadditiveYoneda.obj M ≅ M.presheaf := by
  refine NatIso.ofComponents (fun U => (openFreeHomAddEquiv X U.unop M).toAddCommGrpIso) ?_
  intro U V h
  ext p
  exact openFreeHomEquiv_naturality_open X h.unop M p

lemma injectiveCech_exact_succ (X : Scheme.{u}) (M : X.Modules) [Injective M]
    {ι : Type u} (U : ι → X.Opens) (n : ℕ) :
    ((cechComplexFunctor U).obj M.presheaf).ExactAt (n + 1) := by
  let F := preadditiveYoneda.obj M
  let : F.PreservesHomology := by
    change (preadditiveYonedaObj M ⋙ forget₂ _ _).PreservesHomology
    infer_instance
  have h : ((F.mapHomologicalComplex _).obj
      ((cechComplexFunctor U).obj (openFreeFunctor X).op)).ExactAt (n + 1) :=
    (openFreeCechComplex_exact_succ X U n).op.map F
  exact h.of_iso ((cechComplexCoefficientIso F U (openFreeFunctor X).op) ≪≫
    (cechComplexFunctor U).mapIso (openFreeYonedaIso X M))

lemma affine_injectiveCech_exact_succ {R : CommRingCat.{u}}
    (M : (Spec R).Modules) [Injective M] {ι : Type u}
    (U : ι → (Spec R).Opens) (n : ℕ) :
    ((cechComplexFunctor U).obj (modulesSpecToSheaf.obj M).obj).ExactAt (n + 1) := by
  let F := forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}
  apply (ShortComplex.exact_map_iff_of_faithful _ F).mp
  have h := injectiveCech_exact_succ (Spec R) M U n
  exact h.of_iso (cechComplexCoefficientIso F U (modulesSpecToSheaf.obj M).obj).symm

end AlgebraicGeometry.Scheme.Modules
