/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.GaloisActionMaps
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.ConstantModuleSheaves
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.FiniteExact
public import Aglib.RepresentationTheory.FiniteModulePGroup

/-! # Proper cohomology of modules trivialized by a p-group cover

Finite prime-killed representations are built from finite trivial left-hand
subobjects. Actual invariant sections descend those subobjects; their actual
sheaf cokernels, not a representation-to-sheaf equivalence, supply the
induction step. Original-map naturality identifies the quotient action after
the native module cokernel isomorphism.

The literal supplied coefficient module is explicitly killed by the prime.
It need not have a finite underlying additive group. The coefficient-ring
universe is independent. Noetherianity enters only the finite-middle
cohomology argument, not the representation or sheaf induction.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

universe u r e

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable {R : Type r} [CommRing R] {X : Scheme.{u}} [ConnectedSpace X]
  (Y : Scheme.FiniteEtale X) [PreGaloisCategory.IsGalois Y] [Surjective Y.obj.hom]
  [ConnectedSpace Y.obj.left] [CompactSpace Y.obj.left] [QuasiSeparatedSpace Y.obj.left]

/-- A trivial actual deck action descends the original chosen constant module.
This is the identity-map case of invariant-section descent, not arbitrary object descent. -/
def galoisTrivialActionIso (F : ModuleSheaf R X) (M : ModuleCat.{u + 1} R)
    (hM : IsAddTorsion M)
    (e : (moduleInverseImage R Y.obj.hom).obj F ≅
      (constantSheaf Y.obj.left.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M)
    (htriv : ∀ (σ : Aut Y) (m : M), trivializedDeckRepresentation F Y M hM e σ m = m) :
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M ≅ F := by
  let d := galoisTrivialSubobjectMap F Y M hM e (𝟙 M) htriv
  have hd : (moduleInverseImage R Y.obj.hom).map d ≫ e.hom =
      (moduleInverseImageConstantIso R Y.obj.hom).hom.app M := by
    let C := constantSheaf Y.obj.left.smallEtaleTopology (ModuleCat.{u + 1} R)
    let a := (moduleInverseImageConstantIso R Y.obj.hom).hom.app M
    have hc : C.map (𝟙 M) = 𝟙 (C.obj M) := CategoryTheory.Functor.map_id C M
    exact (galoisTrivialSubobjectMap_pullback F Y M hM e (𝟙 M) htriv).trans
      ((congrArg (fun b : C.obj M ⟶ C.obj M => a ≫ b) hc).trans (Category.comp_id a))
  have : IsIso ((moduleInverseImage R Y.obj.hom).map d ≫ e.hom) := by
    rw [hd]
    infer_instance
  have hmap : IsIso ((moduleInverseImage R Y.obj.hom).map d) :=
    IsIso.of_isIso_comp_right _ e.hom
  have : IsIso d := isIso_of_module_etale_inverseImages R
    (fun _ : Unit => (Scheme.FiniteEtale.toEtale X).obj Y)
    (fun x => by obtain ⟨y, hy⟩ := Y.obj.hom.surjective x; exact ⟨(), y, hy⟩)
    d (fun _ => hmap)
  exact asIso d

/-- An isomorphism-invariant property of actual sheaves that contains the finite
prime-killed constants and is closed under short exact extensions holds for
actual finite prime-killed modules trivialized by the given p-group cover. -/
theorem property_of_pGroup_trivialization (p : ℕ) [Fact p.Prime]
    (hY : IsPGroup p (Aut Y)) (P : ModuleSheaf R X → Prop)
    (hconstant : ∀ (M : ModuleCat.{u + 1} R), ∀ [Module.Finite R M],
      (∀ m : M, p • m = 0) →
        P ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M))
    (hiso : ∀ {F G : ModuleSheaf R X}, (F ≅ G) → P F → P G)
    (hstep : ∀ S : ShortComplex (ModuleSheaf R X), S.ShortExact →
      P S.X₁ → P S.X₃ → P S.X₂)
    (F : ModuleSheaf R X) (M : ModuleCat.{u + 1} R) [Module.Finite R M]
    (hM : ∀ m : M, p • m = 0)
    (e : (moduleInverseImage R Y.obj.hom).obj F ≅
      (constantSheaf Y.obj.left.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M) : P F := by
  let U := forget₂ (Rep.{u + 1} R (Aut Y)) (ModuleCat.{u + 1} R)
  let C := constantSheaf Y.obj.left.smallEtaleTopology (ModuleCat.{u + 1} R)
  let Q : Rep.{u + 1} R (Aut Y) → Prop := fun A =>
    ∀ (_ : Module.Finite R A) (hp : ∀ a : A, p • a = 0)
      (E : ModuleSheaf R X)
      (t : (moduleInverseImage R Y.obj.hom).obj E ≅ C.obj (U.obj A)),
      trivializedDeckRepresentation E Y (U.obj A)
        (moduleIsAddTorsion_of_nsmul_eq_zero (U.obj A) p (Nat.Prime.pos (Fact.out)) hp) t =
          A.ρ → P E
  have hQ : ∀ (A : Rep.{u + 1} R (Aut Y)), ∀ [Module.Finite R A],
      (∀ a : A, p • a = 0) → Q A := by
    intro A _ hp
    apply Rep.induction_finite_of_prime_nsmul_trivial_subobject p hY Q ?_ ?_ A hp
    · intro B _ _ hB hfinite hpB E t hρ
      let := hfinite
      let := hB
      let ht := moduleIsAddTorsion_of_nsmul_eq_zero (U.obj B) p
        (Nat.Prime.pos (Fact.out)) hpB
      have htriv (σ : Aut Y) (b : U.obj B) :
          trivializedDeckRepresentation E Y (U.obj B) ht t σ b = b := by
        rw [hρ]
        exact Representation.isTrivial_apply B.ρ σ b
      exact hiso (galoisTrivialActionIso Y E (U.obj B) ht t htriv)
        (hconstant (U.obj B) hpB)
    · intro S hS hfinite₁ hp₁ htriv₁ hquot hfinite₂ hp₂ E t hρ
      let := hfinite₁
      let := hfinite₂
      let := htriv₁
      let T := S.map U
      have hT : T.ShortExact := hS.map_of_exact U
      have : Mono S.f := hS.mono_f
      have : Epi S.g := hS.epi_g
      have : Epi T.g := hT.epi_g
      let ht := moduleIsAddTorsion_of_nsmul_eq_zero (U.obj S.X₂) p
        (Nat.Prime.pos (Fact.out)) hp₂
      have hfix (σ : Aut Y) (b : U.obj S.X₁) :
          trivializedDeckRepresentation E Y (U.obj S.X₂) ht t σ (T.f b) = T.f b := by
        rw [hρ]
        exact (Rep.hom_comm_apply S.f σ b).symm.trans
          (congrArg S.f (Representation.isTrivial_apply S.X₁.ρ σ b))
      let d := galoisTrivialSubobjectMap E Y (U.obj S.X₂) ht t T.f hfix
      let E' := cokernel d
      have hd : (ShortComplex.cokernelSequence d).ShortExact :=
        galoisTrivialSubobjectMap_shortExact E Y (U.obj S.X₂) ht t T.f hfix
          ((Rep.mono_iff_injective S.f).mp inferInstance)
      have hsurj : Function.Surjective S.g :=
        (Rep.epi_iff_surjective S.g).mp inferInstance
      have hfinite₃ : Module.Finite R S.X₃ :=
        Module.Finite.of_surjective S.g.hom.toLinearMap hsurj
      have hp₃ (b : S.X₃) : p • b = 0 := by
        obtain ⟨a, rfl⟩ := hsurj b
        rw [← map_nsmul, hp₂, map_zero]
      have : Mono (cokernel.desc T.f T.g T.zero) := hT.exact.mono_cokernelDesc
      have : IsIso (cokernel.desc T.f T.g T.zero) := isIso_of_mono_of_epi _
      let c : cokernel T.f ≅ U.obj S.X₃ := asIso (cokernel.desc T.f T.g T.zero)
      let t' : (moduleInverseImage R Y.obj.hom).obj E' ≅ C.obj (U.obj S.X₃) :=
        galoisTrivialSubobjectCokernelIso E Y (U.obj S.X₂) ht t T.f hfix ≪≫ C.mapIso c
      have hprojection : (moduleInverseImage R Y.obj.hom).map (cokernel.π d) ≫ t'.hom =
          t.hom ≫ C.map T.g := by
        change (moduleInverseImage R Y.obj.hom).map (cokernel.π d) ≫
          ((galoisTrivialSubobjectCokernelIso E Y (U.obj S.X₂) ht t T.f hfix).hom ≫
            C.map c.hom) = _
        rw [← Category.assoc, galoisTrivialSubobjectCokernelIso_projection,
          Category.assoc, ← C.map_comp]
        change t.hom ≫ C.map (cokernel.π T.f ≫ cokernel.desc T.f T.g T.zero) = _
        rw [cokernel.π_desc]
      let ht₃ := moduleIsAddTorsion_of_nsmul_eq_zero (U.obj S.X₃) p
        (Nat.Prime.pos (Fact.out)) hp₃
      have hρ₃ : trivializedDeckRepresentation E' Y (U.obj S.X₃) ht₃ t' = S.X₃.ρ := by
        ext σ b
        obtain ⟨a, rfl⟩ := hsurj b
        have hn := trivializedDeckRepresentation_naturality Y (U.obj S.X₂) (U.obj S.X₃)
          ht ht₃ t t' (cokernel.π d) T.g hprojection σ a
        rw [hρ] at hn
        exact hn.symm.trans (Rep.hom_comm_apply S.g σ a)
      exact hstep (ShortComplex.cokernelSequence d) hd (hconstant (U.obj S.X₁) hp₁)
        (hquot hfinite₃ hp₃ E' t' hρ₃)
  exact hQ (killedTrivializedDeckRep F Y M p (Nat.Prime.pos (Fact.out)) hM e) hM
    inferInstance hM F e rfl

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open AlgebraicGeometry.Scheme.OverField Constructible.Modules

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable {k : Type u} [Field k] [IsSepClosed k] (X : FScheme k) [IsProper X.hom]
  [ConnectedSpace X.left]
  [HasExt.{e} (AbelianSheaf.{u, u + 1} X.left)]
  [HasColimitsOfSize.{u + 1, u + 1} AddCommGrpCat.{e}]
  (p : ℕ) [Fact p.Prime] [CharP k p]
  (R : Type r) [CommRing R] [IsNoetherianRing R]

/-- An actual p-group Galois trivialization by a finite prime-killed original
module gives finite original module cohomology in every degree on a proper
scheme over a separably closed field of characteristic p.

The connected qcqs cover hypotheses are explicit. No finite underlying group,
small coefficient ring, general effective descent, or torsion-detection premise
is substituted for the literal chosen module and actual trivialization. -/
theorem moduleSheaf_cohomology_finite_of_pGroup_trivialization
    (Y : Scheme.FiniteEtale X.left) [PreGaloisCategory.IsGalois Y] [Surjective Y.obj.hom]
    [ConnectedSpace Y.obj.left] [CompactSpace Y.obj.left] [QuasiSeparatedSpace Y.obj.left]
    (hY : IsPGroup p (Aut Y)) (q : ℕ)
    (F : ModuleSheaf R X.left) (M : ModuleCat.{u + 1} R) [Module.Finite R M]
    (hM : ∀ m : M, p • m = 0)
    (e : (moduleInverseImage R Y.obj.hom).obj F ≅
      (constantSheaf Y.obj.left.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M) :
    Module.Finite R ((ModuleCat.Sheaf.cohomology X.left.smallEtaleTopology R q).obj F) := by
  apply property_of_pGroup_trivialization Y p hY
    (fun E => Module.Finite R
      ((ModuleCat.Sheaf.cohomology X.left.smallEtaleTopology R q).obj E))
    (fun N _ hp => constantModuleSheaf_cohomology_finite_of_prime_nsmul X p R q N hp)
    ?_ ?_ F M hM e
  · intro E E' i hE
    let := hE
    exact Module.Finite.equiv
      ((ModuleCat.Sheaf.cohomology X.left.smallEtaleTopology R q).mapIso i).toLinearEquiv
  · intro S hS h₁ h₃
    let := h₁
    let := h₃
    exact ModuleCat.Sheaf.finite_cohomology_of_shortExact X.left.smallEtaleTopology R S hS q

end AlgebraicGeometry.Scheme.EtaleCohomology
