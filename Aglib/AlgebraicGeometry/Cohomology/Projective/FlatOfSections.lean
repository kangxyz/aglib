/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.FlatTwist
public import Aglib.AlgebraicGeometry.Modules.Flat.Relative.OfSections
public import Aglib.AlgebraicGeometry.ProjectiveSpace.SectionExtension.Colimit
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor.Equivalence.Hom
public import Aglib.RingTheory.Flat.EquationalCriterion

/-!
# Flatness from flat global sections of large twists

Let `R` be a commutative ring and `F` a quasicoherent module on `P = ProjectiveSpace R ι` with
finitely many coordinates. If `H^0(P, F(d))` is a flat `R`-module for every `d ≥ N`, then `F` is
relatively flat over `Spec R`. This is Nitsure, *Construction of Hilbert and Quot schemes*,
arXiv:math/0504590v1, Lemma 3.2, p. 15, over an affine base, where the hypothesis is local
freeness (for coherent `F` over a Noetherian base, local freeness, projectivity and flatness of
`π_* F(r)` agree). No Noetherian or finite-type hypothesis is needed for this direction. With the
converse of `FlatTwist` (the exercise after Lemma 3.2), Lemma 3.2 becomes an equivalence for
coherent `F` over a Noetherian ring.

Nitsure's proof localizes the graded module `⊕_{r ≥ N} H^0(F(r))` at `x_i`; its degree-zero part
is `Γ(D_+(x_i), F)`. Here the same colimit is used elementwise. Global sections of `F(d)` are
identified, linearly over `R`, with morphisms `O(-d) ⟶ F` (`negativeTwistHomLinearEquivH0`,
through `negativeTwistHomLinearEquivSections` of `ProjectiveSpace/Tensor/Equivalence/Hom`). By
`SectionExtension.Colimit`, a chart section is the value of such a morphism on the generator
`x_i^{-d}`, and the kernel of this evaluation is killed by precomposition with a power of `x_i`.
Hence every finite relation among chart sections lifts to a relation in one flat module
`Hom(O(-d), F)`, which is trivial there by the equational criterion ([Stacks, Tag 00HK]); so
`Γ(D_+(x_i), F)` is flat (`Module.Flat.of_forall_exists_lift_relation`). Flatness of the sections
on the standard affine cover gives relative flatness (`relativeFlat_of_flat_affineOpen_sections`).

The algebraic input `Module.Flat.of_forall_exists_lift_relation` lives in
`RingTheory/Flat/EquationalCriterion`, and `Scheme.Modules.unitHomGlobalSectionsLinearEquivOfHom`
(`Hom(𝒪_X, M) ≅ Γ(X, M)`, linearly) in `Modules/Linear`.

* `ProjectiveSpace.negativeTwistHomLinearEquivH0`: `Hom(O(-d), M) ≅ H^0(P, O(d) ⊗ M)`, linearly;
* `ProjectiveSpace.flat_coordinateOpen_sections_of_flat_negativeTwistHom`: flat chart sections;
* `relativeFlat_of_flat_twistedSections`, `relativeFlat_of_projective_twistedSections`: Lemma 3.2;
* `relativeFlat_iff_exists_projective_twistedSections`: Lemma 3.2 with its converse.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u v

namespace AlgebraicGeometry.ProjectiveSpace

variable {R : Type u} [CommRing R] {ι : Type u}

section Linear

variable {A : Type v} [CommRing A] (α : A →+* Γ(ProjectiveSpace R ι, ⊤))

variable [Finite ι]

/-- **Flat chart sections** (Nitsure, Lemma 3.2, p. 15, the step "`(M_{x_i})_0 = Γ(U_i, F)` is
flat"): if the morphism modules `Hom(O(-r), M)` are flat for all `r ≥ N`, then the sections of `M`
on every standard chart are flat over the structural ring. -/
theorem flat_coordinateOpen_sections_of_flat_negativeTwistHom
    (M : (ProjectiveSpace R ι).Modules) [M.IsQuasicoherent] (i : ι) (N : ℕ)
    (hflat : ∀ r : ℕ, N ≤ r →
      letI := moduleCategoryLinearOfHom (ProjectiveSpace R ι) α
      Module.Flat A (twistingSheaf R ι (-(r : ℤ)) ⟶ M)) :
    Module.Flat A ((ModuleCat.restrictScalars (((ProjectiveSpace R ι).presheaf.map
        (homOfLE (le_top : coordinateOpen R ι i ≤ ⊤)).op).hom.comp α)).obj
        (ModuleCat.of Γ(ProjectiveSpace R ι, coordinateOpen R ι i)
          Γ(M, coordinateOpen R ι i))) := by
  classical
  let := moduleCategoryLinearOfHom (ProjectiveSpace R ι) α
  refine Module.Flat.of_forall_exists_lift_relation (κ := {r : ℕ // N ≤ r})
    (E := fun r => twistingSheaf R ι (-((r : ℕ) : ℤ)) ⟶ M) (fun r => hflat r r.2)
    (fun r => negativeTwistChartEval M α i (-((r : ℕ) : ℤ))) ?_
  intro l f x hfx
  choose N₀ hN₀ using fun k => exists_negativeTwistHom_generator_eventually R ι M i (x k)
  let r := max N (Finset.univ.sup N₀)
  have hr (k : Fin l) : N₀ k ≤ r :=
    (Finset.le_sup (f := N₀) (Finset.mem_univ k)).trans (le_max_right _ _)
  choose φ hφ using fun k => hN₀ k r (hr k)
  have hψ : negativeTwistChartEval M α i (-(r : ℤ)) (∑ k, f k • φ k) = 0 := by
    rw [map_sum]
    simp only [_root_.map_smul]
    convert hfx using 3 with k
    exact hφ k
  obtain ⟨m, hm⟩ := exists_negativeTwistCoordinatePowerMap_comp_eq_zero M i r _ hψ
  have hrm : r ≤ r + m := Nat.le_add_right r m
  refine ⟨⟨r + m, (le_max_left _ _).trans hrm⟩,
    fun k => negativeTwistCoordinatePowerMap R ι i r (r + m) hrm ≫ φ k, fun k => ?_, ?_⟩
  · exact (negativeTwistCoordinatePowerMap_comp_generator M i r (r + m) hrm (φ k)).trans (hφ k)
  · simp only [← Linear.comp_smul, ← Preadditive.comp_sum]
    exact hm _ hrm le_rfl

end Linear

/-- Morphisms from a negative twist are degree-zero cohomology of the positive twist, linearly over
any specified structural ring map. -/
def negativeTwistHomLinearEquivH0 {A : Type u} [CommRing A]
    (α : A →+* Γ(ProjectiveSpace R ι, ⊤)) (d : ℤ) (M : (ProjectiveSpace R ι).Modules) :
    letI := moduleCategoryLinearOfHom (ProjectiveSpace R ι) α
    letI := Scheme.Cohomology.moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α
      ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).obj M) 0
    (twistingSheaf R ι (-d) ⟶ M) ≃ₗ[A]
      Sheaf.H.{u + 1} (Scheme.Cohomology.moduleAddSheaf (ProjectiveSpace R ι)
        ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).obj M)) 0 :=
  (negativeTwistHomLinearEquivSections α d M).trans
    (Scheme.Cohomology.moduleH0EquivOfHom (ProjectiveSpace R ι) α _).symm

end AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry.Scheme.Cohomology

/-- **Nitsure's Lemma 3.2 over an affine base, flat form** (arXiv:math/0504590v1, p. 15): for a
quasicoherent module `F` on projective space over a commutative ring `R` with finitely many
coordinates, if `H^0(P^n_R, F(d))` is a flat `R`-module for every `d ≥ N`, then `F` is relatively
flat over `Spec R`. Here `F(d) = 𝒪(d) ⊗ F`. -/
theorem relativeFlat_of_flat_twistedSections {R : Type u} [CommRing R] {ι : Type u} [Finite ι]
    (F : (ProjectiveSpace R ι).Modules) [F.IsQuasicoherent] (N : ℤ)
    (hflat : ∀ d : ℤ, N ≤ d →
      (let α := (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
       letI := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α
         ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).obj F) 0
       Module.Flat R (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
         ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).obj F)) 0))) :
    relativeFlat (toSpec R ι) F := by
  let α := (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  let := moduleCategoryLinearOfHom (ProjectiveSpace R ι) α
  have hhom (r : ℕ) (hr : N.toNat ≤ r) :
      Module.Flat R (twistingSheaf R ι (-(r : ℤ)) ⟶ F) := by
    let := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α
      ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι r)).obj F) 0
    exact (Module.Flat.equiv_iff (negativeTwistHomLinearEquivH0 α (r : ℤ) F)).mpr
      (hflat r (by omega))
  apply relativeFlat_of_flat_affineOpen_sections (toSpec R ι) F
  intro x
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (show x ∈ iSup (coordinateOpen R ι) by
      rw [iSup_coordinateOpen_eq_top]
      trivial)
  exact ⟨coordinateOpen R ι i, isAffineOpen_coordinateOpen R ι i, hi,
    flat_coordinateOpen_sections_of_flat_negativeTwistHom α F i N.toNat hhom⟩

/-- **Nitsure's Lemma 3.2 over an affine base** (arXiv:math/0504590v1, p. 15): if
`H^0(P^n_R, F(d))` is a projective `R`-module for every `d ≥ N`, then `F` is relatively flat over
`Spec R`. -/
theorem relativeFlat_of_projective_twistedSections {R : Type u} [CommRing R] {ι : Type u}
    [Finite ι] (F : (ProjectiveSpace R ι).Modules) [F.IsQuasicoherent] (N : ℤ)
    (hproj : ∀ d : ℤ, N ≤ d →
      (let α := (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
       letI := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α
         ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).obj F) 0
       Module.Projective R (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
         ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).obj F)) 0))) :
    relativeFlat (toSpec R ι) F :=
  relativeFlat_of_flat_twistedSections F N fun d hd => by
    have h := hproj d hd
    intro α
    exact @Module.Flat.of_projective _ _ _ _
      (moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α _ 0) h

/-- **Nitsure's Lemma 3.2 with its converse** (arXiv:math/0504590v1, Lemma 3.2 and the exercise
after it, p. 15), over an affine Noetherian base: a coherent module `F` on `P^n_R` is relatively
flat over `Spec R` if and only if `H^0(P^n_R, F(d))` is a projective `R`-module for all
sufficiently large `d`. -/
theorem relativeFlat_iff_exists_projective_twistedSections {R : Type u} [CommRing R]
    [IsNoetherianRing R] {ι : Type u} (n : ℕ) (e : ι ≃ Fin (n + 1))
    (F : (ProjectiveSpace R ι).Modules) (hF : affineLocallyFiniteType (ProjectiveSpace R ι) F) :
    relativeFlat (toSpec R ι) F ↔ ∃ N : ℤ, ∀ d : ℤ, N ≤ d →
      (let α := (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
       letI := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α
         ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).obj F) 0
       Module.Projective R (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
         ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).obj F)) 0)) := by
  constructor
  · intro hflat
    obtain ⟨B, hB⟩ := exists_twist_baseChange_isIso_and_projective_of_relativeFlat n e F hF hflat
    exact ⟨B, fun d hd => (hB d hd).2⟩
  · rintro ⟨N, hN⟩
    have : Finite ι := Finite.of_equiv _ e.symm
    let : F.IsQuasicoherent := quasicoherent_of_affineCharts F (fun A j _ => (hF A j).1)
    exact relativeFlat_of_projective_twistedSections F N hN

end AlgebraicGeometry.Scheme.Cohomology
