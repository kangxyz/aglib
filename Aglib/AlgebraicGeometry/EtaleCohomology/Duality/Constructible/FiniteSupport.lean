/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Ext.Concentration
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.PointPresentation
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.LocallyConstantPerfectness
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.LowerShriekDirectImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.ClosedExactness
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.DegreeZero

/-!
# Constructible coefficients on the actual finite point scheme

The source is the original finite closed direct image. Compact degree zero
retains its existing ZMod action; its positive degrees vanish for every
coefficient on the point scheme. Original finite-unit presentations and their
constructible kernels give uniform source concentration and the original
trace-pairing adjoint in degree two. The unit base is the full finite-point
pairing, rather than a cyclic diagonal or an isomorphism of the total sum trace.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u v wU wX wA

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients Curves.FiniteClosedSupport Scheme.OverField

attribute [local instance] hasSheafifyLarge hasSheafifyModules ModuleCat.Sheaf.hasSheafify
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard moduleSheafExtZModModule
  moduleSheaf_hasFiniteBiproducts

section CompactMaps

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : Set U) (n : ℕ)
  [HasExt.{wX} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]

/-- The literal original compact coefficient map, on its original
ZMod actions. No coefficient or cohomology carrier is bundled again. -/
private def moduleFiniteSupportCompactMap
    {M M' : ModuleSheaf (pointScheme U T) (ULift.{u + 1} (ZMod n))} (f : M ⟶ M') (q : ℕ) :
    Ext.{wX} (moduleUnit X (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).obj
        ((moduleDirectImage (inclusion U T) (ULift.{u + 1} (ZMod n))).obj M)) q →ₗ[ZMod n]
      Ext.{wX} (moduleUnit X (ULift.{u + 1} (ZMod n)))
        ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).obj
          ((moduleDirectImage (inclusion U T) (ULift.{u + 1} (ZMod n))).obj M')) q :=
  AddMonoidHom.toZModLinearMap n
    ((Ext.mk₀ ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).map
      ((moduleDirectImage (inclusion U T) (ULift.{u + 1} (ZMod n))).map f))).postcomp
        (moduleUnit X (ULift.{u + 1} (ZMod n))) (add_zero q))

end CompactMaps

section CurveSupport

variable {k : Type u} [Field k] [IsAlgClosed k] (X : FScheme k) (hX : Curve.Properties X)
  {U : Scheme.{u}} (j : U ⟶ X.left) [IsOpenImmersion j]
  (T : Set U) (hTfin : T.Finite) (hTclosed : ∀ x ∈ T, IsClosed ({x} : Set U))
  (n : ℕ)
  [HasExt.{wX} (ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))]

include hX j hTclosed in
private theorem finiteSupport_residue_isSepClosed (x : T) :
    IsSepClosed (U.residueField x.val) := by
  let := Curve.curveProperties_locallyOfFiniteType hX
  let : LocallyOfFiniteType (j ≫ X.hom) := inferInstance
  let := residueAlgebra U (j ≫ X.hom) x.val
  let : Module.Finite k (U.residueField x.val) :=
    residue_finite U (j ≫ X.hom) ⟨x.val, hTclosed x.val x.property⟩
  exact Algebra.IsAlgebraic.isSepClosed (F := k)

include hX hTfin hTclosed in
/-- Every actual coefficient on the finite point scheme has zero positive
compact cohomology. Constructibility is not needed for this vanishing. -/
theorem moduleFiniteSupportC_pos_subsingleton
    (M : ModuleSheaf (pointScheme U T) (ULift.{u + 1} (ZMod n)))
    (q : ℕ) (hq : 0 < q) :
    Subsingleton (Ext.{wX} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).obj
        ((moduleDirectImage (inclusion U T) (ULift.{u + 1} (ZMod n))).obj M)) q) := by
  exact moduleLowerShriekDirectImage_subsingleton_of_sepClosed j
    (ULift.{u + 1} (ZMod n)) T hTfin
    (fun x hx => modulePoint_image_isClosed hX j ⟨x, hTclosed x hx⟩)
    (finiteSupport_residue_isSepClosed X hX j T hTclosed) M q hq

include hX hTfin hTclosed in
/-- The SAME compact degree-zero functor is exact on actual point coefficients,
by the original compact Ext sequence and positive supported vanishing. -/
private theorem moduleFiniteSupportC0_shortExact
    {S : ShortComplex (ModuleSheaf (pointScheme U T) (ULift.{u + 1} (ZMod n)))}
    (hS : S.ShortExact) (q : ℕ) (hq : q = 0) :
    Function.Injective (moduleFiniteSupportCompactMap j T n S.f q) ∧
      Function.Exact (moduleFiniteSupportCompactMap j T n S.f q) (moduleFiniteSupportCompactMap j
        T n S.g q) ∧
      Function.Surjective (moduleFiniteSupportCompactMap j T n S.g q) := by
  subst q
  let Λ := ULift.{u + 1} (ZMod n)
  let A := moduleUnit X.left Λ
  let J := moduleDirectImage (inclusion U T) Λ
  let L := moduleLowerShriek j Λ
  let : IsClosedImmersion (inclusion U T) := inclusion_isClosedImmersion U T hTfin hTclosed
  have hJ := shortExact_finiteModuleDirectImage Λ (inclusion U T) hS
  have hL := shortExact_moduleLowerShriek j Λ hJ
  dsimp only [ShortComplex.map] at hL
  let : Mono ((J ⋙ L).map S.f) := hL.mono_f
  let := moduleFiniteSupportC_pos_subsingleton X hX j T hTfin hTclosed n S.X₁ 1 (by decide)
  have hi : Function.Injective
      (moduleFiniteSupportCompactMap j T n S.f 0) :=
    Ext.postcomp_mk₀_injective_of_mono A ((J ⋙ L).map S.f)
  have he : Function.Exact
      (moduleFiniteSupportCompactMap j T n S.f 0)
      (moduleFiniteSupportCompactMap j T n S.g 0) := by
    have h := Ext.covariant_sequence_exact₂' A hL 0
    rw [ShortComplex.ab_exact_iff_function_exact] at h
    exact h
  have hg : Function.Surjective
      (moduleFiniteSupportCompactMap j T n S.g 0) := by
    intro c
    obtain ⟨b, hb⟩ := Ext.covariant_sequence_exact₃ A hL c
      (show 0 + 1 = 1 from rfl) (Subsingleton.elim _ _)
    exact ⟨b, hb⟩
  exact ⟨hi, he, hg⟩


include hX hTfin hTclosed in
/-- Original compact degree zero is the original point-scheme sections group.
The comparison uses the SAME coefficient equivalence and original evaluation
at the terminal etale chart; its target keeps the original coefficient action. -/
def moduleFiniteSupportC0SectionsAddEquiv
    (M : ModuleSheaf (pointScheme U T) (ULift.{u + 1} (ZMod n))) :
    Ext.{wX} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).obj
        ((moduleDirectImage (inclusion U T) (ULift.{u + 1} (ZMod n))).obj M)) 0 ≃+
      (Constructible.Modules.moduleGlobalSections (ULift.{u + 1} (ZMod n))
        (pointScheme U T)).obj
          ((moduleSheafEquivalence (pointScheme U T) (ULift.{u + 1} (ZMod n))).inverse.obj M) := by
  let Λ := ULift.{u + 1} (ZMod n)
  let Z := pointScheme U T
  let E := moduleSheafEquivalence Z Λ
  let F := E.inverse.obj M
  let Q := SheafOfModules.toSheaf (constantRing Z Λ)
  let : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} X.left) := hasExtStandard X.left
  let : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} Z) := hasExtStandard Z
  let := CompactSupport.isClosedImmersion_inclusion_comp j T hTfin
    (fun x hx => modulePoint_image_isClosed hX j ⟨x, hTclosed x hx⟩)
  let e : Q.obj M ≅ (Constructible.Modules.moduleUnderlying Λ Z).obj F :=
    (Q.mapIso (E.counitIso.app M)).symm ≪≫ (moduleSheafUnderlyingIso Z Λ).app F
  let e₀ := ((sheafToPresheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}).mapIso e).app
    (Opposite.op (etaleTerminal Z))
  exact (moduleLowerShriekDirectImageAddEquiv.{wX, u + 2, u + 2}
      j (inclusion U T) Λ M 0).trans
    ((Sheaf.H.equiv₀ (Q.obj M) (etaleTerminalIsTerminal Z)).trans
      e₀.addCommGroupIsoToAddEquiv)

include hX hTfin hTclosed in
/-- Constructible finite support has finite original compact degree zero.
Only finite generation over the original finite coefficient ring is used. -/
theorem moduleFiniteSupportC0_finite (hn : 0 < n)
    (M : ModuleSheaf (pointScheme U T) (ULift.{u + 1} (ZMod n)))
    (hM : Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence (pointScheme U T) (ULift.{u + 1} (ZMod n))).inverse.obj M)) :
    Finite (Ext.{wX} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).obj
        ((moduleDirectImage (inclusion U T) (ULift.{u + 1} (ZMod n))).obj M)) 0) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let : Finite T := hTfin.to_subtype
  let Λ := ULift.{u + 1} (ZMod n)
  let Z := pointScheme U T
  let F := (moduleSheafEquivalence Z Λ).inverse.obj M
  let : Module.Finite Λ ((Constructible.Modules.moduleGlobalSections Λ Z).obj F) :=
    Constructible.Modules.modulePointGlobalSections_finite Λ U T
      (finiteSupport_residue_isSepClosed X hX j T hTclosed) F hM
  let : Finite ((Constructible.Modules.moduleGlobalSections Λ Z).obj F) :=
    Module.finite_of_finite Λ
  exact Finite.of_injective (moduleFiniteSupportC0SectionsAddEquiv X hX j T hTfin hTclosed n M)
    (moduleFiniteSupportC0SectionsAddEquiv X hX j T hTfin hTclosed n M).injective

end CurveSupport

section SourceConcentration

variable {k : Type u} [Field k] [IsAlgClosed k] (X : FScheme k) (hX : Curve.Properties X)
  (D : Set X.left) (hfin : D.Finite) (hclosed : ∀ x ∈ D, IsClosed ({x} : Set X.left))
  {U : Scheme.{u}} (j : U ⟶ X.left) [IsOpenImmersion j] (hD : Set.range j = Dᶜ)
  (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) (hinv : IsUnit (n : Γ(X.left, ⊤)))
  [HasExt.{wU} (ModuleSheaf U (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wX} (ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wA} (AbelianSheaf.{u, u + 1} X.left)]
  (T : Set U) (hTfin : T.Finite) (hTclosed : ∀ x ∈ T, IsClosed ({x} : Set U))

omit [HasExt.{wX} (ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wA} (AbelianSheaf.{u, u + 1} X.left)] in
include hX j hn hunit hTfin hTclosed in
private theorem finitePointUnit_ext_subsingleton (q : ℕ) (hq : q ≠ 2) :
    Subsingleton (Ext.{wU} (moduleFinitePointSource U T n) (moduleRootsOfUnity U n) q) := by
  let : Finite T := hTfin.to_subtype
  let (x : T) : Subsingleton (Ext.{wU}
      ((moduleDirectImage (U.fromSpecResidueField x.val) (ULift.{u + 1} (ZMod n))).obj
        (moduleUnit (Spec (U.residueField x.val)) (ULift.{u + 1} (ZMod n))))
      (moduleRootsOfUnity U n) q) := by
    by_cases hq0 : q = 0
    · subst q
      exact moduleOpenPointExt_zero_subsingleton hX j ⟨x.val, hTclosed x.val x.property⟩ n hn hunit
    by_cases hq1 : q = 1
    · subst q
      exact moduleOpenPointExt_one_subsingleton hX j ⟨x.val, hTclosed x.val x.property⟩ n hn hunit
    exact moduleOpenPointExt_high_subsingleton hX j
      ⟨x.val, hTclosed x.val x.property⟩ n hn hunit q (by omega)
  exact (moduleFinitePointExtAddEquiv U T n hTclosed
    (moduleRootsOfUnity U n) q).injective.subsingleton

omit [HasExt.{wX} (ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wA} (AbelianSheaf.{u, u + 1} X.left)] in
include hX j hn hunit hTfin hTclosed in
private theorem finitePointPower_ext_subsingleton (m q : ℕ) (hq : q ≠ 2) :
    Subsingleton (Ext.{wU}
      ((moduleDirectImage (inclusion U T) (ULift.{u + 1} (ZMod n))).obj
        (⨁ fun _ : Fin m => moduleUnit (pointScheme U T) (ULift.{u + 1} (ZMod n))))
      (moduleRootsOfUnity U n) q) := by
  let J := moduleDirectImage (inclusion U T) (ULift.{u + 1} (ZMod n))
  let B := fun _ : Fin m => moduleUnit (pointScheme U T) (ULift.{u + 1} (ZMod n))
  let (a : Fin m) : Subsingleton (Ext.{wU} ((J.obj ∘ B) a) (moduleRootsOfUnity U n) q) :=
    finitePointUnit_ext_subsingleton X hX j n hn hunit T hTfin hTclosed q hq
  exact (Ext.biproductAddEquiv
    (Functor.mapFiniteBiconeIsBilimit J (biproduct.isBilimit B))
    (moduleRootsOfUnity U n) q).injective.subsingleton

/-- Apply the existing whole pairing law while its original bicone remains
variable; specialize the actual mapped point-unit bicone only afterward. -/
private theorem finiteSupport_bicone_zero_isPerfPair
    {I : Type v} [Finite I]
    {F : I → ModuleSheaf U (ULift.{u + 1} (ZMod n))} {b : Bicone F} (hb : b.IsBilimit)
    (hF : ∀ a, (moduleDualityMap.{u, wU, wX, wA}
      X hX D hfin hclosed j hD n hn hunit hinv (F a) 0 (by decide)).IsPerfPair) :
    (moduleDualityMap.{u, wU, wX, wA}
      X hX D hfin hclosed j hD n hn hunit hinv b.pt 0 (by decide)).IsPerfPair := by
  unfold moduleDualityMap moduleTracePairingLinearMap at hF ⊢
  exact Functor.isPerfPair_extPairingLinearMap_compr₂_biproduct.{
      u + 2, u + 1, u + 2, u + 1, wU, wX, v}
    (moduleLowerShriek j (ULift.{u + 1} (ZMod n)))
    (moduleUnit X.left (ULift.{u + 1} (ZMod n))) n hb (moduleRootsOfUnity U n)
    0 2 2 rfl (moduleCompactSupportTraceLinearMap X hX D hfin hclosed j hD n hn hunit hinv) hF

include hTfin hTclosed in
private theorem finitePointPower_zero_isPerfPair (m : ℕ) :
    (moduleDualityMap.{u, wU, wX, wA} X hX D hfin hclosed j hD n hn hunit hinv
      ((moduleDirectImage (inclusion U T) (ULift.{u + 1} (ZMod n))).obj
        (⨁ fun _ : Fin m => moduleUnit (pointScheme U T) (ULift.{u + 1} (ZMod n))))
      0 (by decide)).IsPerfPair := by
  let J := moduleDirectImage (inclusion U T) (ULift.{u + 1} (ZMod n))
  let B := fun _ : Fin m => moduleUnit (pointScheme U T) (ULift.{u + 1} (ZMod n))
  have hF : ∀ a : Fin m, (moduleDualityMap.{u, wU, wX, wA}
      X hX D hfin hclosed j hD n hn hunit hinv ((J.obj ∘ B) a) 0 (by decide)).IsPerfPair :=
    fun _ => moduleDualityMap_finitePoint_isPerfPair.{u, wU, wX, wA}
      X hX D hfin hclosed j hD n hn hunit hinv T hTfin hTclosed 0 (by decide)
  have hb := Functor.mapFiniteBiconeIsBilimit J (biproduct.isBilimit B)
  have hpair := finiteSupport_bicone_zero_isPerfPair
    X hX D hfin hclosed j hD n hn hunit hinv hb hF
  have hpt : (J.mapBicone (biproduct.bicone B)).pt = J.obj (⨁ B) := rfl
  have ht := congrArg (fun F : ModuleSheaf U (ULift.{u + 1} (ZMod n)) =>
    (moduleDualityMap.{u, wU, wX, wA} X hX D hfin hclosed j hD n hn hunit hinv
      F 0 (by decide)).IsPerfPair) hpt
  exact ht.mp hpair

/-- Evaluate the original transpose/flip identification while its coefficient
remains variable, before inserting an actual finite unit power. -/
private theorem finiteSupportTranspose_bijective_of_zero_isPerfPair
    (F : ModuleSheaf U (ULift.{u + 1} (ZMod n)))
    (hF : (moduleDualityMap.{u, wU, wX, wA}
      X hX D hfin hclosed j hD n hn hunit hinv F 0 (by decide)).IsPerfPair) :
    Function.Bijective (moduleDualityTransposeMap.{u, wU, wX, wA}
      X hX D hfin hclosed j hD n hn hunit hinv F 2 le_rfl).toAddMonoidHom := by
  change Function.Bijective (moduleDualityMap.{u, wU, wX, wA}
    X hX D hfin hclosed j hD n hn hunit hinv F 0 (by decide)).flip
  exact hF.bijective_right

include hTfin hTclosed in
/-- Actual constructible finite support has the original bijective degree-two
transpose, and its original source Ext vanishes in EVERY other degree. -/
theorem moduleFiniteSupport_concentration
    (M : ModuleSheaf (pointScheme U T) (ULift.{u + 1} (ZMod n)))
    (hM : Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence (pointScheme U T) (ULift.{u + 1} (ZMod n))).inverse.obj M)) :
    Function.Bijective (moduleDualityTransposeMap.{u, wU, wX, wA}
      X hX D hfin hclosed j hD n hn hunit hinv
      ((moduleDirectImage (inclusion U T) (ULift.{u + 1} (ZMod n))).obj M) 2 le_rfl) ∧
    ∀ q, q ≠ 2 → Subsingleton (Ext.{wU}
      ((moduleDirectImage (inclusion U T) (ULift.{u + 1} (ZMod n))).obj M)
      (moduleRootsOfUnity U n) q) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let : Finite T := hTfin.to_subtype
  let : IsClosedImmersion (inclusion U T) := inclusion_isClosedImmersion U T hTfin hTclosed
  let Λ := ULift.{u + 1} (ZMod n)
  let Z := pointScheme U T
  let J := moduleDirectImage (inclusion U T) Λ
  let L := moduleLowerShriek j Λ
  let A := moduleUnit X.left Λ
  let H := fun F : ModuleSheaf Z Λ => Ext.{wX} A (L.obj (J.obj F)) (2 - 2)
  let hAdd : ∀ F, AddCommGroup (H F) := fun F =>
    inferInstanceAs (AddCommGroup (Ext.{wX} A (L.obj (J.obj F)) (2 - 2)))
  let hScalar : ∀ F, Module (ZMod n) (H F) := fun F =>
    moduleSheafExtZModModule n A (L.obj (J.obj F)) (2 - 2)
  let Hmap {F F' : ModuleSheaf Z Λ} (a : F ⟶ F') :=
    moduleFiniteSupportCompactMap j T n a (2 - 2)
  let P := fun F : ModuleSheaf Z Λ => Constructible.Modules.IsConstructible
    ((moduleSheafEquivalence Z Λ).inverse.obj F)
  let B := fun m : ℕ => ⨁ fun _ : Fin m => moduleUnit Z Λ
  let ν := fun F : ModuleSheaf Z Λ =>
    (moduleDualityTransposeMap.{u, wU, wX, wA}
      X hX D hfin hclosed j hD n hn hunit hinv (J.obj F) 2 le_rfl).toAddMonoidHom
  have hJ : ∀ S : ShortComplex (ModuleSheaf Z Λ), S.ShortExact → (S.map J).ShortExact :=
    fun _ hS => shortExact_finiteModuleDirectImage Λ (inclusion U T) hS
  have hH : ∀ S : ShortComplex (ModuleSheaf Z Λ), S.ShortExact →
      Function.Injective (Hmap S.f) ∧ Function.Exact (Hmap S.f) (Hmap S.g) ∧
        Function.Surjective (Hmap S.g) :=
    fun _ hS => moduleFiniteSupportC0_shortExact X hX j T hTfin hTclosed n hS (2 - 2) (by omega)
  have hP : ∀ F, P F → ∃ (m : ℕ) (a : B m ⟶ F), Epi a ∧ P (kernel a) := by
    intro F hF
    exact exists_modulePointUnitBiproduct_epi_constructible_kernel U T Λ
      (finiteSupport_residue_isSepClosed X hX j T hTclosed) F hF
  have hν : ∀ {F F' : ModuleSheaf Z Λ} (a : F ⟶ F') (e : Ext.{wU} (J.obj F')
      (moduleRootsOfUnity U n) 2) (c : Ext.{wX} (moduleUnit X.left Λ)
        ((moduleLowerShriek j Λ).obj (J.obj F)) (2 - 2)),
      ν F ((Ext.mk₀ (J.map a)).comp e (zero_add 2)) c = ν F' e (Hmap a c) := by
    intro F F' a e c
    have h := LinearMap.congr_fun (moduleDualityTransposeMap_naturality.{u, wU, wX, wA}
      X hX D hfin hclosed j hD n hn hunit hinv (J.map a) 2 le_rfl) e
    exact LinearMap.congr_fun h c
  have hB : ∀ m q, q ≠ 2 → Subsingleton (Ext.{wU} (J.obj (B m))
      (moduleRootsOfUnity U n) q) := fun m q hq =>
    finitePointPower_ext_subsingleton X hX j n hn hunit T hTfin hTclosed m q hq
  have hνB : ∀ m, Function.Bijective (ν (B m)) := by
    intro m
    have hpair := finitePointPower_zero_isPerfPair X hX D hfin hclosed j hD n hn hunit hinv
      T hTfin hTclosed m
    exact finiteSupportTranspose_bijective_of_zero_isPerfPair
      X hX D hfin hclosed j hD n hn hunit hinv _ hpair
  have h := @Ext.concentration_of_uniform_presentations
    (ModuleSheaf Z Λ) inferInstance inferInstance (ModuleSheaf U Λ)
    inferInstance inferInstance (inferInstanceAs (HasExt.{wU} (ModuleSheaf U Λ)))
    J inferInstance (moduleRootsOfUnity U n) n hn H hAdd hScalar Hmap
    hJ hH P ℕ B hP ν hν hB hνB
  exact ⟨h.1 M hM, h.2 M hM⟩


include hTfin hTclosed in
/-- The canonical degree-two comparison is the ORIGINAL transpose of the
trace pairing, on the original compact degree-zero linear dual. -/
def moduleFiniteSupportExtTwoAddEquiv
    (M : ModuleSheaf (pointScheme U T) (ULift.{u + 1} (ZMod n)))
    (hM : Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence (pointScheme U T) (ULift.{u + 1} (ZMod n))).inverse.obj M)) :
    Ext.{wU} ((moduleDirectImage (inclusion U T) (ULift.{u + 1} (ZMod n))).obj M)
      (moduleRootsOfUnity U n) 2 ≃+
      Module.Dual (ZMod n)
        (Ext.{wX} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
          ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).obj
            ((moduleDirectImage (inclusion U T) (ULift.{u + 1} (ZMod n))).obj M)) 0) :=
  (LinearEquiv.ofBijective
    (moduleDualityTransposeMap.{u, wU, wX, wA}
      X hX D hfin hclosed j hD n hn hunit hinv
      ((moduleDirectImage (inclusion U T) (ULift.{u + 1} (ZMod n))).obj M) 2 le_rfl)
    (moduleFiniteSupport_concentration X hX D hfin hclosed j hD n hn hunit hinv
      T hTfin hTclosed M hM).1).toAddEquiv

include hTfin hTclosed in
/-- Both original adjoints are bijective for every constructible coefficient
on the actual finite point scheme, including empty support and modulus one. -/
theorem moduleDualityMap_finiteSupport_isPerfPair
    (M : ModuleSheaf (pointScheme U T) (ULift.{u + 1} (ZMod n)))
    (hM : Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence (pointScheme U T) (ULift.{u + 1} (ZMod n))).inverse.obj M))
    (r : ℕ) (hr : r ≤ 2) :
    (moduleDualityMap.{u, wU, wX, wA} X hX D hfin hclosed j hD n hn hunit hinv
      ((moduleDirectImage (inclusion U T) (ULift.{u + 1} (ZMod n))).obj M) r hr).IsPerfPair := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have h := moduleFiniteSupport_concentration X hX D hfin hclosed j hD n hn hunit hinv
    T hTfin hTclosed M hM
  interval_cases r
  · let := moduleFiniteSupportC0_finite X hX j T hTfin hTclosed n hn M hM
    apply (ZMod.isPerfPair_iff_flip_bijective n _).mpr
    exact h.1
  · let := moduleFiniteSupportC_pos_subsingleton X hX j T hTfin hTclosed n M 1 (by decide)
    let := h.2 1 (by decide)
    exact ZMod.isPerfPair_of_subsingleton n _
  · let := moduleFiniteSupportC_pos_subsingleton X hX j T hTfin hTclosed n M 2 (by decide)
    let := h.2 0 (by decide)
    exact ZMod.isPerfPair_of_subsingleton n _

end SourceConcentration

end AlgebraicGeometry.Scheme.EtaleCohomology
