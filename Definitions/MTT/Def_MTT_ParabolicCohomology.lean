module

public import Definitions.MTT.Def_MTT_Cohomology
public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

@[expose] public section publicSection

noncomputable section

/-!
# The MTT symmetric-power coefficient representation

The substitution calculations are adapted from allychan327's accepted Prove2Me
reflection-class proof b65c560e-ff07-4802-bc88-856b821148e6. No resource-limit
settings or unrelated parts of that submission are imported.
-/


namespace MTT.Cohomology

open MvPolynomial

variable {R : Type*} [CommRing R]

private lemma act_eq_bind (A : Matrix (Fin 2) (Fin 2) ℤ) (P : Binary R) :
    act A P = MvPolynomial.bind₁ (fun i : Fin 2 =>
      ∑ a : Fin 2, (A a i : R) • MvPolynomial.X a) P := rfl

@[simp] theorem act_one (P : Binary R) : act 1 P = P := by
  rw [act_eq_bind]
  have h : (fun i : Fin 2 => ∑ a : Fin 2,
      ((1 : Matrix (Fin 2) (Fin 2) ℤ) a i : R) • MvPolynomial.X a) =
      fun i : Fin 2 => (MvPolynomial.X i : Binary R) := by
    funext i
    rw [Fin.sum_univ_two]
    fin_cases i <;> simp [Matrix.one_apply]
  rw [h, MvPolynomial.bind₁_X_left, AlgHom.id_apply]

/-- Substituting linear forms respects multiplication of the coefficient matrices. -/
theorem act_matrix_mul (A B : Matrix (Fin 2) (Fin 2) ℤ) (P : Binary R) :
    act (A * B) P = act A (act B P) := by
  simp only [act_eq_bind]
  rw [MvPolynomial.bind₁_bind₁]
  congr 2
  funext i
  rw [map_sum]
  simp only [map_smul, MvPolynomial.bind₁_X_right, Fin.sum_univ_two, Matrix.mul_apply]
  match_scalars <;> ring

/-- A substitution by linear forms preserves the homogeneous degree. -/
theorem act_mem_sym (A : Matrix (Fin 2) (Fin 2) ℤ) {n : ℕ} {P : Binary R}
    (hP : P ∈ Sym R n) : act A P ∈ Sym R n := by
  have hg (i : Fin 2) :
      (∑ a : Fin 2, (A a i : R) • MvPolynomial.X a : Binary R).IsHomogeneous 1 := by
    change _ ∈ Sym R 1
    exact (Sym R 1).sum_mem fun a _ => (Sym R 1).smul_mem _ (isHomogeneous_X _ _)
  change (MvPolynomial.aeval (fun i : Fin 2 =>
    (∑ a : Fin 2, (A a i : R) • MvPolynomial.X a : Binary R)) P).IsHomogeneous n
  simpa only [one_mul] using hP.aeval
    (fun i : Fin 2 => ∑ a : Fin 2, (A a i : R) • MvPolynomial.X a) hg

/-- The MTT left action on homogeneous binary forms as a mathlib representation. -/
def symRepresentation (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (n : ℕ) (R : Type*) [CommRing R] : Rep R Γ :=
  Rep.of
    { toFun := fun γ =>
        { toFun := fun P : Sym R n => ⟨act γ.val.val P.val, act_mem_sym _ P.property⟩
          map_add' := fun P Q => Subtype.ext (map_add _ P.val Q.val)
          map_smul' := fun a P => Subtype.ext (map_smul _ a P.val) }
      map_one' := by
        apply LinearMap.ext
        intro P
        exact Subtype.ext (act_one P.val)
      map_mul' := by
        intro γ δ
        apply LinearMap.ext
        intro P
        exact Subtype.ext (act_matrix_mul γ.val.val δ.val.val P.val) }

end MTT.Cohomology

/-!
# Parabolic group cohomology for the MTT coefficient module

The one-cocycles and principal coboundaries are mathlib's existing definitions.
The parabolic subspace requires the value at every cusp-fixing element to lie
in the image of that element minus the identity. This is the definition in
Columbia's Spring 2021 Eichler–Shimura seminar notes, §1.1, specialized to the
rational cusps of Gamma1(N).
-/


namespace MTT.Cohomology

open groupCohomology

abbrev gammaOneRep (N n : ℕ) := symRepresentation (CongruenceSubgroup.Gamma1 N) n ℂ

/-- Cocycles whose restrictions to cyclic cusp stabilizers are principal. -/
def parabolicCocycles (N n : ℕ) :
    Submodule ℂ (CongruenceSubgroup.Gamma1 N → gammaOneRep N n) :=
  cocycles₁ (gammaOneRep N n) ⊓
    ⨅ (x : Cusp) (γ : CongruenceSubgroup.Gamma1 N) (_ : cuspAct γ.val x = x),
      (LinearMap.range ((gammaOneRep N n).ρ γ - LinearMap.id)).comap (LinearMap.proj γ)

/-- The principal coboundaries regarded as a submodule of parabolic cocycles. -/
def parabolicCoboundaries (N n : ℕ) : Submodule ℂ (parabolicCocycles N n) :=
  (coboundaries₁ (gammaOneRep N n)).comap (parabolicCocycles N n).subtype

/-- The first parabolic cohomology is the cocycle space modulo principal coboundaries. -/
abbrev ParabolicH1 (N n : ℕ) :=
  parabolicCocycles N n ⧸ parabolicCoboundaries N n

theorem mem_parabolicCocycles_iff {N n : ℕ}
    (c : CongruenceSubgroup.Gamma1 N → gammaOneRep N n) :
    c ∈ parabolicCocycles N n ↔
      (∀ γ δ, c (γ * δ) = (gammaOneRep N n).ρ γ (c δ) + c γ) ∧
      ∀ (x : Cusp) (γ : CongruenceSubgroup.Gamma1 N), cuspAct γ.val x = x →
        ∃ Q : gammaOneRep N n, c γ = (gammaOneRep N n).ρ γ Q - Q := by
  simp only [parabolicCocycles, Submodule.mem_inf, mem_cocycles₁_iff,
    Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mem_range,
    LinearMap.sub_apply, LinearMap.id_apply, LinearMap.proj_apply, eq_comm]

theorem mem_parabolicCoboundaries_iff {N n : ℕ} (c : parabolicCocycles N n) :
    c ∈ parabolicCoboundaries N n ↔
      ∃ P : gammaOneRep N n, ∀ γ, c.val γ = (gammaOneRep N n).ρ γ P - P := by
  simp only [parabolicCoboundaries, Submodule.mem_comap, coboundaries₁,
    LinearMap.mem_range, Submodule.coe_subtype, funext_iff, d₀₁_hom_apply, eq_comm]

/-- Every principal cocycle satisfies all parabolic restrictions. -/
theorem coboundaries_le_parabolicCocycles (N n : ℕ) :
    coboundaries₁ (gammaOneRep N n) ≤ parabolicCocycles N n := by
  rintro c ⟨P, rfl⟩
  apply (mem_parabolicCocycles_iff _).mpr
  refine ⟨(mem_cocycles₁_iff _).mp (d₀₁_apply_mem_cocycles₁ P), ?_⟩
  intro x γ hx
  exact ⟨P, rfl⟩

end MTT.Cohomology

end

end publicSection
