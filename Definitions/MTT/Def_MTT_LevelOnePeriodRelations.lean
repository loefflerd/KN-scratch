import Definitions.MTT.Def_MTT_ParabolicCohomology

/-! # The two Manin relations for the MTT left coefficient action -/

noncomputable section

namespace MTT.Cohomology

/-- At level one, every integral determinant-one matrix is in Gamma1. -/
def levelOneIncl : Matrix.SpecialLinearGroup (Fin 2) ℤ ≃* CongruenceSubgroup.Gamma1 1 where
  toFun g := ⟨g, by
    rw [CongruenceSubgroup.Gamma1_mem]
    exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
  invFun := Subtype.val
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Binary homogeneous polynomials satisfying the S and ST period relations. -/
def periodRelations (n : ℕ) : Submodule ℂ (gammaOneRep 1 n) :=
  LinearMap.ker ((gammaOneRep 1 n).ρ (levelOneIncl ModularGroup.S) + LinearMap.id) ⊓
    LinearMap.ker (
      ((gammaOneRep 1 n).ρ (levelOneIncl (ModularGroup.S * ModularGroup.T))) ^ 2 +
      (gammaOneRep 1 n).ρ (levelOneIncl (ModularGroup.S * ModularGroup.T)) + LinearMap.id)

theorem mem_periodRelations_iff {n : ℕ} (P : gammaOneRep 1 n) :
    P ∈ periodRelations n ↔
      (gammaOneRep 1 n).ρ (levelOneIncl ModularGroup.S) P + P = 0 ∧
      (gammaOneRep 1 n).ρ (levelOneIncl (ModularGroup.S * ModularGroup.T))
          ((gammaOneRep 1 n).ρ (levelOneIncl (ModularGroup.S * ModularGroup.T)) P) +
        (gammaOneRep 1 n).ρ (levelOneIncl (ModularGroup.S * ModularGroup.T)) P + P = 0 := by
  simp only [periodRelations, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.add_apply,
    LinearMap.id_apply, pow_two, Module.End.mul_apply]

end MTT.Cohomology

