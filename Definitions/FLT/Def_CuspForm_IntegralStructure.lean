import Definitions.FLT.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

def CuspForm.intLattice (N : ℕ) (k : ℤ) : Submodule ℤ (CuspForm (CongruenceSubgroup.Gamma0 N) k) :=
  Submodule.span ℤ {f | ∀ n : ℕ, ∃ m : ℤ, ModularFormClass.qCoeff f n = (m : ℂ)}

def CuspForm.HasIntegralStructure (N : ℕ) (k : ℤ) : Prop :=
  Submodule.span ℂ ((CuspForm.intLattice N k : Submodule ℤ (CuspForm (CongruenceSubgroup.Gamma0 N) k)) :
    Set (CuspForm (CongruenceSubgroup.Gamma0 N) k)) = ⊤

