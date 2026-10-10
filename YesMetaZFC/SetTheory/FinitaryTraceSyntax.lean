import YesMetaZFC.SetTheory.FinitaryHull

/-! # 带固定种子的最小闭包与交集见证

固定参数集合 A 与变化的种子 Y 一起生成最小有限元闭包 N。交集见证记录
Y=N∩X 及 N 的内部可数性，后续 club 闭性使用最小性同步提升整条内部链。
-/

namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Fc_seed_d (ω H T K A Y N : M.Domain) : Prop :=
  M.MemberSubset A N ∧ M.MemberSubset Y N ∧ M.MemberSubset N H ∧ Fc_closed_d I ω T K N ∧
    ∀ B, M.MemberSubset A B → M.MemberSubset Y B → Fc_closed_d I ω T K B → M.MemberSubset N B

def fc_seed_m {d} (ω H T K A Y N : Term d) : Formula 1 d :=
  .conj (Formula.subset A N) (.conj (Formula.subset Y N) (.conj (Formula.subset N H)
    (.conj (fc_closed_m (𝒞 := 𝒞) ω T K N) (.forallE (.imp (Formula.subset A.weaken .newest)
      (.imp (Formula.subset Y.weaken .newest) (.imp (fc_closed_m (𝒞 := 𝒞) ω.weaken T.weaken K.weaken .newest)
        (Formula.subset N.weaken .newest))))))))
derive_free_closed fc_seed_m

theorem fc_seed_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω H T K A Y N : Term d) :
    Formula.satisfies ρ (fc_seed_m (𝒞 := 𝒞) ω H T K A Y N) ↔
      Fc_seed_d I (ω.eval ρ) (H.eval ρ) (T.eval ρ) (K.eval ρ) (A.eval ρ) (Y.eval ρ) (N.eval ρ) := by
  simp only [fc_seed_m, Fc_seed_d, Formula.satisfies_conj_iff, Formula.satisfies_subset_iff,
    fc_closed_sat_l I hE, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Definitional.Term.eval_weaken]
  rfl

theorem fc_seed_mono_l {ω H T K A Y Z N L} (hN : Fc_seed_d I ω H T K A Y N)
    (hL : Fc_seed_d I ω H T K A Z L) (hYZ : M.MemberSubset Y Z) : M.MemberSubset N L :=
  hN.2.2.2.2 L hL.1 (fun x hx => hL.2.1 x (hYZ x hx)) hL.2.2.2.1

theorem fc_seed_unique_l (hE : Extensional M) {ω H T K A Y N L}
    (hN : Fc_seed_d I ω H T K A Y N) (hL : Fc_seed_d I ω H T K A Y L) : N = L :=
  hE.eq_of_same_members N L (fun x => ⟨fc_seed_mono_l I hN hL (fun _ h => h) x,
    fc_seed_mono_l I hL hN (fun _ h => h) x⟩)

theorem ZF.fc_seed_exists_l (hZF : M.Models ZF) {ω H T D K A Y} (hω : M.IsOmega ω)
    (hK : M.IsSetFunctionFromTo I K D H) (hA : M.MemberSubset A H) (hY : M.MemberSubset Y H) :
    ∃ N, Fc_seed_d I ω H T K A Y N := by
  obtain ⟨B, hB⟩ := KP.exists_unionOfTwo (modelsKP hZF) A Y
  obtain ⟨_, _, N, _, _, _, _, _, hn⟩ := fc_hull_chain_l I hZF hω hK
    (fun x hx => ((hB x).mp hx).elim (hA x) (hY x))
  exact ⟨N, (fun x hx => hn.1 x ((hB x).mpr (Or.inl hx))),
    (fun x hx => hn.1 x ((hB x).mpr (Or.inr hx))), hn.2.1, hn.2.2.1,
    fun C hAC hYC hc => hn.2.2.2 C (fun x hx => ((hB x).mp hx).elim (hAC x) (hYC x)) hc⟩

def Fc_trace_d (ω H T K A X Y N : M.Domain) : Prop :=
  Fc_seed_d I ω H T K A Y N ∧ M.CardinalLessOrEqual I N ω ∧
    ∀ x, M.mem x Y ↔ M.mem x N ∧ M.mem x X

def fc_trace_m {d} (ω H T K A X Y N : Term d) : Formula 1 d :=
  .conj (fc_seed_m (𝒞 := 𝒞) ω H T K A Y N) (.conj (Formula.cardinalLessOrEqual 𝒞 N ω)
    (.forallE (.iff (.mem .newest Y.weaken) (.conj (.mem .newest N.weaken) (.mem .newest X.weaken)))))
derive_free_closed fc_trace_m

theorem fc_trace_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω H T K A X Y N : Term d) :
    Formula.satisfies ρ (fc_trace_m (𝒞 := 𝒞) ω H T K A X Y N) ↔
      Fc_trace_d I (ω.eval ρ) (H.eval ρ) (T.eval ρ) (K.eval ρ) (A.eval ρ) (X.eval ρ) (Y.eval ρ) (N.eval ρ) := by
  simp only [fc_trace_m, Fc_trace_d, Formula.satisfies_conj_iff, fc_seed_sat_l I hE,
    Formula.satisfies_cardinalLessOrEqual_iff I hE, Formula.satisfies_forall_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, Definitional.Term.eval_weaken]
  rfl

end YesMetaZFC.SetTheory
