import YesMetaZFC.Model.SetTheory.Demand.Reply
import YesMetaZFC.SetTheory.LargeCardinal.Game.RecoverySyntax

/-! # demanding 固定回答查询的低参数基底

三条查询在 {ω,A,k} 上一次编译，再扩大到回答的常量域。
原 Q 行保存同一份基底证书，故查询码的秩与随后选择的 τ 无关。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Td_reply_base_d (ω A e k q n m pp pb ph : M.Domain) : Prop := ∃ U D,
  (∀ x, M.mem x U ↔ x = ω ∨ x = A ∨ x = k ∨ x = k) ∧ Tt_pool_d I ω m U D ∧
    Td_pending_query_d I ω A e m q U D k pp ∧
    Tg_bound_query_d I ω e n m U D pb ∧ Tg_height_query_d I ω n m U D ph

def td_reply_base_m {d} (ω A e k q n m pp pb ph : Term d) : Formula 1 d := set[d] ⟪∃ U D,
  ⌜tq_basis_m⌝ₚ(⌜ω⌝ₛ,⌜A⌝ₛ,⌜k⌝ₛ,⌜k⌝ₛ,U) ∧ ⌜tt_pool_m⌝ₚ(⌜ω⌝ₛ,⌜m⌝ₛ,U,D) ∧
  ⌜td_pending_query_m⌝ₚ(⌜ω⌝ₛ,⌜A⌝ₛ,⌜e⌝ₛ,⌜m⌝ₛ,⌜q⌝ₛ,U,D,⌜k⌝ₛ,⌜pp⌝ₛ) ∧
  ⌜tg_bound_query_m⌝ₚ(⌜ω⌝ₛ,⌜e⌝ₛ,⌜n⌝ₛ,⌜m⌝ₛ,U,D,⌜pb⌝ₛ) ∧
  ⌜tg_height_query_m⌝ₚ(⌜ω⌝ₛ,⌜n⌝ₛ,⌜m⌝ₛ,U,D,⌜ph⌝ₛ)⟫
derive_free_closed td_reply_base_m

theorem td_reply_base_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω A e k q n m pp pb ph : Term d) :
    Formula.satisfies ρ (td_reply_base_m ω A e k q n m pp pb ph) ↔
      Td_reply_base_d I (ω.eval ρ) (A.eval ρ) (e.eval ρ) (k.eval ρ) (q.eval ρ) (n.eval ρ)
        (m.eval ρ) (pp.eval ρ) (pb.eval ρ) (ph.eval ρ) := by
  simp only [td_reply_base_m,Td_reply_base_d,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    tq_basis_sat_l hKP.1,tt_pool_sat_l I hKP,td_pending_query_sat_l I hKP,
    tg_bound_query_sat_l I hKP,tg_height_query_sat_l I hKP,Definitional.Term.eval_weaken]
  rfl

theorem Td_reply_base_d.scope_l (hKP : M.Models KP) {ω A e k q n m pp pb ph V W : M.Domain}
    (base : Td_reply_base_d I ω A e k q n m pp pb ph) (pool : Tt_pool_d I ω m V W)
    (hw : M.mem ω V) (hA : M.mem A V) (hk : M.mem k V) :
    Td_pending_query_d I ω A e m q V W k pp ∧
      Tg_bound_query_d I ω e n m V W pb ∧ Tg_height_query_d I ω n m V W ph := by
  obtain ⟨U,D,basis,small,pending,bound,height⟩ := base
  have sub : M.MemberSubset U V := by
    intro x hx
    rcases (basis x).mp hx with rfl | rfl | rfl | rfl
    exact hw
    exact hA
    exact hk
    exact hk
  exact ⟨pending.scope_l I hKP small pool sub,bound.scope_l I hKP small pool sub,
    height.scope_l I hKP small pool sub⟩

theorem td_reply_base_l (hZF : M.Models ZF) {ω A e k q n m : M.Domain}
    (hw : M.IsOmega ω) (hm : M.mem m ω) (he : M.mem e m) (hq : M.mem q m) (hn : M.mem n m) :
    ∃ pp pb ph, Td_reply_base_d (kp_pair_l (ZF.modelsKP hZF)) ω A e k q n m pp pb ph := by
  let J := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨B,pair⟩ := KP.exists_pair (ZF.modelsKP hZF) ω A
  obtain ⟨C,pair'⟩ := KP.exists_pair (ZF.modelsKP hZF) k k
  obtain ⟨U,union⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) B C
  have basis x : M.mem x U ↔ x = ω ∨ x = A ∨ x = k ∨ x = k := by
    simpa only [or_assoc] using (union x).trans (or_congr (pair x) (pair' x))
  obtain ⟨D,pool⟩ := tt_pool_exists_l J hZF hw m U
  have hwU := (basis ω).mpr (Or.inl rfl)
  obtain ⟨pp,pending⟩ := tt_demand_pending_query_l hZF hw hm he hq pool hwU
    ((basis A).mpr (Or.inr (Or.inl rfl))) ((basis k).mpr (Or.inr (Or.inr (Or.inl rfl))))
  obtain ⟨pb,bound⟩ := tt_bound_query_l hZF hw he hn hwU pool
  obtain ⟨ph,height⟩ := tt_height_query_l hZF hw hn pool
  exact ⟨pp,pb,ph,U,D,basis,pool,pending,bound,height⟩

theorem Td_reply_base_d.rank_l (hZF : M.Models ZF) {ω A e k q n m pp pb ph β Z : M.Domain}
    (base : Td_reply_base_d (kp_pair_l (ZF.modelsKP hZF)) ω A e k q n m pp pb ph)
    (hw : M.IsOmega ω) (rank : V_d (kp_pair_l (ZF.modelsKP hZF)) β Z)
    (limit : M.IsLimitOrdinal β) (hwZ : M.mem ω Z) (hA : M.mem A Z) (hk : M.mem k Z)
    (hm : M.mem m ω) : M.mem pp Z ∧ M.mem pb Z ∧ M.mem ph Z := by
  let J := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨U,D,basis,pool,pending,bound,height⟩ := base
  obtain ⟨B,hB,pair⟩ := sc_v_pair_l (ZF.modelsKP hZF) limit rank ω A hwZ hA
  obtain ⟨C,hC,pair'⟩ := sc_v_pair_l (ZF.modelsKP hZF) limit rank k k hk hk
  obtain ⟨W,hW,bw,cw⟩ := v_joint_bound_l J rank hB hC
  have hU : M.mem U Z := v_subset_mem_l J rank hW (fun x hx => by
    rcases (basis x).mp hx with rfl | rfl | rfl | rfl
    exact bw _ ((pair _).mpr (Or.inl rfl))
    exact bw _ ((pair _).mpr (Or.inr rfl))
    exact cw _ ((pair' _).mpr (Or.inl rfl))
    exact cw _ ((pair' _).mpr (Or.inl rfl)))
  have hD := pool.rank_mem_l (ZF.modelsKP hZF) hw rank limit hwZ hm hU
  have trans := v_transitive_l J rank D hD
  exact ⟨trans pp pending.1,trans pb bound.1,trans ph height.1⟩

end YesMetaZFC.SetTheory.LargeCardinal
