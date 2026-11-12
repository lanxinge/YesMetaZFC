import YesMetaZFC.SetTheory.LargeCardinal.Game.Elastic
import YesMetaZFC.Model.SetTheory.Game.NodeEmbedding
import YesMetaZFC.Model.SetTheory.Types.ExceedsSyntax
import YesMetaZFC.SetTheory.LargeCardinal.Types.ElasticNumericTransfer
import YesMetaZFC.SetTheory.LargeCardinal.Game.RecoverySyntax

/-! # 超过关系与 dcp 定义域固定唯一高度对象

旧类型的末位加二为最大序数；新类型超过它且 dcp⁻ 有定义。
只用这一定义域即可推出新类型的末位为最大序数，不调用伸展强性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem tg_exceeds_rigid_l {ω κ τ i m l n U D V P W a b δ w u v g h : M.Domain}
    (hω : M.IsOmega ω) (hi : M.mem i m) (hn : M.SuccessorOf n l)
    (language : Ee_domain_d hZF ω τ l V D g h)
    (heightQuery : Tg_height_query_d I ω i m U P a) (maxQuery : Tg_max_query_d I ω l n V W b)
    (haw : M.mem a w) (drop : Td_dcp_d I l n D u v) (defined : M.mem g v ∧ M.mem h v)
    (exceeds : Tx_exceeds_d hZF ω δ κ m U P w τ n V W u) : M.mem b u := by
  obtain ⟨_, mn, η, Y, c, R, r, hY, model, oldType, ν, ρ, succ, gap, witness⟩ := exceeds
  obtain ⟨α, _, oldLast⟩ := oldType.tuple.2.1 i hi
  have height := (heightQuery.2 η Y c R r δ w α hY model oldType oldLast).mp haw
  obtain ⟨A, d, H, s, f, g, π, hA, lower, type, ff, _, graph, orig, bij, perm⟩ := witness
  have fα := (orig i α hi).mp oldLast
  have hαA := ff.output_mem_of_pairMember fα
  have oα : M.IsOrdinal α := by
    obtain ⟨β, γ, hβ, hγ, hη⟩ := height
    exact (((v_ordinal_l I hY).mem hη.predecessor_mem).mem hγ.predecessor_mem).mem hβ.predecessor_mem
  have rigid := height.gap_l hZF.1 (KP.mem_irrefl_d (ZF.modelsKP hZF)) (v_ordinal_l I hY)
    (ZF.v_ordinal_height_l hZF hA oα hαA) succ gap
  obtain ⟨s₀, v₀, cut, drop₀, prefixType⟩ := type.dcp_l hZF hω drop.1 language.pool
  have eqv := drop₀.unique_l I hZF.1 drop
  subst v₀
  obtain ⟨ν₀, hs⟩ := (language.successor ν A d H s₀ δ v hA lower prefixType).mp defined.1
  obtain ⟨A₀, hA₀⟩ := ZF.v_exists_l I hZF ((v_ordinal_l I hA).mem hs.predecessor_mem)
  have hων : M.MemberSubset ω ν₀ := by
    rcases (hs ω).mp (ZF.v_ordinal_height_l hZF hA (hω.isOrdinal (ZF.modelsKP hZF)) (prefixType.constants ω language.omega_mem)) with lt | eq
    · exact (v_ordinal_l I hA₀).transitive ω lt
    · exact fun x hx => (eq x).mp hx
  have tuple := ((language.domain ν₀ ν A₀ A d H s₀ δ v hA₀ hA hs hων lower prefixType).mp defined.2).1
  have eqν := rigid.predecessor_eq hZF.1 oα hs
  subst ν₀
  obtain ⟨j, hj, ji⟩ := bij.2 i (mn i hi)
  have oldα : Rd_entry_d j α s := (graph j α).mp ((perm j hj α hαA).mpr ⟨i, mn i hi, ji, fα⟩)
  have last : Rd_entry_d l α s := by
    rcases (hn j).mp hj with lt | eq
    · have low := (tuple.bound_l ((cut.2 j α).mpr ⟨lt, oldα⟩)).2
      exact (KP.mem_irrefl_d (ZF.modelsKP hZF) α (ZF.v_ordinal_height_l hZF hA₀ oα low)).elim
    · exact hZF.1.eq_of_same_members j l eq ▸ oldα
  exact (maxQuery.2 ν A d H s δ u α hA lower type last).mpr rigid

-- 旧回答的七项查询基底；旧 κ,δ,U,P,w；新 τ,l,n,V,D,W,g,h,u；新节点的 k,s,t 及五条查询。
def tc_rigid_seed0_m : Formula 1 29 :=
  let p : Fin 29 → Term 29 := Term.bound
  set[29] ⟪⌜Formula.isOmega⌝ₚ(⌜p 0⌝ₛ) ∧ ⌜p 2⌝ₛ ∈ ⌜p 3⌝ₛ ∧ ⌜p 0⌝ₛ ∈ ⌜p 9⌝ₛ ∧
    ⌜tt_pool_m⌝ₚ(⌜p 0⌝ₛ, ⌜p 3⌝ₛ, ⌜p 9⌝ₛ, ⌜p 10⌝ₛ) ∧
    ⌜tg_reply_base_m⌝ₚ(⌜p 0⌝ₛ, ⌜p 1⌝ₛ, ⌜p 2⌝ₛ, ⌜p 3⌝ₛ, ⌜p 4⌝ₛ, ⌜p 5⌝ₛ, ⌜p 6⌝ₛ) ∧
    ⌜p 6⌝ₛ ∈ ⌜p 11⌝ₛ ∧
    ⌜ee_domain_pack_m⌝ₚ(⌜p 0⌝ₛ, ⌜p 12⌝ₛ, ⌜p 13⌝ₛ, ⌜p 15⌝ₛ, ⌜p 16⌝ₛ, ⌜p 18⌝ₛ, ⌜p 19⌝ₛ) ∧
    (∃ v, ⌜td_dcp_m⌝ₚ(⌜p 13⌝ₛ, ⌜p 14⌝ₛ, ⌜p 16⌝ₛ, ⌜p 20⌝ₛ, v) ∧ ⌜p 18⌝ₛ ∈ v ∧ ⌜p 19⌝ₛ ∈ v) ∧
    ⌜tg_query_base_m⌝ₚ(⌜p 0⌝ₛ, ⌜p 1⌝ₛ, ⌜p 13⌝ₛ, ⌜p 14⌝ₛ, ⌜p 21⌝ₛ, ⌜p 22⌝ₛ, ⌜p 23⌝ₛ,
      ⌜p 24⌝ₛ, ⌜p 25⌝ₛ, ⌜p 26⌝ₛ, ⌜p 27⌝ₛ, ⌜p 28⌝ₛ) ∧
    ⌜tt_pool_m⌝ₚ(⌜p 0⌝ₛ, ⌜p 14⌝ₛ, ⌜p 15⌝ₛ, ⌜p 17⌝ₛ) ∧
    ⌜p 21⌝ₛ ∈ ⌜p 15⌝ₛ ∧ ⌜p 22⌝ₛ ∈ ⌜p 15⌝ₛ ∧ ⌜p 23⌝ₛ ∈ ⌜p 15⌝ₛ ∧
    ⌜tx_exceeds_m⌝ₚ(⌜p 0⌝ₛ, ⌜p 8⌝ₛ, ⌜p 7⌝ₛ, ⌜p 3⌝ₛ, ⌜p 9⌝ₛ, ⌜p 10⌝ₛ, ⌜p 11⌝ₛ,
      ⌜p 12⌝ₛ, ⌜p 14⌝ₛ, ⌜p 15⌝ₛ, ⌜p 17⌝ₛ, ⌜p 20⌝ₛ)⟫

theorem tc_rigid_seed0_closed_l : tc_rigid_seed0_m.FreeClosed := by
  simp -implicitDefEqProofs [tc_rigid_seed0_m, Definitional.Formula.FreeClosed]

def tc_rigid_m : Formula 1 0 := Formula.forallClosure 29
  (.imp tc_rigid_seed0_m (.mem (.bound 25) (.bound 20)))

theorem tc_rigid_closed_l : tc_rigid_m.FreeClosed :=
  (Definitional.Formula.freeClosed_forallClosure _).mpr ⟨tc_rigid_seed0_closed_l, rfl, rfl⟩

include hZF in
/-- 高度刚性只反射 ZF 读取定理，伸展和不可达性不进入前件。 -/
theorem tc_rigid_true_l (ε : FreeVarId → M.Domain) :
    Formula.satisfies (⟨Fin.elim0, ε⟩ : Env M 0) tc_rigid_m := by
  apply (Formula.satisfies_forallClosure_iff ε _).mpr
  intro p
  simp only [tc_rigid_seed0_m, Formula.satisfies_imp_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isOmega_iff, Formula.satisfies_mem_iff, tt_pool_sat_l I (ZF.modelsKP hZF),
    tg_reply_base_sat_l I (ZF.modelsKP hZF), ee_domain_pack_sat_l hZF,
    Formula.satisfies_exists_iff, td_dcp_sat_l I hZF.1, tg_query_base_sat_l I (ZF.modelsKP hZF),
    tx_exceeds_sat_l hZF, Definitional.Term.eval_weaken]
  rintro ⟨hw, hi, hwU, oldPool, reply, hh, domain, ⟨v, drop, hg, hd⟩, base, pool, hk, hs, ht, exceeds⟩
  exact tg_exceeds_rigid_l hZF hw hi drop.1 domain (reply.scope_l I (ZF.modelsKP hZF) oldPool hwU).2.2
    (base.scope_l I (ZF.modelsKP hZF) pool domain.omega_mem hs ht hk).2.1 hh drop ⟨hg, hd⟩ exceeds

end YesMetaZFC.SetTheory.LargeCardinal
