import YesMetaZFC.SetTheory.LargeCardinal.Demand.RoundScope
import YesMetaZFC.SetTheory.LargeCardinal.Demand.RealTrace

/-! # 原回合实数图的函数性及低秩归属

完整节点的第一图取值于原树的实数字母域。有限图落在包含 ω 与字母域
的极限秩层中，故第二共同方块可运输它的全部取值。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem td_round_real_l (hKP : M.Models KP) (ρ : Env M 62) (round : Formula.satisfies ρ td_round0_m) :
    M.IsOmega (ρ.bound 19) ∧ (∀ x, ¬ M.mem x (ρ.bound 20)) ∧
      M.mem (ρ.bound 25) (ρ.bound 19) ∧ Fn0_d (ρ.bound 25) (ρ.bound 50) (ρ.bound 44) := by
  let I := kp_pair_l hKP
  have seed := (Formula.satisfies_rename ..).mp ((Formula.satisfies_conj_iff ..).mp round).1
  simp only [td_seed0_m,td_seed_m,Formula.satisfies_conj_iff] at seed
  obtain ⟨hw,empty,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,node,tree,_⟩ := seed
  have hw := (Formula.satisfies_isOmega_iff ..).mp hw
  have empty := (Formula.satisfies_isEmpty_iff ..).mp empty
  have node := (tg_node_sat_l I hKP.1 ..).mp node
  have tree := (td_tree_sat_l I hKP.1 ..).mp tree
  obtain ⟨fs,_,_,q,hq,join⟩ := node
  obtain ⟨n,hn,graph,triples⟩ := tree.nodes q hq
  have eq : n = ρ.bound 25 := graph.2.eq hKP.1 join.1.2
  have bound i x (ix : M.PairMember I i x (ρ.bound 44)) : M.mem x (ρ.bound 50) := by
    obtain ⟨x',a,b,t,p,ix',_,_,_,pair,ip⟩ := join.2 i ((fs.2 i).mpr ⟨x,ix⟩)
    have ex := fs.1.2 i x' x ix' ix
    obtain ⟨y,_,_,t',hy,pair',_⟩ := triples i p ip
    have ey := (I.injective pair' pair).1
    exact ex ▸ ey ▸ hy
  exact ⟨hw,empty,eq ▸ hn,fn0_of_function_l hKP ⟨fs.1,fs.2,
    fun i hi => ((fs.2 i).mp hi).imp fun x ix => ⟨bound i x ix,ix⟩⟩⟩

theorem td_round_real_mem_l (hZF : M.Models ZF) (ρ : Env M 62) (round : Formula.satisfies ρ td_round0_m)
    {κ V : M.Domain} (rank : V_d (kp_pair_l (ZF.modelsKP hZF)) κ V) (limit : M.IsLimitOrdinal κ)
    (hw : M.mem (ρ.bound 19) V) (hA : M.mem (ρ.bound 50) V) : M.mem (ρ.bound 44) V := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨_,_,hk,fn⟩ := td_round_real_l (ZF.modelsKP hZF) ρ round
  obtain ⟨P,product⟩ := ZF.exists_cartesianProduct hZF I (ρ.bound 25) (ρ.bound 50)
  have hp := ZF.v_product_mem_l I hZF rank limit ((v_transitive_l I rank) _ hw _ hk) hA product
  apply v_subset_mem_l I rank hp
  intro p hp
  obtain ⟨i,x,pair⟩ := (fn0_function_l (ZF.modelsKP hZF) fn).1.1 p hp
  have bounds := fn.bound_l (show Rd_entry_d i x (ρ.bound 44) from ⟨p,pair,hp⟩)
  exact (product p).mpr ⟨i,bounds.1,x,bounds.2,pair⟩

theorem td_round_real_empty_l (hKP : M.Models KP) (ρ : Env M 62) (round : Formula.satisfies ρ td_round0_m)
    (zero : ρ.bound 25 = ρ.bound 20) : ρ.bound 44 = ρ.bound 20 := by
  obtain ⟨_,empty,_,fn⟩ := td_round_real_l hKP ρ round
  apply hKP.1.eq_of_same_members
  intro p
  apply iff_of_false ?_ (empty p)
  intro hp
  obtain ⟨i,x,pair⟩ := (fn0_function_l hKP fn).1.1 p hp
  exact empty i (zero ▸ (fn.bound_l (show Rd_entry_d i x (ρ.bound 44) from ⟨p,pair,hp⟩)).1)

/-- 原语言的 ω 位于新回合秩层内，因而所有数字都能通过档案共同层。 -/
theorem td_round_omega_low_l (hZF : M.Models ZF) (ρ : Env M 62) (round : Formula.satisfies ρ td_round0_m) :
    M.mem (ρ.bound 19) (ρ.bound 1) := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have seed := (Formula.satisfies_rename ..).mp ((Formula.satisfies_conj_iff ..).mp round).1
  simp only [td_seed0_m,td_seed_m,Formula.satisfies_conj_iff] at seed
  have language := seed.2.2.2.2.2.2.2.2.2.2.2.2.1
  simp only [ee_language_m,Formula.satisfies_bind,ee_language0_m,Formula.satisfies_conj_iff] at language
  have domain := language.1
  simp only [ee_domain_pack_m,Formula.satisfies_bind,ee_domain_pack0_m,Formula.satisfies_conj_iff] at domain
  have omega : M.mem (ρ.bound 19) (ρ.bound 35) := (Formula.satisfies_mem_iff ..).mp domain.1
  have rank := (v_sigma_sat_l (ZF.modelsKP hZF) ..).mp language.2.2.1
  have constants := (tt_constants0_sat_l hZF.1 ..).mp language.2.2.2.1
  have witness := ((Formula.satisfies_conj_iff ..).mp round).2
  simp only [td_witness0_m,td_round_m,Formula.satisfies_conj_iff] at witness
  have growth : M.mem (ρ.bound 24) (ρ.bound 0) := (Formula.satisfies_mem_iff ..).mp witness.2.1
  have language' := witness.2.2.2.2.2.2.1
  simp only [ee_language_m,Formula.satisfies_bind,ee_language0_m,Formula.satisfies_conj_iff] at language'
  have limit := (Formula.satisfies_isLimitOrdinal_iff ..).mp language'.2.1
  have rank' : V_d I (ρ.bound 0) (ρ.bound 1) := (v_sigma_sat_l (ZF.modelsKP hZF) ..).mp language'.2.2.1
  exact (v_transitive_l I rank') _ (tt_constants_rank_l hZF rank' limit growth rank constants) _ omega

end YesMetaZFC.SetTheory.LargeCardinal
