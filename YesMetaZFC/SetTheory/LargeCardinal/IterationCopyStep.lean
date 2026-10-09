import YesMetaZFC.SetTheory.LargeCardinal.IterationCopyApply
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSetCopy
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderModelMap
import YesMetaZFC.SetTheory.LargeCardinal.IterationCoherence
import YesMetaZFC.Model.SetTheory.Internal.SourceBranchPull

/-! # 完整可数闭模型中的实际复制一步

原图的目标是完整工作模型中的拥有秩段。扩展器在完整源上施加，复制图
落入该秩段的实际像；共同强度秩层把有限幂一致性提升为全前驱可消费的证书。
只使用所属源在本次支撑处的可数共尾界和秩层大小，不要求秩段高度正则。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ic_copy_step_l
    {ω κ κ' K K₀ K₁ K₂ K₃ K₄ L L' X R H Q A S B T Z V U W α β
      c b a d z π σ F F' P Rₚ o j₀ : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (owner : Ep_source_d hZF ω κ K₀ H Q)
    (small : Ep_source_d hZF ω κ' K₁ A S) (cut : Ep_source_d hZF ω κ' K₂ B T)
    (ambient : Ic_model_d hZF ω κ' K₃ Z V) (outer : Ep_source_d hZF ω κ' K₄ U W)
    (closed : Sc_bounded_omega_closed_d ω U) (power : Sc_power_d U) (cover : Sc_cover_d U)
    (bound : Sc_omega_bound_d ω U L') (sizes : Sc_rank_size_d I U L')
    (hA : M.mem A Z) (ra : Vr_d Z α A) (hα : M.IsLimitOrdinal α)
    (hB : M.mem B U) (rb : Vr_d U β B) (hβ : M.IsLimitOrdinal β)
    (hm : Smem_d I c X R) (ho : Smem_d I b H Q) (ha : Smem_d I a A S)
    (hb : Smem_d I d B T) (hz : Smem_d I z Z V)
    (hπ : Smap_d I ω c a X A π) (hσ : Smap_d I ω b d H B σ)
    (hκπ : Rd_entry_d κ κ' π) (hκσ : Rd_entry_d κ κ' σ)
    (hLσ : Rd_entry_d L L' σ) (hFσ : Rd_entry_d F F' σ)
    (agree : Ea_agree_d ω κ X H) (same : Ea_agree_d ω κ' A B) (maps : Ea_maps_d ω κ X π σ)
    (loc : It_local_d ω H κ L F) (strength : Ex_strength_d hZF ω κ L H F)
    (inaccessible : Sc_inaccessible_d ω H L)
    (hp : Smem_d I o P Rₚ) (ultra : It_ultra_d hZF ω κ L F c o j₀) :
    ∃ N Rₙ n j Kₙ α' A' S' a' k K', Smem_d I n N Rₙ ∧ It_ultra_d hZF ω κ' L' F' z n j ∧
      Ic_model_d hZF ω L' Kₙ N Rₙ ∧ Rd_entry_d α α' j ∧ Rd_entry_d A A' j ∧ M.IsLimitOrdinal α' ∧
      M.mem A' N ∧ Vr_d N α' A' ∧ Smem_d I a' A' S' ∧ Ep_source_d hZF ω L' K' A' S' ∧
      Smap_d I ω o a' P A' k ∧
      (∀ x x' y y', Rd_entry_d x x' π → Rd_entry_d x y j₀ → Rd_entry_d x' y' j → Rd_entry_d y y' k) ∧
      Es_strength_d H L P ∧ Pn_agree_d H B σ P A' k L L' ∧
      Ea_agree_d ω κ' Z U ∧ It_local_d ω U κ' L' F' ∧
      Ex_strength_d hZF ω κ' L' U F' ∧ Sc_inaccessible_d ω U L' := by
  have az := ambient.source.rank_agree_l hZF hA ra hα small.cardinal_mem
  have bu := outer.rank_agree_l hZF hB rb hβ cut.cardinal_mem
  have zu : Ea_agree_d ω κ' Z U := fun m D C hm hd hc =>
    (az m D C hm hd hc).symm.trans ((same m D C hm hd hc).trans (bu m D C hm hd hc))
  have zb : Ea_agree_d ω κ' Z B := fun m D C hm hd hc =>
    (az m D C hm hd hc).symm.trans (same m D C hm hd hc)
  have loc' := loc.map_l hZF source.omega owner.transitive cut.transitive ho hb hσ hκσ hLσ hFσ
  have strength' := strength.map_l hZF source.omega owner.transitive cut.transitive ho hb hσ cut.theory hκσ hLσ hFσ
  have card' := inaccessible.map_l hZF source.omega owner.transitive cut.transitive ho hb hσ hLσ
  obtain ⟨up, strong, card, N, Rₙ, n, j, Kₙ, W', hn, big, next, hwU, rwU, rwN, _, _, _⟩ :=
    ambient.rank_apply_l hZFC outer closed power cover bound sizes zu hz hB rb hβ loc' strength' card'
  have hj := big.elementary_l hZF hz.1 hn.1
  have ht := next.source.transitive
  obtain ⟨A', hA', hAA⟩ := hj.1.1.2.2 A hA
  obtain ⟨C, f, hC, hf, cert⟩ := ra
  have hαZ := sc_function_domain_mem_l hZF source.omega ambient.source.transitive hz ambient.source.theory hf (cert A hA).2.1
  have ra : Vr_d Z α A := ⟨C, f, hC, hf, cert⟩
  obtain ⟨α', _, hαα⟩ := hj.1.1.2.2 α hαZ
  have ra' := (hj.hierarchy_l hZF source.omega ambient.source.transitive ht hz hn hαα hAA).mp ra
  have hl := (hj.limit_l hZF source.omega ambient.source.transitive ht hz hn hαα).mp hα
  have ta := ra'.transitive_l hZF ht hA'
  have hw := hj.omega_l I hZF source.omega ambient.source.transitive ht hz hn ambient.source.omega_mem
  have hwA' := ((hn.2 ω A').mp ((hj.relation_l I hZF source.omega hz.1 hn.1 hw hAA).mp
    ((hz.2 ω A).mpr ⟨ambient.source.omega_mem, hA, small.omega_mem⟩))).2.2
  obtain ⟨a', S', ha'⟩ := smdl_membership_l I hZF ⟨ω, hwA'⟩
  -- 所属小秩段中的层级大小及闭包均由完整源的实际证书向下读取。
  have op := power.rank_l hZF outer.transitive hB rb hβ
  have oc := sc_rank_cover_l hZF outer.transitive hB rb
  have ob := (closed.rank_l hZF outer.transitive hB rb hβ cut.omega_mem).branch_l
  have os := sizes.rank_l hZF outer.transitive hB rb hβ (hσ.1.1.output_mem_of_pairMember hLσ)
  have old_sizes := (hσ.rank_size_l hZF source.omega owner.transitive cut.transitive ho hb hLσ).mpr os
  have old_power := (sc_power_iff_l hZF source.omega owner.transitive cut.transitive ho hb hσ).mpr op
  have old_cover := (sc_cover_iff_l hZF source.omega owner.transitive cut.transitive ho hb hσ).mpr oc
  have old_branch := ob.pull_l hZF source.omega owner.transitive cut.transitive owner.omega_mem ho hb hσ
  have hL := inaccessible.limit_l (ZF.modelsKP hZF) owner.transitive owner.theory.algebra.pair
  have hL' := card'.limit_l (ZF.modelsKP hZF) cut.transitive cut.theory.algebra.pair
  obtain ⟨W₀, f₀, hw₀, rw₀, hf₀, bf₀⟩ := old_sizes.level
  obtain ⟨C₀, hc₀, _, iso⟩ := ep_transitive_code_l hZF owner (rw₀.transitive_l hZF owner.transitive hw₀) hf₀ bf₀
  have level : Er_level_d H L W₀ := ⟨hw₀, rw₀, C₀, f₀, hc₀, hf₀, iso⟩
  obtain ⟨k, hk, commute, hLP, hLA, fixed, endpt, kmaps, _⟩ := ep_set_copy_l hZFC source small ambient.source
    owner cut agree zb old_power hm ha hz hn ha' hπ hκπ ho hb hσ hκσ hLσ hFσ maps loc hL level
    (fun m D C hm hd hc => (az m D C hm hd hc).mpr) hp ultra big hAA
  -- 原后继的源证书和共同强度秩层来自给定超幂，不另选新的后继。
  have pt := ultra.transitive_l hZF hp.1
  have hj₀ := ultra.elementary_l hZF hm.1 hp.1
  have copy := loc
  obtain ⟨_, _, _, _, pre⟩ := copy
  simp only [ex_short_m, ex_pre_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at pre
  have above := hL.1.transitive κ pre.1.2.2.2.2.1 ω pre.1.2.2.1
  have below := hL.1.transitive ω above
  have theory := source.theory.map_l I hZF source.omega source.transitive pt hm hp hj₀
  obtain ⟨Kₚ, ready⟩ := source.successor_l hZF hm hp pt hj₀ hLP below
    (sc_ordinal_small_l hZF source.omega pt hp theory hLP hL.1)
  have oh := (sc_hierarchy_iff_l hZF source.omega source.transitive small.transitive hm ha hπ).mpr
    (ambient.hierarchy.rank_l hZF ambient.source.transitive hA ra hα)
  have pp := (sc_power_iff_l hZF source.omega source.transitive small.transitive hm ha hπ).mpr
    (ambient.power.rank_l hZF ambient.source.transitive hA ra hα)
  have successor : Ep_successor_d hZF ω κ L X R F P Rₚ := by
    obtain ⟨X₀, R₀, P₀, Q₀, J, O, Z₀, A₀, p, T₀, V₀, q, u, C₁, W₁, i, e,
      mx, mp, system, limit, model, wc, bij, he, _⟩ := ultra
    obtain ⟨rfl, rfl⟩ := smdl_unique_l I mx.1 hm.1
    obtain ⟨rfl, rfl⟩ := smdl_unique_l I mp.1 hp.1
    exact ⟨J, O, Z₀, A₀, p, T₀, V₀, q, u, C₁, W₁, o, e, system, limit, model, hp, pt, wc, bij, he⟩
  obtain ⟨W₁, hwH, rwH, rwP, _, exactness, _⟩ := loc.rank_agree_l hZFC source owner ready agree
    old_branch old_power old_cover ((sc_hierarchy_iff_l hZF source.omega source.transitive pt hm hp hj₀).mp oh)
    ((sc_power_iff_l hZF source.omega source.transitive pt hm hp hj₀).mp pp) old_sizes hL successor strength
  obtain ⟨Kₕ, ownerL⟩ := owner.rebase_l hZF (hσ.1.1.input_mem_of_pairMember hLσ) below
    (sc_ordinal_small_l hZF source.omega owner.transitive ho owner.theory (hσ.1.1.input_mem_of_pairMember hLσ) hL.1)
  obtain ⟨C₁, f₁, _, hf₁, iso₁⟩ := rwP.code
  obtain ⟨_, _, _, points⟩ := kmaps.transitive_l hZF ready ownerL ta cut.transitive hp ha' hk ho hb hσ endpt hLσ fixed
    (rwP.hierarchy.transitive_l hZF pt rwP.member) hf₁ (iso₁.bijection_l (ZF.modelsKP hZF))
  obtain ⟨hwB, rwB⟩ := rb.rank_l hZF outer.transitive hB hβ (hσ.1.1.output_mem_of_pairMember hLσ) hwU rwU
  obtain ⟨hwA, rwA⟩ := ra'.rank_l hZF ht hA' hl hLA rwN.member rwN.hierarchy
  have adjacent : Pn_agree_d H B σ P A' k L L' :=
    ⟨owner.transitive, cut.transitive, pt, ta, hL, hL',
      ⟨W₁, hwH, rwP.member, rwH, rwP.hierarchy, fun x y hx => (points x y hx).symm⟩,
      ⟨W', hwB, hwA, rwB, rwA⟩, hLσ, endpt⟩
  obtain ⟨K', small'⟩ := ready.successor_l hZF hp ha' ta hk hLA
    ((hσ.subset_l hZF source.omega owner.transitive cut.transitive ho hb
      (hσ.omega_l I hZF source.omega owner.transitive cut.transitive ho hb owner.omega_mem) hLσ).mp below)
    ((hk.small_l hZF source.omega pt ta hp ha' endpt).mp ready.cardinal_small)
  exact ⟨N, Rₙ, n, j, Kₙ, α', A', S', a', k, K', hn, big, next, hαα, hAA, hl, hA', ra', ha', small', hk,
    commute, exactness, adjacent, zu, up, strong, card⟩

end YesMetaZFC.SetTheory.LargeCardinal
