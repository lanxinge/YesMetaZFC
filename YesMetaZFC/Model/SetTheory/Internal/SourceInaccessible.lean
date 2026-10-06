import YesMetaZFC.Model.SetTheory.Internal.TransitiveCardinal
import YesMetaZFC.Model.SetTheory.Internal.SourcePower

/-! # 所属模型中的原始不可达性

正则性使用原始共尾度定义，强极限性使用原始幂集基数定义。
极限 Vδ 的实例直接回收共尾图与单射图；不要求 Vδ 本身满足 ZF。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def sc_inaccessible_m {d} (ω κ : Term d) : Formula 1 d := .conj (.mem ω κ)
  (.conj (Formula.isRegularCardinal kpair_convention_l κ) (Formula.isStrongLimitCardinal kpair_convention_l κ))
derive_free_closed sc_inaccessible_m

def Sc_inaccessible_d (ω X κ : M.Domain) : Prop :=
  ∃ hω : M.mem ω X, ∃ hκ : M.mem κ X, Formula.satisfies
    (⟨Fin.cases ⟨κ, hκ⟩ (fun _ => ⟨ω, hω⟩), fun _ => ⟨ω, hω⟩⟩ : Env (rt_model_l X ⟨⟨ω, hω⟩⟩) 2)
    (sc_inaccessible_m (.bound 1) .newest)

/-- 完整初等图传输原始公式，不把目标内部不可达性提升为背景不可达性。 -/
theorem Sc_inaccessible_d.map_l (hZF : M.Models ZF) {ω c d X R Y S j κ κ' : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R) (hn : Smem_d (kp_pair_l (ZF.modelsKP hZF)) d Y S)
    (hj : Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω c d X Y j) (hκ : Rd_entry_d κ κ' j)
    (h : Sc_inaccessible_d ω X κ) : Sc_inaccessible_d ω Y κ' := by
  obtain ⟨hωX, hκX, h⟩ := h
  have hωj := hj.omega_l _ hZF hω hX hY hm hn hωX
  have hωY := hj.1.1.output_mem_of_pairMember hωj
  have hκY := hj.1.1.output_mem_of_pairMember hκ
  let ρ : Env (rt_model_l X ⟨⟨ω, hωX⟩⟩) 2 :=
    ⟨Fin.cases ⟨κ, hκX⟩ (fun _ => ⟨ω, hωX⟩), fun _ => ⟨ω, hωX⟩⟩
  let η : Env (rt_model_l Y ⟨⟨ω, hωY⟩⟩) 2 :=
    ⟨Fin.cases ⟨κ', hκY⟩ (fun _ => ⟨ω, hωY⟩), fun _ => ⟨ω, hωY⟩⟩
  obtain ⟨z, hz⟩ := KP.exists_empty (ZF.modelsKP hZF)
  exact ⟨hωY, hκY, (spred_source_l _ hZF hω ⟨c, R, d, S, hm.empty_pred_l _ hz, hn.empty_pred_l _ hz, hj⟩
    ⟨⟨ω, hωX⟩⟩ ⟨⟨ω, hωY⟩⟩ (sc_inaccessible_m (.bound 1) .newest) (by simp -implicitDefEqProofs)
    ρ η (Fin.cases hκ (fun _ => hωj))).mp h⟩

theorem sc_v_inaccessible_l (hZF : M.Models ZF) {δ X ω κ : M.Domain} (hδ : M.IsLimitOrdinal δ)
    (hX : V_d (kp_pair_l (ZF.modelsKP hZF)) δ X) (hκ : M.mem κ X) (above : M.mem ω κ)
    (hr : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP hZF)) κ)
    (hs : M.IsStrongLimitCardinal (kp_pair_l (ZF.modelsKP hZF)) κ) : Sc_inaccessible_d ω X κ := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have ht := ZF.v_transitive_l I hZF hX
  have hω := ht κ hκ ω above
  let nx : Nonempty {x // M.mem x X} := ⟨⟨ω, hω⟩⟩
  let N := rt_model_l X nx
  have hp := sc_v_pair_l hZF hδ hX
  let J := rt_pair_l ht nx hZF.1 hp
  let k : N.Domain := ⟨κ, hκ⟩
  have cardinal := rt_cardinal_l ht nx hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) hp k hr.1
  refine ⟨hω, hκ, ?_⟩
  simp only [sc_inaccessible_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_isRegularCardinal_iff J (rt_model_ext_l hZF.1 ht nx),
    Formula.satisfies_isStrongLimitCardinal_iff J (rt_model_ext_l hZF.1 ht nx)]
  change M.mem ω κ ∧ N.IsRegularCardinal J k ∧ N.IsStrongLimitCardinal J k
  refine ⟨above, ⟨cardinal, ?_, ?_⟩, cardinal, ?_⟩
  -- 正则性：回收原共尾图和值域，再把可能更短的序列送回背景比较。
  · obtain ⟨f, cofinal⟩ := hr.2.1
    have ff := cofinal.isSetFunctionFromTo
    have hf := ZF.v_relation_mem_l I hZF hX hδ hκ (fun p hpf => by
      obtain ⟨a, b, pair⟩ := ff.1.1 p hpf
      exact ⟨a, ff.input_mem_of_pairMember ⟨p, pair, hpf⟩, b, ff.output_mem_of_pairMember ⟨p, pair, hpf⟩, pair⟩)
    obtain ⟨R, range, _⟩ := cofinal.2.2.1.2.2
    have hR := ZF.v_subset_mem_l I hZF hX hκ (cofinal.range_isCofinalSubset hZF.1 range).2.1
    exact ⟨⟨f, hf⟩, rt_cofinal_down_l ht nx hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) hp ⟨f, hf⟩ k k ⟨R, hR⟩ range cofinal⟩
  · rintro μ ⟨f, hf⟩
    exact (hr.2.2 μ.val ⟨f.val, rt_cofinal_up_l ht nx hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) hp
      (ZF.modelsKP hZF) f μ k hf⟩).imp Subtype.ext id
  -- 强极限性：源中的相对幂集就是实际幂集，其基数单射仍落在同一秩段。
  · intro a ha P power
    have pow : M.IsPowerSetOf P.val a.val := by
      intro B
      refine ⟨fun hb x hx => ?_, fun sub => ?_⟩
      · exact (power ⟨B, ht P.val P.property B hb⟩).mp hb ⟨x, ht B (ht P.val P.property B hb) x hx⟩ hx
      · exact (power ⟨B, ZF.v_subset_mem_l I hZF hX a.property sub⟩).mpr (fun x hx => sub x.val hx)
    obtain ⟨⟨f, ff⟩, not_bij⟩ := hs.2 a.val ha P.val pow
    obtain ⟨B, hB, pb, kb⟩ := ZF.v_joint_bound_l I hZF hX P.property hκ
    have hf := ZF.v_relation_mem_l I hZF hX hδ hB (fun p hpf => by
      obtain ⟨a, b, pair⟩ := ff.1.1.1 p hpf
      exact ⟨a, pb a (ff.1.input_mem_of_pairMember ⟨p, pair, hpf⟩), b,
        kb b (ff.1.output_mem_of_pairMember ⟨p, pair, hpf⟩), pair⟩)
    exact ⟨⟨⟨f, hf⟩, (rt_injection_l ht nx hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) hp ⟨f, hf⟩ P k).mpr ff⟩,
      fun ⟨g, gg⟩ => not_bij ⟨g.val, (rt_bijection_l ht nx hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) hp g P k).mp gg⟩⟩

end YesMetaZFC.SetTheory.Internal
