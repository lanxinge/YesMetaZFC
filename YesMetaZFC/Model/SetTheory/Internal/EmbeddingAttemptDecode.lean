import YesMetaZFC.Model.SetTheory.Internal.EmbeddingAttempt
import YesMetaZFC.SetTheory.Card.FiniteOrdinal
import YesMetaZFC.SetTheory.Card.OrdinalImage

/-! # 从总尝试枝解码完整初等嵌入

给定可数域的实际编号图，嵌入就是枝沿编号的复合。有限个赋值编号有一个
内部自然数界，所以同一节点能检验任意内部公式；最后恢复原 Smap 证书。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

include hZF in
theorem at_index_bound_l {ω b q : M.Domain} (hω : M.IsOmega ω) (hb : M.mem b ω)
    (hq : Fn0_d b ω q) : ∃ n, M.mem n ω ∧ Fn0_d b n q := by
  have hf := fn0_function_l (ZF.modelsKP hZF) hq
  obtain ⟨D, hD⟩ := ZF.exists_range_of_setFunction hZF I hf.1 hf.2.1
  have fd := hq.retarget_l (fun i x h => (hD x).mpr ⟨i, h⟩)
  have finite : Finite_d I ω D := ⟨b, hb, ZF.ordinal_image_bound_l I hZF ((hω.isOrdinal hZF).mem hb)
    (ZF.exists_inclusionInjection hZF I (source := b) (fun _ h => h)) (fn0_function_l (ZF.modelsKP hZF) fd)
    (fun x hx => ((hD x).mp hx).elim fun i hi => ⟨i, (hq.bound_l hi).1, hi⟩)⟩
  have hu : M.IsUnionOf ω ω := fun i => ⟨fun hi => (hω.1.2 i hi).elim fun n hn =>
    ⟨n, hn.2, hn.1.predecessor_mem⟩, fun ⟨n, hn, hi⟩ => hω.transitive hZF n hn i hi⟩
  obtain ⟨z, _, hz⟩ := hω.1.1
  obtain ⟨n, hn, sub⟩ := ZF.finite_union_bound_l I hZF hω (hω.isOrdinal hZF) hu ⟨z, hz⟩ finite
    (fun x hx => ((hD x).mp hx).elim fun _ hi => (hq.bound_l hi).2)
  exact ⟨n, hn, fd.mono_target_l sub⟩

include hZF in
private theorem at_upper_l {ω i k : M.Domain} (hω : M.IsOmega ω) (hi : M.mem i ω) (hk : M.mem k ω) :
    ∃ n, M.mem n ω ∧ M.mem i n ∧ M.mem k n := by
  rcases (hω.isOrdinal hZF).wellOrder.linear.compare i hi k hk with eq | hik | hki
  · have eq := hZF.1.eq_of_same_members i k eq
    subst k
    obtain ⟨n, hn, hnω⟩ := hω.1.2 i hi
    exact ⟨n, hnω, hn.predecessor_mem, hn.predecessor_mem⟩
  · obtain ⟨n, hn, hnω⟩ := hω.1.2 k hk
    exact ⟨n, hnω, (hn i).mpr (Or.inl hik), hn.predecessor_mem⟩
  · obtain ⟨n, hn, hnω⟩ := hω.1.2 i hi
    exact ⟨n, hnω, hn.predecessor_mem, (hn k).mpr (Or.inl hki)⟩

theorem at_decode_l {ω c d A R B S e τ ι g j : M.Domain}
    (hω : M.IsOmega ω) (hm : Smdl_d I c A R) (hn : Smdl_d I d B S)
    (he : Fn0_d ω A e) (hι : Fn0_d A ω ι)
    (hsect : ∀ x i, Rd_entry_d x i ι → Rd_entry_d i x e)
    (hg : Fn0_d ω B g) (hj : Cp0_d A ω B ι g j)
    (branch : ∀ n, M.mem n ω → ∃ p, At_node_d I ω A R B S e τ n p ∧ M.IsRestrictionOf I p g n) :
    Smap_d I ω c d A B j ∧ ∀ x y, M.mem x A → M.mem y B → Rd_entry_d x y τ → Rd_entry_d x y j := by
  have ef := fn0_function_l (ZF.modelsKP hZF) he
  have jf := fn0_function_l (ZF.modelsKP hZF) hj.1
  have inject : M.IsSetInjective I j := by
    intro x z y hxy hzy
    obtain ⟨i, hi, hxi⟩ := hι.2.1 x (hj.1.bound_l hxy).1
    obtain ⟨k, hk, hzk⟩ := hι.2.1 z (hj.1.bound_l hzy).1
    obtain ⟨n, hnω, hin, hkn⟩ := at_upper_l hZF hω hi hk
    obtain ⟨p, node, res⟩ := branch n hnω
    have hip := (res.2 i y).mpr ⟨hin, (hj.value_l hι hg hxi).mp hxy⟩
    have hkp := (res.2 k y).mpr ⟨hkn, (hj.value_l hι hg hzk).mp hzy⟩
    obtain ⟨a, _, hia, hka⟩ := (node.coherent i hin k hkn).mpr ⟨y, (hj.1.bound_l hxy).2, hip, hkp⟩
    exact (ef.1.2 i x a (hsect x i hxi) hia).trans (ef.1.2 k z a (hsect z k hzk) hka).symm
  refine ⟨⟨⟨jf, inject⟩, ?_⟩, fun x y hx hy hτ => ?_⟩
  · obtain ⟨C, hC⟩ := scode_exists_l I hZF hω
    refine ⟨C, hC, fun a f v ha hf hv assign => ?_⟩
    obtain ⟨l, F, r, code⟩ := (hC a).mp ha
    obtain ⟨b, hb, bound⟩ := sbound_exists_l I hZF hω code.2.1
    have sub := hω.transitive hZF b hb
    obtain ⟨s, hs⟩ := ZF.exists_restriction hZF I f b
    obtain ⟨t, ht⟩ := ZF.exists_restriction hZF I v b
    have sf := fn0_of_function_l (ZF.modelsKP hZF) (hs.isSetFunctionFromTo hf sub)
    have tf := fn0_of_function_l (ZF.modelsKP hZF) (ht.isSetFunctionFromTo hv sub)
    obtain ⟨q, hq⟩ := cp0_exists_l (ZF.modelsKP hZF) sf hι
    obtain ⟨n, hnω, qn⟩ := at_index_bound_l hZF hω hb hq.1
    obtain ⟨p, node, res⟩ := branch n hnω
    have source : Cp0_d b ω A q e s := ⟨sf, fun u hu => by
      obtain ⟨x, hx, hux⟩ := sf.2.1 u hu
      obtain ⟨i, hi, hxi⟩ := hι.2.1 x hx
      exact ⟨i, hi, x, hx, (hq.value_l sf hι hux).mpr hxi, hsect x i hxi, hux⟩⟩
    have target : Cp0_d b n B q p t := ⟨tf, fun u hu => by
      obtain ⟨x, hx, hux⟩ := sf.2.1 u hu
      obtain ⟨i, hi, hxi⟩ := hι.2.1 x hx
      obtain ⟨y, hy, hxy⟩ := hj.1.2.1 x hx
      have hui := (hq.value_l sf hι hux).mpr hxi
      have huv := assign u (sub u hu) x y ((hs.2 u x).mp hux).2 hxy
      exact ⟨i, (qn.bound_l hui).2, y, hy, hui,
        (res.2 i y).mpr ⟨(qn.bound_l hui).2, (hj.value_l hι hg hxi).mp hxy⟩, (ht.2 u y).mpr ⟨hu, huv⟩⟩⟩
    obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF I b A
    obtain ⟨D, hD⟩ := ZF.exists_functionSpace hZF I b B
    obtain ⟨E₀, hE₀⟩ := ZF.exists_functionSpace hZF I ω A
    obtain ⟨D₀, hD₀⟩ := ZF.exists_functionSpace hZF I ω B
    have left := ssat_spaces_l I hZF (R := R) code.2.1 bound hE₀ hE sub (fun _ h => h) code.2.2
      ((hE₀ f).mpr hf) ((hE s).mpr (fn0_function_l (ZF.modelsKP hZF) sf))
      (fun i x hi => ((hs.2 i x).trans (and_iff_right hi)).symm)
    have right := ssat_spaces_l I hZF (R := S) code.2.1 bound hD₀ hD sub (fun _ h => h) code.2.2
      ((hD₀ v).mpr hv) ((hD t).mpr (fn0_function_l (ZF.modelsKP hZF) tf))
      (fun i x hi => ((ht.2 i x).trans (and_iff_right hi)).symm)
    exact (satisfies_decode_l I hZF.1 hm code hE₀).trans (left.trans
      ((node.elementary b l F E D q s t hb code.2.1 bound hE hD qn source target r code.2.2).trans
        (right.symm.trans (satisfies_decode_l I hZF.1 hn code hD₀).symm)))
  · obtain ⟨i, hi, hxi⟩ := hι.2.1 x hx
    obtain ⟨n, hni, hnω⟩ := hω.1.2 i hi
    obtain ⟨p, node, res⟩ := branch n hnω
    exact (hj.value_l hι hg hxi).mpr ((res.2 i y).mp
      (node.prescribed i hni.predecessor_mem x hx y hy (hsect x i hxi) hτ)).2

end YesMetaZFC.SetTheory.Internal
