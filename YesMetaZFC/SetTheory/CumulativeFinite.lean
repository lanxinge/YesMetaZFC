import YesMetaZFC.SetTheory.CumulativeFunction
import YesMetaZFC.SetTheory.Card.FiniteOrdinal

/-! # 极限秩层中的内部有限函数闭包

把实际函数值的秩组成有限序数集，再取严格公共界。长度取自模型自己的 ω，
因此非标准有限列同样封闭；不要求极限秩层具有不可数共尾度。
-/
namespace YesMetaZFC.SetTheory.ZF
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "Q" => kp_pair_l (modelsKP hZF)

theorem v_finite_function_l {ω η Y n F : M.Domain} (hω : M.IsOmega ω)
    (hη : M.IsLimitOrdinal η) (hY : V_d Q η Y) (hωY : M.mem ω Y) (hn : M.mem n ω)
    (hf : M.IsSetFunctionFromTo Q F n Y) :
    ∃ C, M.mem C Y ∧ M.IsSetFunctionFromTo Q F n C ∧ M.mem F Y := by
  let ρ : Env M 2 := ⟨Fin.cases F (fun _ => Y), fun _ => F⟩
  let φ : BinarySchema 2 := {
    body := Formula.existsMem (.bound 3)
      (.conj (rd_entry0_m (.bound 2) .newest (.bound 3)) (rk_m (𝒞 := kpair_convention_l) .newest (.bound 1))) }
  have sat i α : φ.denote ρ i α ↔ ∃ x, M.mem x Y ∧ Rd_entry_d i x F ∧ Rk_d Q x α := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      rd_entry0_sat_l hZF.1, rk_sat_l Q hZF.1]
    rfl
  obtain ⟨G, hg, graph⟩ := exists_setFunctionFromTo_of_denote hZF Q φ ρ (source := n) (target := η)
    (fun i hi => by
      obtain ⟨x, hx, hix⟩ := hf.2.2 i hi
      obtain ⟨α, hα⟩ := rk_exists_l Q hZF x
      exact ⟨α, (sat i α).mpr ⟨x, hx, hix, hα⟩⟩)
    (fun i _ α β ha hb => by
      obtain ⟨x, _, hix, ha⟩ := (sat i α).mp ha
      obtain ⟨y, _, hiy, hb⟩ := (sat i β).mp hb
      exact rk_unique_l Q hZF.1 ha (hf.1.2 i y x hiy hix ▸ hb))
    (fun i α _ h => by
      obtain ⟨x, hx, _, hα⟩ := (sat i α).mp h
      exact (rk_mem_l Q hZF hα hY).mp hx)
  obtain ⟨S, range⟩ := exists_range_of_setFunction hZF Q hg.1 hg.2.1
  have gs : M.IsSetFunctionFromTo Q G n S := ⟨hg.1, hg.2.1,
    fun i hi => (hg.2.2 i hi).imp fun α ha => ⟨(range α).mpr ⟨i, ha.2⟩, ha.2⟩⟩
  have finite : Finite_d Q ω S := ⟨n, hn, ordinal_image_bound_l Q hZF (hω.members_areOrdinals (ZF.modelsKP hZF) n hn)
    (exists_inclusionInjection hZF Q (source := n) (fun _ h => h)) gs
    (fun α hα => ((range α).mp hα).imp fun i hi => ⟨hg.input_mem_of_pairMember hi, hi⟩)⟩
  have union : M.IsUnionOf η η := fun i => ⟨fun hi => (hη.2.2 i hi).imp fun j hj => ⟨hj.1, hj.2⟩,
    fun ⟨j, hj, hij⟩ => hη.1.transitive j hj i hij⟩
  obtain ⟨ξ, hξ, bound⟩ := finite_union_bound_l Q hZF hω hη.1 union hη.2.1 finite
    (fun α hα => ((range α).mp hα).elim fun _ hi => hg.output_mem_of_pairMember hi)
  obtain ⟨C, hc⟩ := v_exists_l Q hZF (hη.1.mem hξ)
  have hCY := v_mem_l Q hZF hc hY hξ
  have values i x (hx : M.PairMember Q i x F) : M.mem x C := by
    obtain ⟨α, _, hα⟩ := hg.2.2 i (hf.input_mem_of_pairMember hx)
    obtain ⟨y, _, hy, rank⟩ := (sat i α).mp ((graph i α).mp hα).2
    exact (rk_mem_l Q hZF (hf.1.2 i y x hy hx ▸ rank) hc).mpr (bound α ((range α).mpr ⟨i, hα⟩))
  have fc : M.IsSetFunctionFromTo Q F n C := ⟨hf.1, hf.2.1,
    fun i hi => (hf.2.2 i hi).imp fun x hx => ⟨values i x hx.2, hx.2⟩⟩
  obtain ⟨B, hB, hnB, hcB⟩ := v_joint_bound_l Q hY (v_transitive_l Q hY ω hωY n hn) hCY
  exact ⟨C, hCY, fc, v_relation_mem_l Q hY hη hB fun p hp =>
    (fn0_of_function_l (modelsKP hZF) fc).1 p hp |>.elim fun i hi => hi.2.elim fun x hx =>
      ⟨i, hnB i hi.1, x, hcB x hx.1, hx.2⟩⟩

end YesMetaZFC.SetTheory.ZF
