import YesMetaZFC.SetTheory.LargeCardinal.TypeElastic

/-! # 只从两条定义域查询读取实际前驱

此步不使用伸展或不可达性：ZF 已足以从裸类型中的原查询得到
后继高度、下降后的原元组及完整前驱类型。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ee_language_d.defined_l {ω κ n B U D δ η Y c R s t : M.Domain} {q : Ee_queries_d M}
    (language : Ee_language_d hZF ω κ n B U D q) (hω : M.IsOmega ω)
    (hY : V_d I η Y) (model : Smem_d I c Y R) (type : Tt_realized_d I ω c Y R n s δ U D t)
    (defined : Ee_defined_d q t) :
    ∃ ν A b Q v, M.SuccessorOf η ν ∧ V_d I ν A ∧ Smem_d I b A Q ∧
      Ee_minus_d I ω D q t v ∧ Tt_realized_d I ω b A Q n s δ U D v := by
  obtain ⟨ν, succ⟩ := (language.successor η Y c R s δ t hY model type).mp defined.1
  obtain ⟨A, hA⟩ := ZF.v_exists_l I hZF ((v_ordinal_l I hY).mem succ.predecessor_mem)
  have hwU := (tt_constants_finite_l hZF hω type.finite language.limit language.rank language.constants).1
  have hων : M.MemberSubset ω ν := by
    rcases (succ ω).mp (ZF.v_ordinal_height_l hZF hY (hω.isOrdinal hZF) (type.constants ω hwU)) with lt | eq
    · exact (v_ordinal_l I hA).transitive ω lt
    · exact fun x hx => (eq x).mp hx
  obtain ⟨tuple, point, critical⟩ := (language.domain ν η A Y c R s δ t hA hY succ hων model type).mp defined.2
  have hkν := ZF.v_ordinal_height_l hZF hA language.limit.1 critical
  have sub := ZF.v_mono_l I hZF language.rank hA ((v_ordinal_l I hA).transitive κ hkν)
  obtain ⟨b, Q, v, lower, minus, realized⟩ := tt_minus_rank_l hZF hω hA hY succ type model tuple point
    (fun x hx => ((language.constants x).mp hx).elim (sub x) (fun eq => eq.symm ▸ critical))
  exact ⟨ν, A, b, Q, v, succ, hA, lower, ⟨defined, minus⟩, realized⟩

end YesMetaZFC.SetTheory.LargeCardinal
