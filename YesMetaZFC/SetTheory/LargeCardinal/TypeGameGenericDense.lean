import YesMetaZFC.SetTheory.LargeCardinal.TypeGameGenericMove
import YesMetaZFC.SetTheory.CumulativeFinite

/-! # 有限坍缩条件中强制出现可继续请求

任意给定内部有限条件先延长至指定编号之后，再统一界定已有值与节点参数的秩。
武丁继续工厂给出更高 κ；把同一个合法请求追加到条件末尾，所有较早值均在 Vκ。
这里保留请求的实际完整类型及其实现高度，供下一次严格下降使用。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_setup_d.generic_dense_l {p : Tg_params_d M.Domain}
    {X ℓ a₀ ℓ₀ t₀ κ₀ u₀ b₀ j k N τ B U D w η Y c R r g β s t g' x F f E : M.Domain}
    {q₀ : Tg_reply_queries_d M}
    (setup : Tg_setup_d hZFC p X) (hd : Woodin_d I p.δ) (hℓ : M.mem ℓ p.ω)
    (oldMove : Tg_aux_data_d a₀ ℓ₀ t₀ κ₀ u₀) (oldAnswer : KPair_d M b₀ τ w)
    (ft₀ : Fn0_d j p.ω t₀) (hk : M.SuccessorOf k j) (hN : M.SuccessorOf N k)
    (ft : Fn0_d k p.ω t) (cut : M.IsRestrictionOf I t₀ t j)
    (oldLanguage : Tg_reply_language_d hZF p.ω p.e k N τ B U D q₀)
    (hY : V_d I η Y) (model : Smem_d I c Y R) (type : Tt_realized_d I p.ω c Y R N r p.δ U D w)
    (rS : Rd_entry_d p.e p.S r) (last : Rd_entry_d k β r) (set : Sg_set_d I p.e k r g)
    (bound : Tg_bound_d I p.δ p.S β) (height : Tg_height_d β η)
    (node : Tg_node_d I k p.S s t g') (extend : ∀ a, M.mem a g' ↔ M.mem a g ∨ a = x)
    (hτ : M.mem τ p.δ) (hs : M.mem s X) (ht : M.mem t X)
    (space : Fseq_space_d I p.ω X F) (hf : M.mem f F) (hE : M.mem E p.ω) :
    ∃ κ C a u μ A d H m V P r' i q,
      M.mem κ p.δ ∧ V_d I κ C ∧ M.mem a X ∧ Tg_aux_data_d a ℓ t κ u ∧
      M.SuccessorOf μ β ∧ V_d I μ A ∧ Smem_d I d A H ∧ M.SuccessorOf m N ∧ (∀ x, M.mem x V ↔ M.mem x C ∨ x = κ) ∧
      Tt_realized_d I p.ω d A H m r' p.δ V P u ∧ Rd_entry_d p.e p.S r' ∧ Rd_entry_d N β r' ∧ Sg_set_d I p.e N r' g' ∧
      M.mem q F ∧ M.MemberSubset f q ∧ M.mem E i ∧ M.mem i p.ω ∧ Rd_entry_d i a q ∧
      (∀ j y, M.mem j i → Rd_entry_d j y q → M.mem y C) ∧
      ∀ n h z, Tg_digits_d hZF p.c p.b n p.A h z → M.IsRestrictionOf I s z k → M.mem ℓ n →
        Tg_event_d I p.c ℓ p.e h a₀ → Tg_event_d I p.c ℓ p.a h b₀ →
        Tg_growth_d hZF p.e p.c p.A n h κ C → Tg_aux_d hZF p n h a := by
  obtain ⟨n, hn, fn⟩ := (space f).mp hf
  have on := setup.omega.members_areOrdinals hZF n hn
  have oE := setup.omega.members_areOrdinals hZF E hE
  obtain ⟨E', succ, hE'⟩ := setup.omega.1.2 E hE
  have fit : ∃ i, M.mem i p.ω ∧ M.mem E i ∧ M.MemberSubset n i := by
    rcases on.trichotomy hZF.1 oE (KP.difference_exists_d (ZF.modelsKP hZF))
        (KP.intersection_exists_d (ZF.modelsKP hZF) n E) with eq | lt | gt
    · exact ⟨E', hE', succ.predecessor_mem, fun a ha => (succ a).mpr (Or.inl ((eq a).mp ha))⟩
    · exact ⟨E', hE', succ.predecessor_mem, fun a ha => (succ a).mpr (Or.inl (oE.transitive n lt a ha))⟩
    · exact ⟨n, hn, gt, fun _ ha => ha⟩
  obtain ⟨i, hi, hEi, ni⟩ := fit
  have oi := setup.omega.members_areOrdinals hZF i hi
  have hwX := ZF.v_ordinal_mem_l I hZF setup.rank setup.above
  have tr := ZF.v_transitive_l I hZF setup.rank
  have heω := num_mem_l hZF.1 setup.omega (show Num_d 0 p.e from setup.empty)
  obtain ⟨b, fill, fb⟩ := senv_fill_exists_l I hZF fn (tr p.ω hwX p.e heω)
  obtain ⟨f₀, restrict⟩ := ZF.exists_restriction hZF I b i
  have ff₀ := restrict.isSetFunctionFromTo fb (setup.omega.transitive hZF i hi)
  have kept a y (ay : Rd_entry_d a y f) : Rd_entry_d a y f₀ := by
    have ha := fn.input_mem_of_pairMember ay
    exact (restrict.2 a y).mpr ⟨ni a ha, (fill.2 a y).mpr
      ⟨setup.omega.transitive hZF n hn a ha, Or.inl ⟨ha, ay⟩⟩⟩
  obtain ⟨C₀, hC₀, values, _⟩ := ZF.v_finite_function_l hZF setup.omega setup.limit setup.rank hwX hi ff₀
  -- 同时界定整段已有枚举值、两张节点图与旧回答的参数域。
  have algebra := sc_v_algebra_l hZFC setup.limit setup.rank
  obtain ⟨S₀, hS₀, pair₀⟩ := algebra.pair s t hs ht
  obtain ⟨T₀, hT₀, pair₁⟩ := algebra.pair S₀ τ hS₀ (ZF.v_ordinal_mem_l I hZF setup.rank hτ)
  obtain ⟨Z₀, hZ₀, cZ, tZ⟩ := ZF.v_joint_bound_l I hZF setup.rank hC₀ hT₀
  obtain ⟨χ, Z, hχ, hZ, zz⟩ := (ZF.v_unfold_l I hZF setup.rank Z₀).mp hZ₀
  have trZ := ZF.v_transitive_l I hZF hZ
  have hS₀Z := zz S₀ (tZ S₀ ((pair₁ S₀).mpr (Or.inl rfl)))
  have hτZ := zz τ (tZ τ ((pair₁ τ).mpr (Or.inr rfl)))
  have hτχ := ZF.v_ordinal_height_l hZF hZ oldLanguage.limit.1 hτZ
  obtain ⟨κ, C, a, u, μ, A, d, H, m, V, P, r', above, hκ, hC, ha, move, hμ, hA, lower,
    hm, constants, full, first, last', nextSet, legal⟩ := setup.generic_continue_l hZFC hd hℓ oldMove oldAnswer ft₀ hk hN ft cut
      oldLanguage hY model type rS last set bound height node extend hχ
      ((v_ordinal_l I hZ).transitive τ hτχ) hZ
      (trZ S₀ hS₀Z s ((pair₀ s).mpr (Or.inl rfl))) (trZ S₀ hS₀Z t ((pair₀ t).mpr (Or.inr rfl)))
  obtain ⟨i', si, hi'⟩ := setup.omega.1.2 i hi
  obtain ⟨q, fq, old, last⟩ := tt_column_append_l hZF oi si ff₀ ha
  have sub : M.MemberSubset f q := by
    intro v hv
    obtain ⟨j, y, pair⟩ := fn.1.1 v hv
    have jy : Rd_entry_d j y f := ⟨v, pair, hv⟩
    obtain ⟨v', cp, hv'⟩ := (old j y (ni j (fn.input_mem_of_pairMember jy))).mpr (kept j y jy)
    exact (kpair_unique_l M hZF.1 pair cp).symm ▸ hv'
  have before j y (hj : M.mem j i) (jy : Rd_entry_d j y q) : M.mem y C :=
    ZF.v_mono_l I hZF hZ hC ((v_ordinal_l I hC).transitive χ above) y
      (zz y (cZ y (values.output_mem_of_pairMember ((old j y hj).mp jy))))
  exact ⟨κ, C, a, u, μ, A, d, H, m, V, P, r', i, q, hκ, hC, ha, move, hμ, hA, lower, hm, constants,
    full, first, last', nextSet, (space q).mpr ⟨i', hi', fq⟩, sub, hEi, hi, last, before, legal⟩

end YesMetaZFC.SetTheory.LargeCardinal
