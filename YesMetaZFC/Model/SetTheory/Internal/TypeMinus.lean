import YesMetaZFC.Model.SetTheory.Internal.TypeMinusSyntax
import YesMetaZFC.Model.SetTheory.Internal.TypeQueryClosure

/-! # 前驱类型由同一元组在前一秩层实现

查询域不变，名字列不变；每个合法公式都有实际限制代码。
纯语法证书的正确性使所有编译结果给出同一真值，故逆像正是前一层的完整类型。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem tm_query_exists_l {ω p z e a : M.Domain} (hω : M.IsOmega ω) (hp : (I).Codes p z e)
    (hz : Sc_num_d I ω a z) : ∃ q, Tm_query_d I ω p q := by
  have code := hz
  obtain ⟨n, F, r, _, _, ha, _⟩ := code
  obtain ⟨a', m, G, u, ha', lower⟩ := sr_minus_formula_l I hZF hω ha
  obtain ⟨z', hz'⟩ := sc_num_exists_l I hZF hω ha'
  obtain ⟨q, hq⟩ := (I).total z' e
  exact ⟨q, z, e, z', hp, hq, a, a', n, F, r, m, G, u, hz, hz', ha, ha', lower⟩

theorem Tm_query_d.pool_l {ω p q n U D : M.Domain} (hω : M.IsOmega ω)
    (h : Tm_query_d I ω p q) (pool : Tt_pool_d I ω n U D) (hp : M.mem p D) : M.mem q D := by
  obtain ⟨z, e, z', cp, cq, _, a', _, _, _, _, _, _, _, hz', _⟩ := h
  obtain ⟨N, E, _, _, prod⟩ := pool
  obtain ⟨v, _, s, he, code⟩ := (prod p).mp hp
  obtain ⟨ez, ee⟩ := (I).injective code cp
  subst v s
  exact (prod q).mpr ⟨z', sc_num_natural_l I hZF hω hz', e, he, cq⟩

theorem Tm_query_d.slots_l {ω p q D : M.Domain} (hω : M.IsOmega ω)
    (h : Tm_query_d I ω p q) (slots : Tt_slots_d ω D) : M.mem p D ↔ M.mem q D := by
  obtain ⟨z, e, w, cp, cq, code⟩ := h
  have zw := code.natural_l I hZF hω
  constructor
  · intro hp
    obtain ⟨q', hq', cq'⟩ := slots p z e w hp zw.1 zw.2 cp
    exact kpair_unique_l M hZF.1 cq' cq ▸ hq'
  · intro hq
    obtain ⟨p', hp', cp'⟩ := slots q w e z hq zw.2 zw.1 cq
    exact kpair_unique_l M hZF.1 cp' cp ▸ hp'

theorem Tm_query_d.sat_l {ω c X R d Y S n s δ p q z b e a f : M.Domain}
    (hω : M.IsOmega ω) (h : Tm_query_d I ω p q)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hY : M.TransitiveSet Y) (top : Sr_top_d Y X)
    (hp : (I).Codes p z e) (hz : M.mem z ω) (hb : M.mem b ω) (he : M.IsDomainOf I b e)
    (ha : Tn_assign_d n s δ e a) (hf : Senv_fill_d I ω δ b a f) (ff : Fn0_d ω X f) :
    Tt_query_d I ω c n s δ p ↔ Tt_query_d I ω d n s δ q := by
  obtain ⟨z₀, e₀, z', cp, cq, c₀, c₁, l, F, r, m, G, u, code₀, code₁, form₀, form₁, lower⟩ := h
  obtain ⟨ez, ee⟩ := (I).injective cp hp
  subst z₀ e₀
  exact (tt_query_decode_l I (ZF.modelsKP hZF) hp hz hb he ha hf).trans
    ((sc_sat_decode_l I hZF hω code₀).trans ((lower.satisfies_l I hZF hω form₀ form₁ hm hn hY top
      (fn0_function_l (ZF.modelsKP hZF) ff)).trans ((sc_sat_decode_l I hZF hω code₁).symm.trans
        (tt_query_decode_l I (ZF.modelsKP hZF) cq (sc_num_natural_l I hZF hω code₁) hb he ha hf).symm)))

/-- 最大元素给出的限制类型自动存在，且由原元组及同一常量域实现。 -/
theorem Tt_realized_d.minus_l {ω d Y S n s δ U D t X : M.Domain} (hω : M.IsOmega ω)
    (h : Tt_realized_d I ω d Y S n s δ U D t) (model : Smem_d I d Y S)
    (hY : M.TransitiveSet Y) (top : Sr_top_d Y X) (tuple : Fn0_d n X s)
    (point : M.mem δ X) (constants : M.MemberSubset U X) : ∃ c R u,
      Smem_d I c X R ∧ Tm_minus_d I ω D t u ∧ Tt_realized_d I ω c X R n s δ U D u := by
  obtain ⟨c, R, code⟩ := smdl_membership_l I hZF ⟨δ, point⟩
  obtain ⟨u, truth, _⟩ := tt_truth_exists_l I hZF ω c n s δ D
  refine ⟨c, R, u, code, ?_, ⟨code.1, h.finite, tuple, point, constants, h.pool, truth⟩⟩
  intro p
  refine (truth p).trans (and_congr_right fun hpD => ?_)
  obtain ⟨z, b, e, a, f, hp, hz, hb, he, ha, hf, ff, decode⟩ :=
    Tt_pool_d.realize_l hZF (c := c) hω h.finite tuple point constants h.pool hpD
  constructor
  · intro hp'
    obtain ⟨a₀, code₀, _⟩ := decode.mp hp'
    obtain ⟨q, hq⟩ := tm_query_exists_l hZF hω hp code₀
    exact ⟨q, hq, (h.truth q).mpr ⟨hq.pool_l hZF hω h.pool hpD,
      (hq.sat_l hZF hω code model hY top hp hz hb he ha hf ff).mp hp'⟩⟩
  · rintro ⟨q, hq, hqt⟩
    exact (hq.sat_l hZF hω code model hY top hp hz hb he ha hf ff).mpr ((h.truth q).mp hqt).2

/-- Neeman 3.5 的类型保持结论：V(η+1) 中的类型经限制后，由同一元组在 Vη 中实现。 -/
theorem tt_minus_rank_l {ω ν μ X Y d S n s δ U D t : M.Domain} (hω : M.IsOmega ω)
    (hV : V_d I ν X) (hW : V_d I μ Y) (hs : M.SuccessorOf μ ν)
    (h : Tt_realized_d I ω d Y S n s δ U D t) (model : Smem_d I d Y S)
    (tuple : Fn0_d n X s) (point : M.mem δ X) (constants : M.MemberSubset U X) : ∃ c R u,
      Smem_d I c X R ∧ Tm_minus_d I ω D t u ∧ Tt_realized_d I ω c X R n s δ U D u :=
  h.minus_l hZF hω model (ZF.v_transitive_l I hZF hW)
    (sr_top_power_l (ZF.v_successor_l I hZF hV hW hs)) tuple point constants

/-- 缩小常量域与取前驱交换；实际构造限制后的前驱，而非另加投影存在前提。 -/
theorem tm_minus_project_l {ω D E t t₀ u : M.Domain} (hω : M.IsOmega ω)
    (small : Tt_slots_d ω D) (large : Tt_slots_d ω E) (sub : M.MemberSubset t E)
    (cut : ∀ p, M.mem p t₀ ↔ M.mem p D ∧ M.mem p t) (h : Tm_minus_d I ω E t u) :
    ∃ u₀, Tm_minus_d I ω D t₀ u₀ ∧ ∀ p, M.mem p u₀ ↔ M.mem p D ∧ M.mem p u := by
  obtain ⟨u₀, h₀⟩ := tm_minus_exists_l I hZF ω D t₀
  refine ⟨u₀, h₀, fun p => (h₀ p).trans ⟨?_, ?_⟩⟩
  · rintro ⟨hp, q, code, hq⟩
    have qt := ((cut q).mp hq).2
    exact ⟨hp, (h p).mpr ⟨(code.slots_l hZF hω large).mpr (sub q qt), q, code, qt⟩⟩
  · rintro ⟨hp, hu⟩
    obtain ⟨_, q, code, hq⟩ := (h p).mp hu
    exact ⟨hp, q, code, (cut q).mpr ⟨(code.slots_l hZF hω small).mp hp, hq⟩⟩

end YesMetaZFC.SetTheory.Internal
