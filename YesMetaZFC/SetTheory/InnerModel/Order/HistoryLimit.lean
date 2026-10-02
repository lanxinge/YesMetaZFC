import YesMetaZFC.SetTheory.InnerModel.Order.Seen

/-! # 极限索引处短历史的层内集合化

较早层中的可见证书恰对应较小索引。由有界查询构造索引集、前段图、值域、
后继像及坐标像；旧见证统一界在该较早层中，再作有限装配。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem js_limit_in_l (hM : M.Models KPi) {C a B R p : M.Domain} (hC : Rd_closed_d C)
    (hc : M.TransitiveSet C) (hBC : M.mem B C) (ρ : Env M 0) (ha : M.IsLimitOrdinal a)
    (hp : Js_state_d a p) (hpBR : KPair_d M p B R)
    (ih : ∀ b, M.mem b a → ∃ q, Si_cert_d B (rc_value_s rw_op_s) ρ b q) :
    Si_cert_d C (rc_value_s rw_op_s) ρ a p := by
  let hKP := (KPi.models_iff_l.mp hM).1
  have level : Js_value_d a B R := ⟨p, hp, hpBR⟩
  have bt := (js_coherence_l hM ha.1 level).1
  have closed := js_limit_closed_l hM ha level
  have find b hb : ∃ q, Js_seen_d ρ B b q := (ih b hb).imp fun q h => js_seen_of_in_l hKP bt (ha.1.mem hb) h
  have seen b (hb : M.mem b a) q (hq : Js_state_d b q) : Js_seen_d ρ B b q := by
    obtain ⟨r, hr⟩ := find b hb
    exact js_state_unique_l hM hr.state_l hq ▸ hr
  have params : ∀ i, M.mem ((ρ.push B).bound i) C ∧ M.MemberSubset ((ρ.push B).bound i) B :=
    Fin.cases ⟨hBC, fun _ h => h⟩ (fun i => Fin.elim0 i)
  -- 可见证书恰来自更小索引，因此索引过滤器恢复 a 本身。
  obtain ⟨I, hIC, hi⟩ := rd_bounded_filter_l hKP hC hc hBC bt js_indices_s (ρ.push B) params
  have eq : I = a := by
    apply hKP.1.eq_of_same_members; intro b
    rw [hi b, js_indices_sat_l hKP ρ]
    exact ⟨fun ⟨_, q, _, h⟩ => js_seen_lt_l hM ha.1 level h, fun hb =>
      (find b hb).elim fun q h => ⟨h.2.1, q, h.2.2.1, h⟩⟩
  have hAC : M.mem a C := eq ▸ hIC
  obtain ⟨F, hFC, hf⟩ := rd_bounded_filter_l hKP hC hc hBC bt js_rows_s (ρ.push B) params
  have fm r : M.mem r F ↔ M.mem r B ∧ ∃ b, M.mem b B ∧ ∃ q, M.mem q B ∧ KPair_d M r b q ∧ Js_seen_d ρ B b q :=
    (hf r).trans (and_congr_right fun _ => js_rows_sat_l hKP ρ B r)
  have entry b q : Rd_entry_d b q F ↔ M.mem b a ∧ Js_state_d b q := by
    constructor
    · rintro ⟨r, hr, hrF⟩
      obtain ⟨_, c, _, z, _, hz, h⟩ := (fm r).mp hrF
      obtain ⟨rfl, rfl⟩ := kpair_injective_l M hz hr
      exact ⟨js_seen_lt_l hM ha.1 level h, h.state_l⟩
    · rintro ⟨hb, hq⟩
      have h := seen b hb q hq
      obtain ⟨r, hr⟩ := (kp_pair_l hKP).total b q
      have hrB := closed .opair b q b h.2.1 h.2.2.1 h.2.1 r (rd_opair_value_l hKP.1 hr)
      exact ⟨r, hr, (fm r).mpr ⟨hrB, b, h.2.1, q, h.2.2.1, hr, h⟩⟩
  have fn : Fn0_d a B F := by
    refine ⟨?_, ?_, fun b _ q _ r _ hq hr => js_state_unique_l hM ((entry b q).mp hq).2 ((entry b r).mp hr).2⟩
    · intro r hrF
      obtain ⟨_, b, _, q, hq, hr, h⟩ := (fm r).mp hrF
      exact ⟨b, js_seen_lt_l hM ha.1 level h, q, hq, hr⟩
    · intro b hb
      obtain ⟨q, h⟩ := find b hb
      exact ⟨q, h.2.2.1, (entry b q).mpr ⟨hb, h.state_l⟩⟩
  -- 由相同的有界查询构造前段图的值域与后继像，不在 B 内调用收集。
  obtain ⟨X, hXC, hx⟩ := rd_bounded_filter_l hKP hC hc hBC bt js_values_s (ρ.push B) params
  have xm q : M.mem q X ↔ M.mem q B ∧ ∃ b, M.mem b B ∧ Js_seen_d ρ B b q :=
    (hx q).trans (and_congr_right fun _ => js_values_sat_l hKP ρ B q)
  have xsub q hq := ((xm q).mp hq).1
  have range : Rd_fun_d .range F F F X := by
    intro q; apply (xm q).trans
    exact ⟨fun ⟨_, b, _, h⟩ => ⟨b, (entry b q).mpr ⟨js_seen_lt_l hM ha.1 level h, h.state_l⟩⟩,
      fun ⟨b, h⟩ => let s := seen b ((entry b q).mp h).1 q ((entry b q).mp h).2; ⟨s.2.2.1, b, s.2.1, s⟩⟩
  have step x (hx : M.mem x X) q (h : Rw_state_d x q) : Si_cert_d B rw_state_s ρ x q := by
    obtain ⟨_, b, _, hs⟩ := (xm x).mp hx
    exact js_seen_step_in_l hM closed bt hs h
  obtain ⟨Y, hYC, hy⟩ := si_bounded_image_l hKP hC hc hBC bt hXC xsub rw_state_s ρ
  have ysub q hq := ((hy q).mp hq).1
  have image q : M.mem q Y ↔ ∃ x, M.mem x X ∧ Rw_state_d x q := by
    constructor
    · intro hq
      obtain ⟨_, x, hx, w, _, hw⟩ := (hy q).mp hq
      exact ⟨x, hx, (rw_state_sat_l hKP ρ x q).mp ((rw_state_s.sat_l ρ x q).mpr ⟨w, hw⟩)⟩
    · rintro ⟨x, hx, h⟩
      obtain ⟨w, hwB, _, hqw, hw⟩ := step x hx q h
      exact (hy q).mpr ⟨bt w hwB q hqw, x, hx, w, hwB, hw⟩
  have projection i q (hq : M.mem q Y) v (hv : Rp_proj_d i q v) : M.mem v B := by
    obtain ⟨x, _, A, Q, V, S, _, _, _, hp⟩ := (image q).mp hq
    have bounds := po_pair_bound_l bt (ysub q hq) hp
    have he := (rp_proj_pair_l hKP.1 hp i).mp hv
    rw [he]; cases i <;> first | exact bounds.1 | exact bounds.2
  obtain ⟨D, hDC, dsub, hd⟩ := rp_image_bounded_l hKP hC hc hBC bt hYC ysub false ρ (projection false)
  obtain ⟨E, hEC, esub, he⟩ := rp_image_bounded_l hKP hC hc hBC bt hYC ysub true ρ (projection true)
  obtain ⟨X', Y', hx', hy', join⟩ := (rw_op_sat_l hKP ρ F p).mp (js_prefix_op_l hM ρ hp fn entry)
  have eq := rd_fun_unique_l hKP.1 hx' range; subst X'
  have eq := hKP.1.eq_of_same_members Y' Y (fun q => (hy' q).trans (image q).symm); subst Y'
  have coords := join.coordinates_l hpBR
  have hDU := rp_image_union_l hd coords.1
  have hER := rp_image_union_l he coords.2
  have hRC := hC .union E E E hEC hEC hEC R hER
  have rsub : M.MemberSubset R B := by
    intro x hx; obtain ⟨A, hAE, hxA⟩ := (hER x).mp hx; exact bt A (esub A hAE) x hxA
  obtain ⟨T, hTC, ht, bsub, hL⟩ := rd_finite_bounded_l hKP hC hBC bt [X, Y, D, E, B, R] (by
    intro Z hZ; simp only [List.mem_cons, List.not_mem_nil, or_false] at hZ
    rcases hZ with h | h | h | h | h | h
    · exact h ▸ ⟨hXC, xsub⟩
    · exact h ▸ ⟨hYC, ysub⟩
    · exact h ▸ ⟨hDC, dsub⟩
    · exact h ▸ ⟨hEC, esub⟩
    · subst Z; exact ⟨hBC, fun _ h => h⟩
    · exact h ▸ ⟨hRC, rsub⟩)
  have im : Formula.satisfies (((ρ.push X).push Y).push B) rw_state_s.image.matrix.body := by
    apply (rw_state_s.image_matrix_l ρ X Y B).mpr
    constructor
    · intro x hx
      obtain ⟨q, hq⟩ := rw_state_total_l hKP x
      obtain ⟨w, hwB, _, _, hw⟩ := step x hx q hq
      exact ⟨q, (image q).mpr ⟨x, hx, hq⟩, w, hwB, hw⟩
    · intro q hq; exact ((hy q).mp hq).2
  have op := rw_op_in_l hKP hC hTC ht ρ
    ⟨X, Y, D, E, B, R, hL X (by simp), hL Y (by simp), hL D (by simp), hL E (by simp),
      hL B (by simp), hL R (by simp), range, hd, he, hDU, hER, hpBR, rw_state_s.image_mono_l ρ im bsub⟩
  obtain ⟨K, hKC, hk, _, hFK⟩ := rd_bounded_enclosed_l hKP hC hBC bt hFC (fun r hr => ((fm r).mp hr).1)
  -- 所有旧限制图和计算见证都界在 B 内，最后只需有限装配。
  obtain ⟨W, hWC, cert⟩ := rc_local_cover_l hKP hC hBC bt ha.1.transitive fn
    (rd_transitive_enclosed_l hKP hC hAC ha.1.transitive) ⟨K, hKC, hk, hFK⟩ rw_op_s ρ (by
      intro b hb q hbq
      obtain ⟨r, hi⟩ := ih b hb
      have eq := js_state_unique_l hM ((js_state_env_l ρ b r).mp hi.sound_l) ((entry b q).mp hbq).2
      subst r
      obtain ⟨Z, hZB, _, _, hm⟩ := hi
      obtain ⟨G, hGZ, w, hwZ, fnG, ge, gw⟩ := js_witness_prefix_l hM ρ hm
      refine ⟨G, bt Z hZB G hGZ, w, bt Z hZB w hwZ, ⟨(fn0_function_l hKP fnG).1.1, fun c v => ?_⟩, gw⟩
      exact (ge c v).trans (and_congr_right fun hcb =>
        ⟨fun h => (entry c v).mpr ⟨ha.1.transitive b hb c hcb, h⟩, fun h => ((entry c v).mp h).2⟩))
  exact rc_local_extend_l hKP hC hc cert hWC op

end YesMetaZFC.SetTheory.InnerModel
