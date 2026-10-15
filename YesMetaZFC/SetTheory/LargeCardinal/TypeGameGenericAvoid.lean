import YesMetaZFC.SetTheory.LargeCardinal.TypeGameGenericCatch
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameGenericBranch
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameLevelReply
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameTracked

/-! # 6.1 泛型 I 方向的严格高度矛盾

反例分支给出真实地有限节点。旧实现关系中的已捕获高度有内部最小元；
原回答严格降低它，原稠密集与 6.6 又捕获同一分支的下一请求，从而矛盾。
整个下降使用原 subtype、exceeds 和固定查询表，目标模型只需 ZF。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} {N : Structure.{v}} (hZFC : M.Models ZFC) (hN : N.Models ZF)
variable (e : M.Domain → N.Domain) (hi : Function.Injective e)
  (he : ∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
local notation "hM" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hM)
local notation "J" => kp_pair_l (ZF.modelsKP hN)
include hi he

theorem Tg_setup_d.generic_no_branch_l {p : Tg_params_d M.Domain}
    {X F L G O σ R a Γ P Y S Q : M.Domain} {U : M.Domain → Prop} {g K D T f H τ : N.Domain}
    (setup : Tg_setup_d hZFC p X) (hd : Woodin_d I p.δ) (root : M.mem p.e p.S)
    (histories : Tg_histories_d hM p X F L) (owner : Tg_owner_d hM p.ω p.c p.a p.b O)
    (control : Cg_control_d I true p.ω p.e X F L G O σ R) (ha : M.mem a p.A)
    (hw : N.IsOmega (e p.ω)) (c : Cg_scanner_d hN (e p.ω) (e p.A) (e X) (e F) (e L) (e O) (e σ) g K D T)
    (surj : N.IsSetSurjectiveOnto J g (e p.ω) (e X)) (ff : Fn0_d (e p.ω) (e p.A) f)
    (values : ∀ s y, Rd_entry_d s y τ → Cg_scan_answer_d hN (e p.ω) (e p.A) (e F) T (e p.e) (e a) s y)
    (follows : Gm_follows_d J true (e p.ω) τ f) (run : Gi_d hN false (e p.ω) (e F) T (e p.e) (e a) f H)
    (space : Fseq_space_d I p.ω Y S) (prod : M.IsCartesianProduct I P p.ω Γ) (letters : M.IsCartesianProduct I Y p.A P)
    (order : ∀ q r, Entry_d M q r Q ↔ M.mem q F ∧ M.mem r F ∧ M.MemberSubset r q)
    (generic : Generic_d M F Q F U)
    (origin : ∀ q, U q → ∀ j y, Rd_entry_d j y q → Rd_entry_d (e j) (e y) g) :
    ¬ Tg_projection_d hN (e p.ω) (e Y) (e S) (e p.S) f := by
  intro bad
  -- 反例分支的每个内部有限前缀都来自地模型；实现高度则始终读取旧实现表。
  obtain ⟨t, G', ft, fg, nodes⟩ := bad.ground_nodes_l hM hN e hi he setup.omega hw space prod letters
    (fn0_function_l (ZF.modelsKP hN) ff)
  have heω := num_mem_l hM.1 setup.omega (show Num_d 0 p.e from setup.empty)
  obtain ⟨one, so, hone⟩ := setup.omega.1.2 p.e heω
  have eq := so.eq hM.1 setup.one; subst one
  obtain ⟨_, _, _, _, _, _, node₁, _⟩ := nodes p.a hone
  have notOrd := node₁.not_ordinal_l hM.1 (KP.exists_pair (ZF.modelsKP hM)) (KP.mem_irrefl_d (ZF.modelsKP hM)) setup.one.predecessor_mem
  obtain ⟨_, Z, rank, treeRank⟩ := setup.low.read_l hM setup.limit.1
  obtain ⟨V, table⟩ := tg_level_table_l hM p X Z
  have empty : ∀ y, ¬ N.mem y (e p.e) := fun y hy => (he p.e y).mp hy |>.elim fun x hx => setup.empty x hx.1
  have emptyCut (v : N.Domain) : N.IsRestrictionOf J (e p.e) v (e p.e) :=
    ⟨(tg_graph_empty_l J empty).1.1, fun i y => iff_of_false (fun ⟨q, _, hq⟩ => empty q hq) (fun h => empty i h.1)⟩
  have enumFn := fn0_function_l (ZF.modelsKP hN) c.enumeration
  have histFn := fn0_function_l (ZF.modelsKP hN) run.1
  have indexFn := fn0_function_l (ZF.modelsKP hN) c.indices
  have hwX := ZF.v_ordinal_mem_l I hM setup.rank setup.above
  have heX := ZF.v_transitive_l I hM setup.rank p.ω hwX p.e heω
  have initial : Tg_tracked_d hN (e p.ω) H K g (e V) t G' (e p.ν) := by
    obtain ⟨n, m, h, h', v, i, en, _, hn, nh, _, _, aux, _, ki, iv, _⟩ :=
      setup.generic_round_l hZFC hN e hi he hd root histories owner control ha hw c surj ff run ((image_member_l e hi he).mpr heω)
    have eq := hi en; subst n
    have saved := aux
    obtain ⟨ℓ, t₀, κ, u, k, l, n, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      data, hκ, f₀, sl, _, _, _, _, _, _, _, _, _, _, branch⟩ := saved
    have te : t₀ = p.e := branch.elim And.left (fun h => (setup.empty ℓ h.2.1).elim); subst t₀
    have ke : k = p.e := hM.1.eq_of_same_members k p.e (fun i => iff_of_false
      (fun hi => (f₀.2.1 i hi).elim fun y hy => hy.2.elim fun z hz => setup.empty z hz.2) (setup.empty i)); subst k
    have key : Tg_level_key_d hM p X Z v p.e p.e p.e p.ν :=
      ⟨(image_member_l e hi he).mp (c.enumeration.bound_l iv).2, heω, heX, fun x hx => (setup.empty x hx).elim,
        Or.inr rfl, ℓ, κ, u, p.a, data, hκ, f₀, setup.one, setup.level_reset_l hZFC aux data⟩
    exact table.track_l hM hN e hi he heω nh ki iv key (emptyCut t) (emptyCut G')
  -- 初始重置给出高度 ν，故已捕获高度非空。对实际原公式取内部最小元 α。
  obtain ⟨α, _, tracked, least⟩ := tg_tracked_min_l hN (image_ord_l hM hN e hi he (v_ordinal_l I rank)) initial
  obtain ⟨n, h, v, k, t₀, g₀, α₀, i, eα, hn, nh, ki, iv, key, rt, rg⟩ := table.read_tracked_l hM hN e he run.1 tracked
  subst α
  obtain ⟨hvX, hk, htX, hgZ, hαν, ℓ, κ, u, l, data, hκ, f₀, sl, level⟩ := key
  obtain ⟨n', m, h', hNext, v', i', en, sm, _, nh', mh, _, aux, ev, ki', iv', _, h₁, b, fh₁, answer, ae, be⟩ :=
    setup.generic_round_l hZFC hN e hi he hd root histories owner control ha hw c surj ff run ((image_member_l e hi he).mpr hn)
  have eq := hi en; subst n'
  have eq := hi (histFn.1.2 (e n) (e h') (e h) nh' nh); subst h'
  have eq := indexFn.1.2 (e h) i' i ki' ki; subst i'
  have eq := hi (enumFn.1.2 i (e v') (e v) iv' iv); subst v'
  obtain ⟨s₀, t₁, g₁, fs₀, _, fg₀, node₀, _, rt₁, rg₁⟩ := nodes k hk
  have eq := hi (rt₁.eq hN.1 rt); subst t₁
  have eq := hi (rg₁.eq hN.1 rg); subst g₁
  -- 原回答的 subtype／exceeds 约束给出同一树、同一标签图上的 β<α。
  obtain ⟨τ₀, B₀, U₀, D₀, w, N₀, q₀, η, A, d, R₀, r, β, pair, hτ, sN, language, hA, model, full,
    first, last, labels, bound, height, below⟩ := setup.level_reply_l hZFC hn fh₁ ae aux answer data f₀ sl level root notOrd
      (fn0_function_l (ZF.modelsKP hM) fg₀).1.1
  obtain ⟨l', sl', hl'⟩ := setup.omega.1.2 k hk
  have hl := sl'.eq hM.1 sl ▸ hl'
  obtain ⟨s₁, t₁, g₁, fs₁, ft₁, fg₁, node, rs₁, rt₁, rg₁⟩ := nodes l hl
  have pull {A k l s t : M.Domain} {f : N.Domain} (fs : Fn0_d k A s) (ft : Fn0_d l A t)
      (rs : N.IsRestrictionOf J (e s) f (e k)) (rt : N.IsRestrictionOf J (e t) f (e l)) (kl : M.MemberSubset k l) : M.IsRestrictionOf I s t k := by
    have fs' := image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he (fn0_function_l (ZF.modelsKP hM) fs)
    have ft' := image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he (fn0_function_l (ZF.modelsKP hM) ft)
    exact (ds_restrict_iff_l I (fn0_function_l (ZF.modelsKP hM) fs) (fn0_function_l (ZF.modelsKP hM) ft).1).mpr
      ((image_subset_iff_l e hi he).mp (ds_prefix_mono_l J fs' ft'.1 rs rt ((image_subset_iff_l e hi he).mpr kl)))
  have kl : M.MemberSubset k l := fun x hx => (sl x).mpr (Or.inl hx)
  have cut := pull f₀ ft₁ rt rt₁ kl
  have gcut := pull fg₀ fg₁ rg rg₁ kl
  obtain ⟨z, gz, add⟩ := tg_graph_extend_l hM.1 (KP.exists_pair (ZF.modelsKP hM)) sl
    node₀.2.2.1 node.2.2.1 ((ds_restrict_iff_l I (fn0_function_l (ZF.modelsKP hM) fg₀)
      (fn0_function_l (ZF.modelsKP hM) fg₁).1).mp gcut)
  obtain ⟨x, cx, _⟩ := gz
  have extend y : M.mem y g₁ ↔ M.mem y g₀ ∨ y = x := (add y).trans
    ⟨fun h => h.elim Or.inl (fun cy => Or.inr (kpair_unique_l M hM.1 cy cx)),
      fun h => h.elim Or.inl (fun eq => Or.inr (eq.symm ▸ cx))⟩
  have small {A v : M.Domain} (sub : M.MemberSubset A X) (fv : Fn0_d l A v) : M.mem v X := by
    obtain ⟨_, _, _, hv⟩ := ZF.v_finite_function_l hM setup.omega setup.limit setup.rank hwX hl
      ((fn0_function_l (ZF.modelsKP hM) fv).mono_target_l I sub)
    exact hv
  have hsX := small (ZF.v_transitive_l I hM setup.rank p.A setup.letters) fs₁
  have htX' := small (ZF.v_transitive_l I hM setup.rank p.ω hwX) ft₁
  -- 用同一反例分支的下一标签构造地稠密集；6.6 将其捕获成更低的实际请求。
  obtain ⟨B, hB, capture⟩ := setup.capture_threshold_l hZFC hN e hi he (r := N₀) (β := β) (labels := g₁)
    hd root histories owner control ha hw c surj ff values follows run hn sm mh ev be hl fs₁ rs₁
  obtain ⟨q, hq, hit⟩ := setup.generic_meet_l hZFC hd hn data pair f₀ sl sN ft₁ cut language hA model full first last labels
    bound height node extend hτ hsX htX' histories.1 order generic hB
  obtain ⟨n₁, h₁, a₁, i₁, κ₁, C₁, u₁, hn₁, _, nh₁, ki₁, ia₁, target, _⟩ := capture q (generic.proper q hq).1 hit (origin q hq)
  have hβν : M.mem β p.ν := hαν.elim (fun h => (v_ordinal_l I rank).transitive α₀ h β below) (fun eq => eq ▸ below)
  have nextKey : Tg_level_key_d hM p X Z a₁ l t₁ g₁ β :=
    ⟨(image_member_l e hi he).mp (c.enumeration.bound_l ia₁).2, hl, htX', node.labels_rank_l hM rank treeRank,
      Or.inl hβν, n, κ₁, u₁, N₀, target.2.2.1, target.1, ft₁, sN, target.level_l hM⟩
  exact least (e β) ((image_member_l e hi he).mpr below)
    (table.track_l hM hN e hi he hn₁ nh₁ ki₁ ia₁ nextKey rt₁ rg₁)

end YesMetaZFC.SetTheory.LargeCardinal
