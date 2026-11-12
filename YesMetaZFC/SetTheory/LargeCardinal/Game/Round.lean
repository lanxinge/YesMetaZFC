import YesMetaZFC.SetTheory.LargeCardinal.Game.Subtype
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawReply
import YesMetaZFC.SetTheory.LargeCardinal.Types.ContinueAbsolute
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.WorkingApply
import YesMetaZFC.SetTheory.LargeCardinal.Game.ReplyReflect

/-! # 后继反射秩段中的回答证书成为实际超幂

层级证书先读成相对秩段，再由完整工作源构造该秩段的真实源实例。
原有界强度式和超幂商、常值图、坍塌逐项读取，最后得到原规则 (7) 的实际回答。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem tg_image_read_l {ω μ K Z R η C : M.Domain}
    (owner : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω μ K Z R) (power : Sc_power_d Z) (context : Tg_context_d I ω Z R η C)
    (nc : Nonempty {x // M.mem x C}) {k} (ρ : Env (rt_model_l C nc) k)
    (o κ δ l n U D u τ Q w b z r q h : Term k) (σ : Fin 7 → Term k) (hw : (o.eval ρ).val = ω)
    (hδ : M.IsLimitOrdinal (δ.eval ρ).val) (regular : Sc_regular_d Z (δ.eval ρ).val)
    (valid : Formula.satisfies ρ (tg_image_m o κ δ l n U D u τ Q w b z r q h σ)) :
    ∃ X K₀ R₀ L F c d Y T j κ' U' D' u',
      M.mem X Z ∧ Vr_d Z (δ.eval ρ).val X ∧ Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω (κ.eval ρ).val K₀ X R₀ ∧
      M.mem L (δ.eval ρ).val ∧ M.mem (κ.eval ρ).val L ∧ M.mem (τ.eval ρ).val L ∧
      (∃ W, M.mem W Z ∧ M.mem W C ∧ Vr_d Z L W ∧ M.mem (Q.eval ρ).val W) ∧
      It_local_d I ω X R₀ (κ.eval ρ).val L F ∧ Sc_inaccessible_d ω X L ∧ Ex_strength_d (kp_pair_l (ZF.modelsKP hZF)) ω (κ.eval ρ).val L X F ∧
      Smem_d I c X R₀ ∧ Smem_d I d Y T ∧ It_ultra_d (kp_pair_l (ZF.modelsKP hZF)) ω (κ.eval ρ).val L F c d j ∧
      Wd_crit_d I X j (κ.eval ρ).val κ' ∧ M.MemberSubset L κ' ∧ M.IsLimitOrdinal κ' ∧
      Rd_entry_d (U.eval ρ).val U' j ∧ Rd_entry_d (D.eval ρ).val D' j ∧ Rd_entry_d (u.eval ρ).val u' j ∧
      Tg_reply_d I ω (l.eval ρ).val (n.eval ρ).val κ' (τ.eval ρ).val U' D' (Q.eval ρ).val u' (w.eval ρ).val
        (b.eval ρ).val (fun i => (σ i).eval ρ |>.val) (z.eval ρ).val ⟨(r.eval ρ).val, (q.eval ρ).val, (h.eval ρ).val⟩ := by
  have fs := (context.read_l hZF owner).1
  simp only [tg_image_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at valid
  obtain ⟨X, K', R₀, L, F, c, d, Y, T, j, κ', U', D', u', core, queryRank, _, reply⟩ := valid
  let ε := ρ.push X |>.push K' |>.push R₀ |>.push L |>.push F |>.push c |>.push d |>.push Y
    |>.push T |>.push j |>.push κ' |>.push U' |>.push D' |>.push u'
  let a (t : Term k) := t.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken
  let t (i : Fin 14) : Term (k + 14) := .bound ⟨i.val, by omega⟩
  obtain ⟨hXZ, full, K₀, source, hLδ, hκL, hτL, loc, card, strong, mx, my, actual, crit, bound, limit, hU, hD, hu⟩ :=
    ti_image_read_l hZFC nc ε (a o) (a κ) (a δ) (a τ) (a U) (a D) (a u)
      (t 13) (t 12) (t 11) (t 10) (t 9) (t 8) (t 7) (t 6) (t 5) (t 4) (t 3) (t 2) (t 1) (t 0)
      owner power context.member (context.rank_l (ZF.modelsKP hZF) owner.transitive owner.code) fs
      (by simpa only [ε, a, Definitional.Term.eval_weaken] using hw)
      (by simpa only [ε, a, Definitional.Term.eval_weaken] using hδ)
      (by simpa only [ε, a, Definitional.Term.eval_weaken] using regular) core
  simp only [ε, a, Definitional.Term.eval_weaken] at full source hLδ hκL hτL loc strong actual crit hU hD hu
  obtain ⟨W, rankW, hQW⟩ := queryRank
  have rankW := (vr_sat_l (ZF.modelsKP hZF) fs.transitive nc _ _ _).mp rankW
  simp only [Definitional.Term.eval_weaken, Definitional.Term.eval_newest] at rankW hQW
  have hWZ := owner.transitive C context.member W.val W.property
  have fullW := Vr_d.of_rank_l owner.transitive context.member (context.rank_l (ZF.modelsKP hZF) owner.transitive owner.code) W.property rankW
  have reply := tg_reply_source_l (ZF.modelsKP hZF) fs.transitive nc fs.pair _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ reply
  simp only [Definitional.Term.eval_weaken, Definitional.Term.eval_newest, hw] at reply
  have eta (f : Fin 7 → Term (k + 14)) :
      (Fin.cases (f 0) (Fin.cases (f 1) (Fin.cases (f 2) (Fin.cases (f 3)
        (Fin.cases (f 4) (Fin.cases (f 5) (fun _ => f 6))))))) = f := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))) i
  simp only [eta (fun i => a (σ i)), a, Definitional.Term.eval_weaken] at reply
  exact ⟨X.val, K₀, R₀.val, L.val, F.val, c.val, d.val, Y.val, T.val, j.val, κ'.val, U'.val, D'.val, u'.val,
    hXZ, full, source, hLδ, hκL, hτL, ⟨W.val, hWZ, W.property, fullW, hQW⟩,
    loc, card, strong, mx, my, actual, crit, bound, limit, hU, hD, hu, reply⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 反射回答沿共同秩段进入跨模型树边

证书中的小超幂与前驱完整源的超幂共有同一个极限秩段中的有界代表。塌缩唯一性
识别两侧的原类型像，故读取的规则 (7) 属于实际加入 nice 树的那条边。
前驱的反射上下文也沿这条边搬运，为后续新参数保留原全称更新句子。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {ω X η C : M.Domain} (nc : Nonempty {x // M.mem x C}) {s}
  (ρ : Env (rt_model_l C nc) s)
  (o κ δ l n U D u τ Q w b z r q h : Term s) (σ : Fin 7 → Term s)
local notation "v" => (fun (t : Term s) => Subtype.val (Definitional.Term.eval ρ t))

theorem Tg_context_d.tree_image_l {c₀ α ξ T J G E H k c d R Y S K K' ζ V η₀ C₀ : M.Domain}
    (context : Tg_context_d I ω X R η C) (prior : Tg_context_d I ω Y S η₀ C₀)
    (owner : Ic_model_d hZF ω (v κ) K X R) (source : Ic_model_d hZF ω (v κ) K' Y S)
    (tree : It_pnice_d hZF ω c₀ α T J G E H) (succ : M.SuccessorOf α ξ)
    (hc : Rd_entry_d ξ c J) (hd : Rd_entry_d k d J) (mx : Smem_d I c X R) (my : Smem_d I d Y S)
    (hw : v o = ω) (hδ : M.IsLimitOrdinal (v δ)) (regular : Sc_regular_d X (v δ))
    (hV : M.mem V X) (rank : Vr_d X ζ V)
    (hV' : M.mem V Y) (rank' : Vr_d Y ζ V) (hζ : M.IsLimitOrdinal ζ)
    (hVC : M.mem V C₀) (hb : M.mem (v b) ω) (hz : M.mem (v z) ω) (hσ : ∀ i, M.mem (v (σ i)) ω)
    (hζδ : M.mem ζ (v δ)) (hκV : M.mem (v κ) V)
    (hU : M.mem (v U) V) (hD : M.mem (v D) V) (hu : M.mem (v u) V)
    (above : ∀ i μ, Rd_entry_d i μ H → M.mem μ (v τ))
    (valid : Formula.satisfies ρ (tg_image_m o κ δ l n U D u τ Q w b z r q h σ)) :
    ∃ β T' J' G' E' H' d' j N R' K₀ L F κ' U' D' u' η' C' W,
      It_pnice_d hZF ω c₀ β T' J' G' E' H' ∧ It_extension_d α ξ k T J G E β T' J' G' E' ∧
      Rd_entry_d α d' J' ∧ It_map_d G' k α j ∧ Smem_d I d' N R' ∧ Ic_model_d hZF ω L K₀ N R' ∧
      It_ultra_d (kp_pair_l (ZF.modelsKP hZF)) ω (v κ) L F d d' j ∧ Wd_crit_d I Y j (v κ) κ' ∧
      (∃ p, Rd_entry_d ξ p E' ∧ It_payload_d p (v κ) L F) ∧
      M.IsLimitOrdinal L ∧ M.mem (v τ) L ∧ M.MemberSubset L κ' ∧
      (∀ i μ, Rd_entry_d i μ H' → M.mem μ κ' ∨ μ = κ') ∧
      Rd_entry_d (v U) U' j ∧ Rd_entry_d (v D) D' j ∧ Rd_entry_d (v u) u' j ∧
      Tg_reply_d I ω (v l) (v n) κ' (v τ) U' D' (v Q) u' (v w) (v b) (fun i => v (σ i))
        (v z) ⟨v r, v q, v h⟩ ∧
      Rd_entry_d η₀ η' j ∧ Rd_entry_d C₀ C' j ∧ Tg_context_d I ω N R' η' C' ∧
      Tg_reply_in_d ω (v l) (v n) κ' (v τ) U' D' (v Q) u' (v w) (v b) (v z)
        (v r) (v q) (v h) (fun i => v (σ i)) C' ∧
      M.mem W X ∧ M.mem W C ∧ Vr_d X L W ∧ Er_level_d N L W ∧ M.mem (v Q) W ∧ M.mem (v w) W ∧
      (∀ μ, M.mem μ L → Ea_agree_d ω μ X N) ∧
      ∃ V₀, M.mem V₀ Y ∧ Vr_d Y (v κ) V₀ ∧ M.mem V₀ N ∧ Vr_d N (v κ) V₀ ∧
        ∀ x, M.mem x V₀ → Rd_entry_d x x j := by
  obtain ⟨_, pₛ, _, _⟩ := owner.read_l hZF
  obtain ⟨A, K₁, R₁, L, F, a, a', B, S₁, f, κ', U', D', u', hA, cut, small,
    _, hκL, hτL, queryRank, loc, inacc, strength, ma, mb, smallUltra, crit, _, limit, iU, iD, iu, reply⟩ :=
    tg_image_read_l hZFC owner.source pₛ context nc ρ o κ δ l n U D u τ Q w b z r q h σ hw hδ regular valid
  have hL := inacc.limit_l (ZF.modelsKP hZF) small.transitive (small.algebra_l (ZF.modelsKP hZF)).pair
  obtain ⟨β, T', J', G', E', H', d', j, N, R', K₀, W, κ₀,
    next, extension, target, edge, mn, ready, ultra, critical, bound, payload, heights, hW, common, level, agreement, same₀, fixed⟩ :=
    it_working_image_l hZFC tree succ hc hd mx my owner source hA cut hδ small ma mb smallUltra loc strength inacc
      hκL hV rank hV' rank' hζ hζδ hκV
      (fun i μ hm => hL.1.transitive (v τ) hτL μ (above i μ hm))
  have same {x y} (hx : M.mem x V) (entry : Rd_entry_d x y f) : Rd_entry_d x y j := same₀ x y hx entry
  obtain ⟨W₀, hW₀, hWC, rankW₀, hQW₀⟩ := queryRank
  have eW := rankW₀.unique_l hZF owner.source.transitive hW₀ hW common
  subst W₀
  have eq := (ultra.elementary_l hZF my.1 mn.1).1.1.1.2 (v κ) κ₀ κ' critical.image (same hκV crit.image)
  subst κ₀
  have hj := ultra.elementary_l hZF my.1 mn.1
  obtain ⟨η', C', iη, iC, context'⟩ := prior.map_l hZF source.source.omega my.1 mn.1 hj
    (hj.omega_l I hZF source.source.omega source.source.transitive ready.source.transitive my mn source.source.omega_mem)
  have inner x (hx : M.mem x V) := (prior.read_l hZF source.source).1.transitive V hVC x hx
  have inU := (hj.member_l I hZF source.source.omega my mn (same hU iU) iC).mp (inner _ hU)
  have inD := (hj.member_l I hZF source.source.omega my mn (same hD iD) iC).mp (inner _ hD)
  have inu := (hj.member_l I hZF source.source.omega my mn (same hu iu) iC).mp (inner _ hu)
  have legal := context'.support_reply_l hZF ready.source level hQW₀ bound limit.1 inU inD inu hb hz hσ reply
  have hwW := common.subset_mem_l owner.source.transitive hW hQW₀
    (owner.source.transitive C context.member _ (w.eval ρ).property) reply.1
  exact ⟨β, T', J', G', E', H', d', j, N, R', K₀, L, F, κ', U', D', u', η', C', W,
    next, extension, target, edge, mn, ready, ultra, critical, payload, hL, hτL, bound, heights,
    same hU iU, same hD iD, same hu iu, reply, iη, iC, context', legal, hW, hWC, common, level, hQW₀, hwW, agreement, fixed⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原回答的正则界与共同极限秩段

武丁公式给出 δ 在所属工作模型中的正则性。任一包含新临界点的共同极限
秩段都容纳原语言和完整类型；首轮的共同秩段由回答支撑自动给出。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}
section
variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {ω X η C : M.Domain} (nc : Nonempty {x // M.mem x C}) (ρ : Env (rt_model_l C nc) 54)
local notation "p" => (fun i => Subtype.val (Env.bound ρ i))

/-- 原武丁公式提供 δ 的正则性，原语言提供临界点的极限性。 -/
theorem Tg_context_d.round_regular_l {μ K R : M.Domain}
    (context : Tg_context_d I ω X R η C) (owner : Ic_model_d hZF ω μ K X R)
    (hw : p 16 = ω) (valid : Formula.satisfies ρ tg_round0_m) :
    M.IsLimitOrdinal (p 18) ∧ Sc_regular_d X (p 18) ∧ M.IsLimitOrdinal (p 21) := by
  have fs := (context.read_l hZF owner.source).1
  let J := rt_pair_l fs.transitive nc hZF.1 fs.pair
  have ext := rt_model_ext_l hZF.1 fs.transitive nc
  obtain ⟨seed, _⟩ := (Formula.satisfies_conj_iff ..).mp valid
  let ρs := Env.reindex ρ (fun i : Fin 38 =>
    i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)
  have seed : Formula.satisfies ρs tg_seed0_m := (Formula.satisfies_rename ..).mp seed
  simp only [tg_seed0_m, tg_seed_m, Formula.satisfies_conj_iff] at seed
  obtain ⟨omega, _, _, woodin, _, _, _, _, _, _, _, _, _, language, _⟩ := seed
  -- 武丁公式的 ω 与当前记录的 ω 由最小归纳集唯一性识别。
  have omega := (Formula.satisfies_isOmega_iff ..).mp omega
  obtain ⟨w, _, omega', below, regular, strong, _⟩ := (woodin_sat_l J ext ρs (.bound 2)).mp woodin
  have eqω := ext.eq_of_same_members w (ρ.bound 16)
    (fun x => ⟨omega'.2 (ρ.bound 16) omega.1 x, omega.2 w omega'.1 x⟩)
  have cardC : Formula.satisfies ρ (sc_inaccessible_m (.bound 16) (.bound 18)) := by
    simp only [sc_inaccessible_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_isRegularCardinal_iff J ext, Formula.satisfies_isStrongLimitCardinal_iff J ext]
    exact ⟨Eq.mp (congrArg (fun x => (rt_model_l C nc).mem x (ρ.bound 18)) eqω) below, regular, strong⟩
  have cardC : Sc_inaccessible_d ω C (p 18) :=
    hw ▸ (sc_inaccessible_sat_l hZF.1 fs.transitive fs.pair nc ρ (.bound 16) (.bound 18)).mp cardC
  have card := cardC.of_rank_l hZF owner.source.transitive (owner.source.algebra_l (ZF.modelsKP hZF)).pair
    context.member (context.rank_l (ZF.modelsKP hZF) owner.source.transitive owner.source.code) (context.limit_l (ZF.modelsKP hZF) owner.source.transitive owner.source.code)
  have hδ := card.limit_l (ZF.modelsKP hZF) owner.source.transitive (owner.source.algebra_l (ZF.modelsKP hZF)).pair
  obtain ⟨_, _, _, iₛ⟩ := owner.read_l hZF
  have regδ := (iₛ _ card).1
  let a : Fin 10 → Term 38 := fun i => [.bound 0, .bound 5, .bound 7, .bound 14, .bound 15,
    .bound 16, .bound 27, .bound 28, .bound 29, .bound 30].get i
  let ε := Definitional.Env.substitute ρs a
  have lang : Formula.satisfies ε ee_language0_m := (Formula.satisfies_bind ρs a ee_language0_m).mp language
  have limit := lang
  simp only [ee_language0_m, Formula.satisfies_conj_iff] at limit
  have hκ := (rt_limit_l fs.transitive nc (ZF.modelsKP hZF) (ρ.bound 21)).mp
    ((Formula.satisfies_isLimitOrdinal_iff ..).mp limit.2.1)
  exact ⟨hδ, regδ, hκ⟩

/-- 共同极限层自动回收原常量域、dcp 查询域和完整类型。 -/
theorem Tg_context_d.round_members_l {μ K R L W : M.Domain}
    (context : Tg_context_d I ω X R η C) (owner : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω μ K X R)
    (hW : M.mem W X) (rank : Vr_d X L W) (hL : M.IsLimitOrdinal L) (hκW : M.mem (p 21) W)
    (hw : p 16 = ω) (valid : Formula.satisfies ρ tg_round0_m) :
    M.mem (p 31) W ∧ M.mem (p 32) W ∧ M.mem (p 34) W := by
  have fs := (context.read_l hZF owner).1
  have seed := (Formula.satisfies_conj_iff ..).mp valid |>.1
  let ρs := Env.reindex ρ (fun i : Fin 38 =>
    i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)
  have seed : Formula.satisfies ρs tg_seed0_m := (Formula.satisfies_rename ..).mp seed
  simp only [tg_seed0_m, tg_seed_m, Formula.satisfies_conj_iff] at seed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, real, language, _⟩ := seed
  let a : Fin 10 → Term 38 := fun i => [.bound 0, .bound 5, .bound 7, .bound 14, .bound 15,
    .bound 16, .bound 27, .bound 28, .bound 29, .bound 30].get i
  let ε := Definitional.Env.substitute ρs a
  have lang : Formula.satisfies ε ee_language0_m := (Formula.satisfies_bind ρs a ee_language0_m).mp language
  have limit := lang
  simp only [ee_language0_m, Formula.satisfies_conj_iff] at limit
  have hκ := (rt_limit_l fs.transitive nc (ZF.modelsKP hZF) (ρ.bound 21)).mp
    ((Formula.satisfies_isLimitOrdinal_iff ..).mp limit.2.1)
  have wt := rank.transitive_l owner.transitive hW
  have hwW := rank.subset_mem_l owner.transitive hW hκW owner.omega_mem
    (owner.omega.subset_limitOrdinal (ZF.modelsKP hZF) hκ)
  obtain ⟨_, _, all, _⟩ := context.language_rank_l hZF nc ε owner hW rank hL hwW hκW hw lang
  -- 完整类型是原完整查询域的子集；只读取这部分真值，不提升整份满足关系。
  let t : Fin 10 → Term 38 := fun i => [.bound 0, .bound 11, .bound 10, .bound 12, .bound 8,
    .bound 13, .bound 2, .bound 15, .bound 17, .bound 18].get i
  let θ := Definitional.Env.substitute ρs t
  have real : Formula.satisfies θ tt_realized0_m := (Formula.satisfies_bind ρs t tt_realized0_m).mp real
  simp only [tt_realized0_m, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff] at real
  obtain ⟨_, hn, _, _, _, pool, truth⟩ := real
  obtain ⟨N, F, _, _, names, seq, product⟩ :=
    (fs.pool_sat_l (ZF.modelsKP hZF) nc θ (.bound 0) (.bound 4) (.bound 7) (.bound 8) hw).mp pool
  have hPW := (owner.pool_rank_l hZF hW rank hL hwW (wt ω hwW (p 24) (hw ▸ hn))
    (all 4) ⟨N, F, names, seq, product⟩).1
  have huX := owner.transitive C context.member (p 34) (ρ.bound 34).property
  have sub : M.MemberSubset (p 34) (p 33) := by
    simp only [tt_truth_m, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
      Formula.satisfies_mem_iff, Formula.satisfies_conj_iff] at truth
    intro x hx
    exact ((truth ⟨x, fs.transitive (p 34) (ρ.bound 34).property x hx⟩).mp hx).1
  exact ⟨all 4, all 5, rank.subset_mem_l owner.transitive hW hPW huX sub⟩

end
variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {ω X η C : M.Domain} (nc : Nonempty {x // M.mem x C}) (ρ : Env (rt_model_l C nc) 54)
local notation "p" => (fun i => Subtype.val (Env.bound ρ i))

/-- 回答支撑在自身所属模型中给出首轮所需的共同层。 -/
theorem Tg_context_d.round_scope_l {μ K R : M.Domain}
    (context : Tg_context_d I ω X R η C) (owner : Ic_model_d hZF ω μ K X R)
    (hw : p 16 = ω) (valid : Formula.satisfies ρ tg_round0_m) :
    ∃ L W, M.mem W X ∧ Vr_d X L W ∧ M.IsLimitOrdinal L ∧ M.mem W C ∧
      M.mem L (p 18) ∧ M.mem (p 21) W := by
  have fs := (context.read_l hZF owner.source).1
  obtain ⟨hδ, regδ, _⟩ := context.round_regular_l hZF nc ρ owner hw valid
  have data := (Formula.satisfies_conj_iff ..).mp valid |>.2
  -- 同一回答的原支撑 L 位于 δ 以下，故其 V_L 同时属于反射层和完整模型。
  simp only [tg_witness0_m, tg_round_m, Formula.satisfies_conj_iff] at data
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, image⟩ := data
  let s : Fin 7 → Term 54 := Fin.cases (.bound 47) (Fin.cases (.bound 48) (Fin.cases (.bound 49)
    (Fin.cases (.bound 50) (Fin.cases (.bound 51) (Fin.cases (.bound 52) (fun _ => .bound 53))))))
  obtain ⟨_, pₛ, _, _⟩ := owner.read_l hZF
  obtain ⟨A, _, _, L, _, _, _, _, _, _, _, _, _, _, hA, cut, _, hLδ, hκL, _,
      ⟨W, hW, hWC, rank, _⟩, _, inacc, _⟩ :=
    tg_image_read_l hZFC owner.source pₛ context nc ρ
      (.bound 16) (.bound 21) (.bound 18) (.bound 23) (.bound 24) (.bound 31) (.bound 32) (.bound 34)
      (.bound 15) (.bound 12) (.bound 11) (.bound 36) (.bound 38) (.bound 2) (.bound 1) (.bound 0)
      s hw hδ regδ image
  have cardL := inacc.of_rank_l hZF owner.source.transitive (owner.source.algebra_l (ZF.modelsKP hZF)).pair hA cut hδ
  have hL := cardL.limit_l (ZF.modelsKP hZF) owner.source.transitive (owner.source.algebra_l (ZF.modelsKP hZF)).pair
  have hκW := rank.ordinal_subset_l hZF owner.source.transitive hW (p 21) hκL
  exact ⟨L, W, hW, rank, hL, hWC, hLδ, hκW⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 内层更新产生实际跨模型迭代轮

存在量词的十六个见证一次解包。原实现和弹性保存在同一个相对秩段内，
给定回答的原扩展器进入 nice 树；所需正则性与共同秩段由记录自动取得。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def tg_round_env_d (ρ : Env M 38) (v : Fin 16 → M.Domain) : Env M 54 :=
  ρ.push (v 15) |>.push (v 14) |>.push (v 13) |>.push (v 12) |>.push (v 11) |>.push (v 10)
    |>.push (v 9) |>.push (v 8) |>.push (v 7) |>.push (v 6) |>.push (v 5) |>.push (v 4)
    |>.push (v 3) |>.push (v 2) |>.push (v 1) |>.push (v 0)

theorem tg_successor_read_l (ρ : Env M 38) (seed : Formula.satisfies ρ tg_seed0_m)
    (valid : Formula.satisfies ρ tg_successor0_m) :
    ∃ v : Fin 16 → M.Domain, Formula.satisfies (tg_round_env_d ρ v) tg_round0_m := by
  simp only [tg_successor0_m, tg_successor_m, Formula.satisfies_exists_iff] at valid
  obtain ⟨τ, C, V, Q, w, η, Z, a, H, f₀, f₁, f₂, f₃, q₀, q₁, q₂, valid⟩ := valid
  let v : Fin 16 → M.Domain := fun i => [q₂, q₁, q₀, f₃, f₂, f₁, f₀, H, a, Z, η, w, Q, V, C, τ].get i
  exact ⟨v, (Formula.satisfies_conj_iff ..).mpr ⟨(Formula.satisfies_rename ..).mpr seed, valid⟩⟩

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {ω X η C : M.Domain} (nc : Nonempty {x // M.mem x C}) (ρ : Env (rt_model_l C nc) 54)
local notation "p" => (fun i => Subtype.val (Env.bound ρ i))
local notation "σ" => (Fin.cases (p 47) (Fin.cases (p 48) (Fin.cases (p 49) (Fin.cases (p 50)
  (Fin.cases (p 51) (Fin.cases (p 52) (fun _ => p 53)))))))

/-- 原回答的扩展器施加到指定树前驱，原类型通过共同极限秩段识别。 -/
theorem Tg_context_d.round_l {c₀ α ξ T J G E H k c d R Y S μ K μ' K' ζ V η₀ C₀ : M.Domain}
    (context : Tg_context_d I ω X R η C) (prior : Tg_context_d I ω Y S η₀ C₀)
    (owner : Ic_model_d hZF ω μ K X R) (source : Ic_model_d hZF ω μ' K' Y S)
    (tree : It_pnice_d hZF ω c₀ α T J G E H) (succ : M.SuccessorOf α ξ)
    (hc : Rd_entry_d ξ c J) (hd : Rd_entry_d k d J) (mx : Smem_d I c X R) (my : Smem_d I d Y S)
    (hV : M.mem V X) (rank : Vr_d X ζ V) (hV' : M.mem V Y) (rank' : Vr_d Y ζ V)
    (hζ : M.IsLimitOrdinal ζ) (hVC : M.mem V C₀) (hζδ : M.mem ζ (p 18)) (hκV : M.mem (p 21) V)
    (hw : p 16 = ω)
    (above : ∀ i ν, Rd_entry_d i ν H → M.mem ν (p 39) ∨ ν = p 39)
    (valid : Formula.satisfies ρ tg_round0_m) :
    ∃ β T' J' G' E' H' d' j N R' K₀ L F κ' U' D' u' η' C' W,
        It_pnice_d hZF ω c₀ β T' J' G' E' H' ∧ It_extension_d α ξ k T J G E β T' J' G' E' ∧
        Rd_entry_d α d' J' ∧ It_map_d G' k α j ∧ Smem_d I d' N R' ∧ Ic_model_d hZF ω L K₀ N R' ∧
        It_ultra_d (kp_pair_l (ZF.modelsKP hZF)) ω (p 21) L F d d' j ∧ Wd_crit_d I Y j (p 21) κ' ∧
        (∃ q, Rd_entry_d ξ q E' ∧ It_payload_d q (p 21) L F) ∧
        M.IsLimitOrdinal L ∧ M.mem (p 15) L ∧ M.MemberSubset L κ' ∧
        (∀ i μ, Rd_entry_d i μ H' → M.mem μ κ' ∨ μ = κ') ∧
        Rd_entry_d (p 31) U' j ∧ Rd_entry_d (p 32) D' j ∧ Rd_entry_d (p 34) u' j ∧
        Tg_reply_d I ω (p 23) (p 24) κ' (p 15) U' D' (p 12) u' (p 11) (p 36) σ
          (p 38) ⟨p 2, p 1, p 0⟩ ∧
        Rd_entry_d η₀ η' j ∧ Rd_entry_d C₀ C' j ∧ Tg_context_d I ω N R' η' C' ∧
        Tg_reply_in_d ω (p 23) (p 24) κ' (p 15) U' D' (p 12) u' (p 11) (p 36) (p 38)
          (p 2) (p 1) (p 0) σ C' ∧
        M.mem W X ∧ M.mem W C ∧ Vr_d X L W ∧ Er_level_d N L W ∧ M.mem (p 12) W ∧ M.mem (p 11) W ∧
        (∀ μ, M.mem μ L → Ea_agree_d ω μ X N) ∧
        ∃ V₀, M.mem V₀ Y ∧ Vr_d Y (p 21) V₀ ∧ M.mem V₀ N ∧ Vr_d N (p 21) V₀ ∧
          ∀ x, M.mem x V₀ → Rd_entry_d x x j := by
  obtain ⟨hδ, regular, hκ⟩ := context.round_regular_l hZF nc ρ owner hw valid
  obtain ⟨hU, hD, hu⟩ := context.round_members_l hZF nc ρ owner.source hV rank hζ hκV hw valid
  have hκX := owner.source.transitive C context.member (p 21) (ρ.bound 21).property
  obtain ⟨K', ready⟩ := owner.rebase_l hZF hκX (owner.source.omega.subset_limitOrdinal (ZF.modelsKP hZF) hκ)
    (sc_ordinal_small_l hZF owner.source.omega owner.source.transitive mx owner.source.theory hκX hκ.1)
  have hκY := source.source.transitive V hV' (p 21) hκV
  obtain ⟨K'', priorReady⟩ := source.rebase_l hZF hκY (source.source.omega.subset_limitOrdinal (ZF.modelsKP hZF) hκ)
    (sc_ordinal_small_l hZF source.source.omega source.source.transitive my source.source.theory hκY hκ.1)
  have data := ((Formula.satisfies_conj_iff ..).mp valid).2
  simp only [tg_witness0_m, tg_round_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at data
  obtain ⟨hχτ, _, hτδ, _, _, _, _, _, _, _, _, _, _, hb, hz, hs₀, hs₁, hs₂, hs₃, hs₄, hs₅, hs₆, image⟩ := data
  let s : Fin 7 → Term 54 := Fin.cases (.bound 47) (Fin.cases (.bound 48) (Fin.cases (.bound 49)
    (Fin.cases (.bound 50) (Fin.cases (.bound 51) (Fin.cases (.bound 52) (fun _ => .bound 53))))))
  have slots : (fun i => (Definitional.Term.eval ρ (s i)).val) = σ := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))) i
  have finite : ∀ i, M.mem (Definitional.Term.eval ρ (s i)).val ω := by
    intro i
    exact Fin.cases (hw ▸ hs₀) (Fin.cases (hw ▸ hs₁) (Fin.cases (hw ▸ hs₂)
      (Fin.cases (hw ▸ hs₃) (Fin.cases (hw ▸ hs₄) (Fin.cases (hw ▸ hs₅)
        (Fin.cases (hw ▸ hs₆) (fun j => Fin.elim0 j))))))) i
  have oτ := hδ.1.mem hτδ
  have result := context.tree_image_l hZFC nc ρ
    (.bound 16) (.bound 21) (.bound 18) (.bound 23) (.bound 24) (.bound 31) (.bound 32) (.bound 34)
    (.bound 15) (.bound 12) (.bound 11) (.bound 36) (.bound 38) (.bound 2) (.bound 1) (.bound 0) s
    prior ready priorReady tree succ hc hd mx my hw hδ regular hV rank hV' rank' hζ hVC
    (hw ▸ hb) (hw ▸ hz) finite hζδ hκV hU hD hu
    (fun i μ hm => (above i μ hm).elim (oτ.transitive (p 39) hχτ μ)
      (fun eq => eq.symm ▸ hχτ)) image
  rw [slots] at result
  exact result

end YesMetaZFC.SetTheory.LargeCardinal
