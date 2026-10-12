import YesMetaZFC.SetTheory.LargeCardinal.TypeGameCrossImage
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameLanguageTransfer

/-! # 原回答的正则界与共同极限秩段

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
    (context : Tg_context_d ω X η C) (owner : Ic_model_d hZF ω μ K X R)
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
  have card := cardC.of_rank_l hZF owner.source.transitive owner.source.theory.algebra.pair
    context.member context.rank context.limit
  have hδ := card.limit_l (ZF.modelsKP hZF) owner.source.transitive owner.source.theory.algebra.pair
  have regδ := (owner.inaccessible _ card).1
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
    (context : Tg_context_d ω X η C) (owner : Ep_source_d hZF ω μ K X R)
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
  have wt := rank.transitive_l hZF owner.transitive hW
  have hwW := rank.subset_mem_l owner.transitive hW hκW owner.omega_mem
    (owner.omega.subset_limitOrdinal hZF hκ)
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
variable {ω X η C : M.Domain} (nc : Nonempty {x // M.mem x C}) (ρ : Env (rt_model_l C nc) 54)
local notation "p" => (fun i => Subtype.val (Env.bound ρ i))

/-- 回答支撑在自身所属模型中给出首轮所需的共同层。 -/
theorem Tg_context_d.round_scope_l {μ K R : M.Domain}
    (context : Tg_context_d ω X η C) (owner : Ic_model_d hZF ω μ K X R)
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
  obtain ⟨A, _, _, L, _, _, _, _, _, _, _, _, _, _, hA, cut, _, hLδ, hκL, _,
      ⟨W, hW, hWC, rank, _⟩, _, inacc, _⟩ :=
    tg_image_read_l hZFC owner.source owner.power context nc ρ
      (.bound 16) (.bound 21) (.bound 18) (.bound 23) (.bound 24) (.bound 31) (.bound 32) (.bound 34)
      (.bound 15) (.bound 12) (.bound 11) (.bound 36) (.bound 38) (.bound 2) (.bound 1) (.bound 0)
      s hw hδ regδ image
  have cardL := inacc.of_rank_l hZF owner.source.transitive owner.source.theory.algebra.pair hA cut hδ
  have hL := cardL.limit_l (ZF.modelsKP hZF) owner.source.transitive owner.source.theory.algebra.pair
  have hκW := rank.ordinal_subset_l hZF owner.source.transitive hW (p 21) hκL
  exact ⟨L, W, hW, rank, hL, hWC, hLδ, hκW⟩

end YesMetaZFC.SetTheory.LargeCardinal
