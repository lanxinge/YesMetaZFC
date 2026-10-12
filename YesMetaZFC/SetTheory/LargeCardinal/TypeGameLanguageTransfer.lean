import YesMetaZFC.SetTheory.LargeCardinal.TypeGameContext
import YesMetaZFC.SetTheory.LargeCardinal.TypeElasticNumericTransfer
import YesMetaZFC.SetTheory.LargeCardinal.TypePoolRead

/-! # 共同秩段中的原弹性语言

相对秩历史识别同一常量域，有限闭性回收同一查询域。自然数程序沿共同根
传输，实际列图在传递层之间读取；目标反射句子重新给出完整语言。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {ω X Y η C η' D : M.Domain} (nc : Nonempty {x // M.mem x C})
  (ρ : Env (rt_model_l C nc) 10)
local notation "p" => (fun i => Subtype.val (Env.bound ρ i))

/-- 原常量域、完整查询域及其名字列都属于包含 κ 的极限秩段。 -/
theorem Tg_context_d.language_rank_l {κ K R L W : M.Domain}
    (context : Tg_context_d ω X η C) (source : Ep_source_d hZF ω κ K X R)
    (hW : M.mem W X) (rank : Vr_d X L W) (hL : M.IsLimitOrdinal L)
    (hwW : M.mem ω W) (hkW : M.mem (p 1) W)
    (hw : p 0 = ω) (language : Formula.satisfies ρ ee_language0_m) :
    M.IsLimitOrdinal (p 1) ∧ M.mem (p 2) ω ∧ (∀ i, M.mem (p i) W) ∧ Vr_d W (p 1) (p 3) ∧
      ∃ A E, M.mem A W ∧ M.mem E W ∧ Tn_names_d (p 2) (p 4) A ∧
        Fseq_space_d I ω A E ∧ M.IsCartesianProduct I (p 5) ω E := by
  have fs := (context.read_l hZF source).1
  have wt := rank.transitive_l hZF source.transitive hW
  simp only [ee_language0_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at language
  obtain ⟨domain, limit, base, constants, hg, hh, hi, he, _, _, numeric⟩ := language
  have pool := ((Formula.satisfies_conj_iff ..).mp ((Formula.satisfies_conj_iff ..).mp domain).2).1
  have hκ := (rt_limit_l fs.transitive nc (ZF.modelsKP hZF) _).mp
    ((Formula.satisfies_isLimitOrdinal_iff ..).mp limit)
  have vr := (vr_sat_l (ZF.modelsKP hZF) fs.transitive nc ρ (.bound 1) (.bound 3)).mp base
  have vrX := context.rank.of_rank_l hZF source.transitive context.member (ρ.bound 3).property vr
  have hBX := source.transitive C context.member (p 3) (ρ.bound 3).property
  obtain ⟨hBW, vrW⟩ := rank.rank_l hZF source.transitive hW hL hkW hBX vrX
  have cons := (rt_model_delta_l fs.transitive nc (tt_constants0_delta_l ..) ρ).mp constants
  simp only [tt_constants0_sat_l hZF.1, @eval_image_env_l (rt_model_l C nc) M Subtype.val] at cons
  obtain ⟨c, Q, model⟩ := smdl_membership_l I hZF ⟨ω, hwW⟩
  have theory := source.rank_theory_l hZF hW rank hL model
  obtain ⟨U, hUW, insert⟩ := theory.algebra.insert_l hBW hkW
  have eqU := hZF.1.eq_of_same_members U (p 4) (fun a => (insert a).trans (cons a).symm)
  have hUW : M.mem (p 4) W := eqU ▸ hUW
  have hn : M.mem (p 2) ω := by
    simp only [ee_numeric_m, Formula.satisfies_bind, ee_numeric0_m, Formula.satisfies_exists_iff,
      Formula.satisfies_conj_iff] at numeric
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, pe, _⟩ := numeric
    simp only [ee_stretch_program_m, Formula.satisfies_bind, ee_stretch_program0_m,
      Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at pe
    exact hw ▸ pe.1
  have hnW := wt ω hwW (p 2) hn
  obtain ⟨A, E, _, _, names, seq, product⟩ :=
    (fs.pool_sat_l (ZF.modelsKP hZF) nc ρ (.bound 0) (.bound 2) (.bound 4) (.bound 5) hw).mp pool
  obtain ⟨hPW, poolW⟩ := source.pool_rank_l hZF hW rank hL hwW hnW hUW ⟨A, E, names, seq, product⟩
  have all : ∀ i, M.mem (p i) W := Fin.cases (hw.symm ▸ hwW)
    (Fin.cases hkW (Fin.cases hnW (Fin.cases hBW (Fin.cases hUW (Fin.cases hPW
      (Fin.cases (wt _ hPW _ hg) (Fin.cases (wt _ hPW _ hh)
        (Fin.cases (wt _ hPW _ hi) (Fin.cases (wt _ hPW _ he) (fun i => Fin.elim0 i))))))))))
  exact ⟨hκ, hn, all, vrW, poolW⟩

theorem Tg_context_d.language_peer_l {r B R x S y T π σ C₀ κ K κ' K' L W : M.Domain}
    (context : Tg_context_d ω X η C) (target : Tg_context_d ω Y η' D)
    (source : Ep_source_d hZF ω κ K X S) (next : Ep_source_d hZF ω κ' K' Y T)
    (bt : M.TransitiveSet B) (mb : Smem_d I r B R) (mx : Smem_d I x X S) (my : Smem_d I y Y T)
    (j : Smap_d I ω r x B X π) (k : Smap_d I ω r y B Y σ) (hwB : M.mem ω B)
    (iC : Rd_entry_d C₀ C π) (iD : Rd_entry_d C₀ D σ)
    (hW : M.mem W X) (rank : Vr_d X L W) (hW' : M.mem W Y) (rank' : Vr_d Y L W)
    (hL : M.IsLimitOrdinal L) (hwW : M.mem ω W) (hkW : M.mem (p 1) W) (hWD : M.mem W D)
    (hw : p 0 = ω) (language : Formula.satisfies ρ ee_language0_m) :
    M.mem (p 2) ω ∧ (∀ i, M.mem (p i) W) ∧ ∃ nd : Nonempty {a // M.mem a D}, ∃ θ : Env (rt_model_l D nd) 10,
      (∀ i, (θ.bound i).val = p i) ∧ Formula.satisfies θ ee_language0_m := by
  have fs := (context.read_l hZF source).1
  have ft := (target.read_l hZF next).1
  obtain ⟨hκ, hn, all, vrW, N, F, hNW, hFW, names', seq', product'⟩ :=
    context.language_rank_l hZF nc ρ source hW rank hL hwW hkW hw language
  have hBW := all 3
  have inside a (ha : M.mem a W) := ft.transitive W hWD a ha
  simp only [ee_language0_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at language
  obtain ⟨_, _, _, constants, _, _, _, he, _, _, numeric⟩ := language
  have cons := (rt_model_delta_l fs.transitive nc (tt_constants0_delta_l ..) ρ).mp constants
  simp only [tt_constants0_sat_l hZF.1, @eval_image_env_l (rt_model_l C nc) M Subtype.val] at cons
  let nd : Nonempty {a // M.mem a D} := ⟨⟨ω, target.omega⟩⟩
  let θ : Env (rt_model_l D nd) 10 := ⟨fun i => ⟨p i, inside _ (all i)⟩, fun _ => ⟨ω, target.omega⟩⟩
  let pick : Fin 8 → Term 10 := Fin.cases (.bound 0) (Fin.cases (.bound 1) (Fin.cases (.bound 2) (Fin.cases (.bound 4)
    (Fin.cases (.bound 6) (Fin.cases (.bound 7) (Fin.cases (.bound 8) (fun _ => .bound 9)))))))
  let ρ₀ := Definitional.Env.substitute ρ pick
  let θ₀ := Definitional.Env.substitute θ pick
  have code : Formula.satisfies ρ₀ ee_numeric0_m := (Formula.satisfies_bind ρ pick ee_numeric0_m).mp numeric
  have same : ∀ i, (ρ₀.bound i).val = (θ₀.bound i).val := by
    intro i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))))))) i
  have moved := ee_numeric_transfer_l hZF source.omega bt source.transitive next.transitive mb mx my
    j k hwB iC iD fs.transitive ft.transitive nc nd ρ₀ θ₀ same hw (inside _ hNW) names' code
  have vrY := rank'.of_rank_l hZF next.transitive hW' hBW vrW
  have hBY := next.transitive W hW' (p 3) hBW
  have vrD := (target.rank.rank_l hZF next.transitive target.member target.limit (inside _ hkW) hBY vrY).2
  refine ⟨hn, all, nd, θ, fun _ => rfl, target.language_l hZF next nd θ ?_⟩
  simp only [ee_rebuild_seed_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff]
  refine ⟨(Formula.satisfies_isOmega_iff ..).mpr (rt_omega_l ft.transitive nd hZF.1 _
      (show M.IsOmega (p 0) from hw.symm ▸ source.omega)),
    (Formula.satisfies_isLimitOrdinal_iff ..).mpr ((rt_limit_l ft.transitive nd (ZF.modelsKP hZF) _).mpr hκ),
    (vr_sat_l (ZF.modelsKP hZF) ft.transitive nd θ (.bound 1) (.bound 3)).mpr vrD, ?_, ?_, he,
    (Formula.satisfies_bind θ pick ee_numeric0_m).mpr moved⟩
  · apply (rt_model_delta_l ft.transitive nd (tt_constants0_delta_l ..) θ).mpr
    exact (tt_constants0_sat_l hZF.1 ..).mpr cons
  · exact (ft.pool_sat_l (ZF.modelsKP hZF) nd θ (.bound 0) (.bound 2) (.bound 4) (.bound 5) hw).mpr
      ⟨N, F, inside _ hNW, inside _ hFW, names', seq', product'⟩

end YesMetaZFC.SetTheory.LargeCardinal
