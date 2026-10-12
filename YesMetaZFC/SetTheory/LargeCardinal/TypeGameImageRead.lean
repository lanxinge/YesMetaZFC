import YesMetaZFC.SetTheory.LargeCardinal.TypeGameContext
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameReplySource
import YesMetaZFC.SetTheory.LargeCardinal.TypeImageRead

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
    (owner : Ep_source_d hZF ω μ K Z R) (power : Sc_power_d Z) (context : Tg_context_d ω Z η C)
    (nc : Nonempty {x // M.mem x C}) {k} (ρ : Env (rt_model_l C nc) k)
    (o κ δ l n U D u τ Q w b z r q h : Term k) (σ : Fin 7 → Term k) (hw : (o.eval ρ).val = ω)
    (hδ : M.IsLimitOrdinal (δ.eval ρ).val) (regular : Sc_regular_d Z (δ.eval ρ).val)
    (valid : Formula.satisfies ρ (tg_image_m o κ δ l n U D u τ Q w b z r q h σ)) :
    ∃ X K₀ R₀ L F c d Y T j κ' U' D' u',
      M.mem X Z ∧ Vr_d Z (δ.eval ρ).val X ∧ Ep_source_d hZF ω (κ.eval ρ).val K₀ X R₀ ∧
      M.mem L (δ.eval ρ).val ∧ M.mem (κ.eval ρ).val L ∧ M.mem (τ.eval ρ).val L ∧
      (∃ W, M.mem W Z ∧ M.mem W C ∧ Vr_d Z L W ∧ M.mem (Q.eval ρ).val W) ∧
      It_local_d ω X (κ.eval ρ).val L F ∧ Sc_inaccessible_d ω X L ∧ Ex_strength_d hZF ω (κ.eval ρ).val L X F ∧
      Smem_d I c X R₀ ∧ Smem_d I d Y T ∧ It_ultra_d hZF ω (κ.eval ρ).val L F c d j ∧
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
      owner power context.member context.rank fs
      (by simpa only [ε, a, Definitional.Term.eval_weaken] using hw)
      (by simpa only [ε, a, Definitional.Term.eval_weaken] using hδ)
      (by simpa only [ε, a, Definitional.Term.eval_weaken] using regular) core
  simp only [ε, a, Definitional.Term.eval_weaken] at full source hLδ hκL hτL loc strong actual crit hU hD hu
  obtain ⟨W, rankW, hQW⟩ := queryRank
  have rankW := (vr_sat_l (ZF.modelsKP hZF) fs.transitive nc _ _ _).mp rankW
  simp only [Definitional.Term.eval_weaken, Definitional.Term.eval_newest] at rankW hQW
  have hWZ := owner.transitive C context.member W.val W.property
  have fullW := Vr_d.of_rank_l hZF owner.transitive context.member context.rank W.property rankW
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
