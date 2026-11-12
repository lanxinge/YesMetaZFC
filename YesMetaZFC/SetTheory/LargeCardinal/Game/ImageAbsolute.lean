import YesMetaZFC.SetTheory.LargeCardinal.Types.ContinueAbsolute
import YesMetaZFC.SetTheory.LargeCardinal.Game.RoundNativeScope
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawReply
import YesMetaZFC.SetTheory.LargeCardinal.Types.PoolRead

/-! # 整份回答证书从反射秩层回到所属模型

同一扩展器、超幂、查询池和规则 (7) 一起还原。仅重建源的有限列空间，
其余对象沿用原存在见证，所得完整公式直接交给原生后继工厂。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem tg_image_absolute_l {ω η C : M.Domain}
    (hω : M.IsOmega ω) (rankC : V_d I η C) (fs : Fs_read_d ω C)
    (nc : Nonempty {x // M.mem x C}) {s} (ρ : Env (rt_model_l C nc) s)
    (o κ δ l n U D u τ Q w b z r q h : Term s) (σ : Fin 7 → Term s)
    (hw : (o.eval ρ).val = ω) (regular : M.IsRegularCardinal I (δ.eval ρ).val)
    (valid : Formula.satisfies ρ (tg_image_m o κ δ l n U D u τ Q w b z r q h σ)) :
    ∃ L W, M.mem L C ∧ M.mem W C ∧ ∃ X K R F c d Y T j κ' U' D' u',
      Tg_image_at_d (ZF.modelsKP hZF) ω (κ.eval ρ).val (δ.eval ρ).val (l.eval ρ).val (n.eval ρ).val
        (U.eval ρ).val (D.eval ρ).val (u.eval ρ).val (τ.eval ρ).val (Q.eval ρ).val (w.eval ρ).val (b.eval ρ).val
        (fun i => ((σ i).eval ρ).val) (z.eval ρ).val ⟨(r.eval ρ).val, (q.eval ρ).val, (h.eval ρ).val⟩
        L W X K R F c d Y T j κ' U' D' u' := by
  simp only [tg_image_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at valid
  obtain ⟨X, K', R₀, L, F, c, d, Y, T, j, κ', U', D', u', core, queryRank, pool, reply⟩ := valid
  let ε := ρ.push X |>.push K' |>.push R₀ |>.push L |>.push F |>.push c |>.push d |>.push Y
    |>.push T |>.push j |>.push κ' |>.push U' |>.push D' |>.push u'
  let a (t : Term s) := t.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken
  let t (i : Fin 14) : Term (s + 14) := .bound ⟨i.val, by omega⟩
  obtain ⟨rank, K₀, source, hLδ, hκL, hτL, loc, card, strong, mx, my, ultra, crit, bound, limit, hU, hD, hu⟩ :=
    ti_image_absolute_l hZFC hω rankC fs nc ε (a o) (a κ) (a δ) (a τ) (a U) (a D) (a u)
      (t 13) (t 12) (t 11) (t 10) (t 9) (t 8) (t 7) (t 6) (t 5) (t 4) (t 3) (t 2) (t 1) (t 0)
      (by simpa only [ε, a, Definitional.Term.eval_weaken] using hw)
      (by simpa only [ε, a, Definitional.Term.eval_weaken] using regular) core
  simp only [ε, a, Definitional.Term.eval_weaken] at rank source hLδ hκL hτL loc card strong mx my ultra crit bound limit hU hD hu
  obtain ⟨W, rankW, hQW⟩ := queryRank
  have rankW := (vr_sat_l (ZF.modelsKP hZF) fs.transitive nc _ _ _).mp rankW
  simp only [Definitional.Term.eval_weaken, Definitional.Term.eval_newest] at rankW hQW
  have lo := (loc.ordinals_l (ZF.modelsKP hZF) source.transitive source.code).2
  obtain ⟨V, rv⟩ := ZF.v_exists_l I hZF lo
  have hVC := ZF.v_mem_l I hZF rv rankC (ZF.v_ordinal_height_l hZF rankC lo L.property)
  have eq := vr_agree_l hZF fs.transitive W.property rv (fs.transitive V hVC) rankW
  have fullW : V_d I L.val W.val := by rw [eq]; exact rv
  obtain ⟨A, E, _, _, names, seq, product⟩ :=
    (fs.pool_sat_l (ZF.modelsKP hZF) nc ε (a o) (a l) (t 2) (t 1)
      (by simpa only [ε, a, Definitional.Term.eval_weaken] using hw)).mp pool
  simp only [ε, a, Definitional.Term.eval_weaken] at names seq product
  have reply := tg_reply_source_l (ZF.modelsKP hZF) fs.transitive nc fs.pair
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ reply
  simp only [Definitional.Term.eval_weaken, Definitional.Term.eval_newest, hw] at reply
  have eta (f : Fin 7 → Term (s + 14)) :
      (Fin.cases (f 0) (Fin.cases (f 1) (Fin.cases (f 2) (Fin.cases (f 3)
        (Fin.cases (f 4) (Fin.cases (f 5) (fun _ => f 6))))))) = f := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))))))) i
  simp only [eta (fun i => a (σ i)), a, Definitional.Term.eval_weaken] at reply
  exact ⟨L.val, W.val, L.property, W.property,
    X.val, K₀, R₀.val, F.val, c.val, d.val, Y.val, T.val, j.val, κ'.val, U'.val, D'.val, u'.val,
    rank, source, hLδ, hκL, hτL, fullW, hQW, loc, card, strong, mx, my, ultra,
    crit, bound, limit, hU, hD, hu, ⟨A, E, names, seq, product⟩, reply⟩

end YesMetaZFC.SetTheory.LargeCardinal
