import YesMetaZFC.SetTheory.LargeCardinal.TypeGameGenericTransfer
import YesMetaZFC.SetTheory.InaccessibleEnumeration
import YesMetaZFC.Model.Forcing.Applications.Collapse.FiniteSequence
import YesMetaZFC.Model.Forcing.Applications.Collapse.FiniteRecode

/-! # 6.1：地 II 或原 Col(ω,δ) 中的 I

辅助闭博弈先在地模型决定。I 分支通过实际 δ≅Vδ 双射重编码有限条件，
在原 δ 坍缩的名称扩张中调用最小请求策略；不额外假设枚举公平性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}}

/-- 原有限初段坍缩的每个实际泛型扩张都具有该投影补集的 I 获胜策略。 -/
def Tg_collapse_win_d (hZF : M.Models ZF) (ω δ A Y T S : M.Domain) : Prop :=
  let I := kp_pair_l (ZF.modelsKP hZF)
  ∀ C Q, Fseq_space_d I ω δ C →
    (∀ p q, Entry_d M p q Q ↔ M.mem p C ∧ M.mem q C ∧ M.MemberSubset q p) →
    ∀ (O : Cond_order_d M C Q C) U (generic : Generic_d M C Q C U) b, U b →
      let N := extension_l M hZF C Q C U
      ∃ e : M.Domain → N.Domain, Function.Injective e ∧
        (∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y) ∧
        (∀ a t, Check_d M b a t → Qval_d M C Q C U t (e a)) ∧
        Tg_projection_win_d (preserves_zf_l O hZF generic) true (e ω) (e A) (e Y) (e T) (e S)

theorem tg_collapse_no_root_l (hZF : M.Models ZF) {ω δ A Y T S z a : M.Domain}
    (hw : M.IsOmega ω) (hz : ∀ x, ¬ M.mem x z) (ha : M.mem a A)
    (space : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω Y T) (root : ¬ M.mem z S) :
    Tg_collapse_win_d hZF ω δ A Y T S := by
  intro C Q _ _ O U generic b hb
  let N := extension_l M hZF C Q C U
  have hN : N.Models ZF := preserves_zf_l O hZF generic
  obtain ⟨e, hv, he, hi⟩ := check_map_l O hZF generic hb
  have hw' := image_omega_l (hEN := hN.1) e hi he hZF (internal_foundation_l O hZF generic) hw
    (fun D => KP.difference_exists_d (ZF.modelsKP hN) D (e ω))
  exact ⟨e, hi, he, hv, tg_projection_no_root_l hN hw'
    (fun y hy => (he z y).mp hy |>.elim fun x hx => hz x hx.1)
    ((image_member_l e hi he).mpr ha) (image_fseq_l hZF hN e hi he hw hw' space)
    (fun hzS => root ((image_member_l e hi he).mp hzS))⟩

variable (hZFC : M.Models ZFC)
local notation "hM" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hM)

theorem Tg_game_d.collapse_transfer_l {p : Tg_params_d M.Domain}
    {X F L G J B W O Z v σ a Γ P Y T : M.Domain}
    (game : Tg_game_d hZFC p X F L G J B W O Z v) (hd : Woodin_d I p.δ) (root : M.mem p.e p.S)
    (win : Cg_win_d I true p.ω X F J B W σ) (ha : M.mem a p.A)
    (space : Fseq_space_d I p.ω Y T) (prod : M.IsCartesianProduct I P p.ω Γ)
    (letters : M.IsCartesianProduct I Y p.A P) : Tg_collapse_win_d hM p.ω p.δ p.A Y T p.S := by
  have inaccessible := hd
  obtain ⟨_, _, _, _, regular, strong, _⟩ := inaccessible
  obtain ⟨ρ, bij⟩ := ZFC.inaccessible_enumeration_l I hZFC game.setup.omega game.setup.above regular strong game.setup.rank
  obtain ⟨r, inverse, _⟩ := ZF.exists_inverseBijectionWithPairs hM I bij
  obtain ⟨R, order, source, _⟩ := subset_order_l M hM F
  intro C Q collapse ord target U generic b hb
  let N := extension_l M hM C Q C U
  have hN : N.Models ZF := preserves_zf_l target hM generic
  obtain ⟨e, hv, he, hi⟩ := check_map_l target hM generic hb
  have hw := image_omega_l (hEN := hN.1) e hi he hM (internal_foundation_l target hM generic) game.setup.omega
    (fun D => KP.difference_exists_d (ZF.modelsKP hN) D (e p.ω))
  obtain ⟨g, fg, onto, graph⟩ := fseq_generic_surjection_l hM game.setup.omega collapse ord generic target
    ⟨p.ω, game.setup.above⟩ hb e hi he hv
  obtain ⟨V, h, gen, fn, surj, origin⟩ := fseq_recode_generic_l hM hN e hi he game.setup.omega game.histories.1
    collapse inverse source order ord generic fg onto
    (fun q hq i y iy => (graph (e i) (e y)).mpr ⟨q, hq, i, y, iy, rfl, rfl⟩)
  exact ⟨e, hi, he, hv, game.generic_transfer_l hZFC hN e hi he hd root win ha hw
    (fn0_of_function_l (ZF.modelsKP hN) fn) surj space prod letters order gen origin⟩

/-- 从原树、非空实落子字母表及一个 Woodin 基数自动闭合 6.1 的二择一。 -/
theorem tg_lemma61_l {ω δ A X Γ P Y T S a : M.Domain} (hw : M.IsOmega ω) (hd : Woodin_d I δ)
    (rank : V_d I δ X) (hA : M.mem A X) (ha : M.mem a A) (space : Fseq_space_d I ω Y T)
    (tree : Tree_d T S) (prod : M.IsCartesianProduct I P ω Γ) (letters : M.IsCartesianProduct I Y A P) :
    Tg_projection_win_d hM false ω A Y T S ∨ Tg_collapse_win_d hM ω δ A Y T S := by
  classical
  have inaccessible := hd
  obtain ⟨w, _, hw₀, hwd, regular, _⟩ := inaccessible
  have eq : w = ω := hM.1.eq_of_same_members w ω fun x => ⟨hw₀.2 ω hw.1 x, hw.2 w hw₀.1 x⟩
  subst w
  obtain ⟨p, F, L, G, J, B, W, O, Z, v, pw, pd, pa, ps, game⟩ :=
    tg_game_l hZFC (S := S) hw regular.isLimitOrdinal hwd rank hA
  subst ω; subst δ; subst A; subst S
  by_cases root : M.mem p.e p.S
  · obtain ⟨b, σ, _, win⟩ := game.determined_l hZFC
    cases b
    · exact Or.inl (game.transfer_l hZFC hd root win ha space tree)
    · exact Or.inr (game.collapse_transfer_l hZFC hd root win ha space prod letters)
  · exact Or.inr (tg_collapse_no_root_l hM game.setup.omega game.setup.empty ha space root)

end YesMetaZFC.SetTheory.LargeCardinal
