import YesMetaZFC.SetTheory.LargeCardinal.TypeGameCorollary67
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameShiftProjection
import YesMetaZFC.SetTheory.Descriptive.GameShift
import YesMetaZFC.Model.Forcing.Internal.Ground.TreeShift

/-! # 6.10：换手后的原投影博弈

给二坐标树加任意首项后调用 6.7。首手来自旧 I 策略自身或固定字母；
移位策略和投影的对应把地 II／泛型 I 分别变为原投影的地 I／泛型 II。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}}

section Transfer
variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tp_win_d.shift_l {b : Bool} {ω A Γ Y F T S z a : M.Domain}
    (hw : M.IsOmega ω) (hz : ∀ x, ¬ M.mem x z) (ha : M.mem a A)
    (pair : M.IsCartesianProduct I Y A Γ) (space : Fseq_space_d I ω Y F) (subT : M.MemberSubset T F)
    (shift : Tr_shift_d I z F T S) (winning : Tp_win_d hZF b false ω A Y F S) : Tp_win_d hZF (!b) true ω A Y F T := by
  obtain ⟨H, J, B, W, σ, finite, bs, turns, oldPayoff, win⟩ := winning
  have fσ := fn0_function_l (ZF.modelsKP hZF) win.1
  obtain ⟨z', hz', hzω⟩ := hw.1.1
  have eq := hZF.1.eq_of_same_members z' z fun x => iff_of_false (hz' x) (hz x); subst z'
  have hzH := (finite z).mpr ⟨z, hzω, ds_empty_fun_l I hz⟩
  -- 旧 I 的首手必须服从旧策略；旧 II 的对手首手可以固定为任意给定字母。
  have start : ∃ a₀, M.mem a₀ A ∧ (b = true → Rd_entry_d z a₀ σ) := by
    cases b
    · exact ⟨a, ha, fun h => by cases h⟩
    · obtain ⟨a₀, ha₀, za⟩ := fσ.2.2 z hzH
      exact ⟨a₀, ha₀, fun _ => za⟩
  obtain ⟨a₀, ha₀, first⟩ := start
  obtain ⟨τ, fτ, values⟩ := gm_shift_l I hZF hw hz ha₀ finite fσ
  let ρ : Env M 5 := ⟨fun i => [ω, A, Y, F, T].get i, fun _ => ω⟩
  let φ : UnarySchema 5 := { body := tp_projection_m (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) .newest }
  obtain ⟨V, vs⟩ := ZF.separation_exists_d hZF φ ρ B
  have payoff x : M.mem x V ↔ M.mem x B ∧ Tp_projection_d I ω A Y F T x :=
    (vs x).trans (and_congr_right fun _ => tp_projection_sat_l I hZF.1 ..)
  have follows (c : Bool) (r f : M.Domain) : Cg_follows_d I c ω J r f ↔ Gm_follows_d I c ω r f := by
    constructor
    · intro h n hn turn s cut v nv
      apply h n hn ?_ s cut v nv
      cases c
      · exact fun nj => turn ((turns n).mp nj).2
      · exact (turns n).mpr ⟨hn, turn⟩
    · intro h n hn turn s cut v nv
      apply h n hn ?_ s cut v nv
      cases c
      · exact fun even => turn ((turns n).mpr ⟨hn, even⟩)
      · exact ((turns n).mp turn).2
  refine ⟨H, J, B, V, τ, finite, bs, turns, payoff, fn0_of_function_l (ZF.modelsKP hZF) fτ, fun f hf follow => ?_⟩
  have ff := (bs f).mp hf
  -- 对任意新服从对局重建旧服从对局，再在同一模型内使用投影等价。
  obtain ⟨g, fg, cons⟩ := cons_omega_l I hZF hw hz ha₀ ff
  have follow' := gm_shift_follows_l I hZF hw hz ha₀ values first ff fg cons ((follows (!b) τ f).mp follow)
  have hg := (bs g).mpr fg
  have result := win.2 g hg ((follows b σ g).mpr follow')
  have proj := tp_shift_projection_l hZF hw hz ha₀ pair space subT shift ff fg cons
  cases b
  · exact (payoff f).mpr ⟨hf, proj.mp (Classical.byContradiction (fun no => result ((oldPayoff g).mpr ⟨hg, no⟩)))⟩
  · intro yes
    exact ((oldPayoff g).mp result).2 (proj.mpr ((payoff f).mp yes).2)

end Transfer

variable (hZFC : M.Models ZFC)
local notation "hM" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hM)

/-- 6.10：原树投影博弈在地面由 I 获胜，或在每个原坍缩扩张中由 II 获胜。 -/
theorem tg_corollary610_l {ω δ A X Γ Y F T a : M.Domain} (hw : M.IsOmega ω) (hd : Woodin_d I δ)
    (rank : V_d I δ X) (hA : M.mem A X) (ha : M.mem a A) (pair : M.IsCartesianProduct I Y A Γ)
    (space : Fseq_space_d I ω Y F) (tree : Tree_d F T) :
    Tp_win_d hM true true ω A Y F T ∨ Tp_collapse_win_d hM false true ω δ A Y F T := by
  obtain ⟨z, hz⟩ := KP.exists_empty (ZF.modelsKP hM)
  obtain ⟨S, shift⟩ := tr_shift_exists_l I hM z F T
  have tree' := shift.tree_l I hM hw hz space tree
  rcases tg_corollary67_l hZFC hw hd rank hA ha pair space tree' with win | win
  · exact Or.inl (win.shift_l hM hw hz ha pair space tree.1 shift)
  · refine Or.inr (fun C Q collapse order O U generic b hb => ?_)
    let N := extension_l M hM C Q C U
    have hN : N.Models ZF := preserves_zf_l O hM generic
    obtain ⟨e, hi, he, hv, winning⟩ := win C Q collapse order O U generic b hb
    have hw' := image_omega_l (hEN := hN.1) e hi he hM (internal_foundation_l O hM generic) hw
      (fun D => KP.difference_exists_d (ZF.modelsKP hN) D (e ω))
    have hz' y (hy : N.mem y (e z)) : False := (he z y).mp hy |>.elim fun x hx => hz x hx.1
    -- 移位树的规范像仍满足原图方程，目标证明覆盖扩张中的全部新对局。
    exact ⟨e, hi, he, hv, winning.shift_l hN hw' hz' ((image_member_l e hi he).mpr ha)
      (image_product_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he pair)
      (image_fseq_l hM hN e hi he hw hw' space) ((image_subset_iff_l e hi he).mpr tree.1)
      (image_tree_shift_l hM hN e hi he hw hw' hz space tree.1 shift)⟩

end YesMetaZFC.SetTheory.LargeCardinal
