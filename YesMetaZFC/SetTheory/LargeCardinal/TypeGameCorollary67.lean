import YesMetaZFC.SetTheory.LargeCardinal.TypeGameCollapse
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameVacuous
import YesMetaZFC.Model.Forcing.Internal.Ground.TreePullback

/-! # 6.7：二坐标树投影的地面／坍缩二择一

自动构造 S={(s,t,g) : (s,g)∈T} 并应用 6.1。地面与实际泛型扩张分别证明
两个投影相同；原策略和实数落子完全保留，不把地面投影等同于扩张投影。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u v
variable {M : Structure.{u}}

/-- positive 指定 I 的收益为投影还是其补；b 指定实际获胜玩家。 -/
def Tp_win_d (hZF : M.Models ZF) (b positive : Bool) (ω A Y F T : M.Domain) : Prop :=
  let I := kp_pair_l (ZF.modelsKP hZF)
  ∃ H J B W σ, Fseq_space_d I ω A H ∧ M.IsFunctionSpace I B ω A ∧
    (∀ n, M.mem n J ↔ M.mem n ω ∧ Gm_even_d I ω n) ∧
    (∀ x, M.mem x W ↔ M.mem x B ∧ (if positive then Tp_projection_d I ω A Y F T x else ¬ Tp_projection_d I ω A Y F T x)) ∧
    Cg_win_d I b ω A H J B W σ

def Tp_collapse_win_d (hZF : M.Models ZF) (b positive : Bool) (ω δ A Y F T : M.Domain) : Prop :=
  let I := kp_pair_l (ZF.modelsKP hZF)
  ∀ C Q, Fseq_space_d I ω δ C →
    (∀ p q, Entry_d M p q Q ↔ M.mem p C ∧ M.mem q C ∧ M.MemberSubset q p) →
    ∀ (O : Cond_order_d M C Q C) U (generic : Generic_d M C Q C U) p, U p →
      let N := extension_l M hZF C Q C U
      ∃ e : M.Domain → N.Domain, Function.Injective e ∧
        (∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y) ∧
        (∀ a t, Check_d M p a t → Qval_d M C Q C U t (e a)) ∧
        Tp_win_d (preserves_zf_l O hZF generic) b positive (e ω) (e A) (e Y) (e F) (e T)

section Transfer
variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_projection_win_d.vacuous_l {ω A Γ P Y Z F G T S d : M.Domain} {b : Bool}
    (hw : M.IsOmega ω) (prod : M.IsCartesianProduct I P ω Γ) (letters : M.IsCartesianProduct I Y A P)
    (pair : M.IsCartesianProduct I Z A Γ) (space : Fseq_space_d I ω Y F) (target : Fseq_space_d I ω Z G)
    (drop : Tv_drop_d I Y Z d) (pull : Tr_pull_d I d F T S) (win : Tg_projection_win_d hZF b ω A Y F S) :
    Tp_win_d hZF b false ω A Z G T := by
  obtain ⟨H, J, B, W, σ, finite, bs, turns, payoff, win⟩ := win
  exact ⟨H, J, B, W, σ, finite, bs, turns, fun x => (payoff x).trans (and_congr_right fun hx =>
    not_congr (tv_projection_l hZF hw prod letters pair space target drop pull ((bs x).mp hx))), win⟩

end Transfer
section Image
variable {N : Structure.{v}} (hM : M.Models ZF) (hN : N.Models ZF) (e : M.Domain → N.Domain)
  (hi : Function.Injective e) (he : ∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
local notation "I" => kp_pair_l (ZF.modelsKP hM)
local notation "J" => kp_pair_l (ZF.modelsKP hN)
include hi he

theorem Tv_drop_d.image_l {Y Z d : M.Domain} (drop : Tv_drop_d I Y Z d) : Tv_drop_d J (e Y) (e Z) (e d) := by
  have value {p q} (h : Tv_drop_value_d I p q) : Tv_drop_value_d J (e p) (e q) := by
    obtain ⟨a, b, c, v, ap, bc, ac⟩ := h
    exact ⟨e a, e b, e c, e v, image_kpair_l e he ap, image_kpair_l e he bc, image_kpair_l e he ac⟩
  refine ⟨image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he drop.1, fun p q => ?_⟩
  constructor
  · intro pq
    obtain ⟨a, b, ab, rfl, rfl⟩ := (image_entries_l e he drop.1.1.1 p q).mp pq
    exact ⟨(image_member_l e hi he).mpr ((drop.2 a b).mp ab).1, value ((drop.2 a b).mp ab).2⟩
  · rintro ⟨hp, pq⟩
    obtain ⟨a, ha, rfl⟩ := (he Y p).mp hp
    obtain ⟨b, _, ab⟩ := drop.1.2.2 a ha
    have eq := pq.unique_l J (value ((drop.2 a b).mp ab).2); subst q
    exact (image_entries_l e he drop.1.1.1 (e a) (e b)).mpr ⟨a, b, ab, rfl, rfl⟩

end Image

variable (hZFC : M.Models ZFC)
local notation "hM" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hM)

/-- 6.7：原二坐标树的补投影博弈，地面 II 或每个原坍缩扩张中的 I 获胜。 -/
theorem tg_corollary67_l {ω δ A X Γ Y F T a : M.Domain} (hw : M.IsOmega ω) (hd : Woodin_d I δ)
    (rank : V_d I δ X) (hA : M.mem A X) (ha : M.mem a A) (pair : M.IsCartesianProduct I Y A Γ)
    (space : Fseq_space_d I ω Y F) (tree : Tree_d F T) :
    Tp_win_d hM false false ω A Y F T ∨ Tp_collapse_win_d hM true false ω δ A Y F T := by
  obtain ⟨P, prod⟩ := ZF.exists_cartesianProduct hM I ω Γ
  obtain ⟨Z, letters⟩ := ZF.exists_cartesianProduct hM I A P
  obtain ⟨G, finite⟩ := ZF.fseq_space_exists_l I hM hw Z
  obtain ⟨d, drop⟩ := tv_drop_l I hM prod letters pair
  obtain ⟨S, pull⟩ := tr_pull_exists_l I hM d G T
  have tree' := pull.tree_l I hM drop.1 finite space tree
  rcases tg_lemma61_l hZFC hw hd rank hA ha finite tree' prod letters with win | win
  · exact Or.inl (win.vacuous_l hM hw prod letters pair finite space drop pull)
  · refine Or.inr (fun C Q collapse order O U generic b hb => ?_)
    -- 旧逆像树的像仍是扩张中的逆像树；在扩张内对全部新分支应用同一个投影等价。
    let N := extension_l M hM C Q C U
    have hN : N.Models ZF := preserves_zf_l O hM generic
    obtain ⟨e, hi, he, hv, winning⟩ := win C Q collapse order O U generic b hb
    have hw' := image_omega_l (hEN := hN.1) e hi he hM (internal_foundation_l O hM generic) hw
      (fun D => KP.difference_exists_d (ZF.modelsKP hN) D (e ω))
    exact ⟨e, hi, he, hv, winning.vacuous_l hN hw'
      (image_product_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he prod)
      (image_product_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he letters)
      (image_product_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he pair)
      (image_fseq_l hM hN e hi he hw hw' finite) (image_fseq_l hM hN e hi he hw hw' space)
      (drop.image_l hM hN e hi he) (image_tree_pullback_l hM hN e hi he drop.1 finite pull)⟩

end YesMetaZFC.SetTheory.LargeCardinal
