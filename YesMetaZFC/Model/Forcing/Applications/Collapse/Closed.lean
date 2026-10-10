import YesMetaZFC.Model.Forcing.Applications.Collapse.Names
import YesMetaZFC.Model.Forcing.TwoStep.Closed
import YesMetaZFC.Model.Forcing.Iteration.Closed.Successor

/-! # 可数闭首阶段后的参数化塌缩

后继的条件域、序关系、顶名称和闭性力迫均实际构造，再调用二步闭性定理。
最后从两组任意地模型集合参数自动装配两个可数部分函数塌缩。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))

/-- 后继源集、目标集允许任意名称，实际二步偏序自动返回可数闭证书和顶条件。 -/
theorem collapse_two_step_closed_l {B R z b ω X Y} (O : Cond_order_d M B R z)
    (hω : M.IsOmega ω) (hb : M.mem b B) (hz : b ≠ z) (hc : Closed_d I B R z ω)
    (hX : Name_d M B X) (hY : Name_d M B Y) : ∃ w A T t W C S,
      Check_d M b ω w ∧ Coll_names_d I B R z w X Y A T t ∧
      Two_step_d M B R z b A T W C S ∧ Name_pool_d M B A t W ∧
      Cond_order_d M C S C ∧ Closed_d I C S C ω ∧
      ∃ q, KPair_d M q b t ∧ M.mem q C ∧ ∀ r, M.mem r C → Entry_d M r q S := by
  obtain ⟨w, hw, hwN, _⟩ := zf_check_l M hZF hb ω
  obtain ⟨A, T, t, hn⟩ := collapse_names_l O hZFC hwN hX hY
  obtain ⟨hP, ht, hc'⟩ := collapse_names_closed_l O hZFC hω hb hw (below_refl_l O hb hz) hn
  obtain ⟨W, C, S, h, L, hW, htop⟩ := two_step_pointed_l O hZF hn.1.1 hn.1.2.1 hn.1.2.2 hb hz hP ht
  exact ⟨w, A, T, t, W, C, S, hw, hn, h, hW, L, two_step_closed_l O hZFC h hW hn.1.2.1 hP hω hw hc hc', htop⟩

/-- 两组集合参数直接生成可数闭二步塌缩；所有名称与闭性前提由实际构造消去。 -/
theorem collapse_pair_closed_l {ω} (hω : M.IsOmega ω) (X₀ Y₀ X₁ Y₁ : M.Domain) :
    ∃ B R b x y w A T t W C S,
      Coll_spec_d I ω X₀ Y₀ B R ∧ Cond_order_d M B R B ∧ Closed_d I B R B ω ∧
      M.mem b B ∧ Check_d M b X₁ x ∧ Check_d M b Y₁ y ∧ Check_d M b ω w ∧
      Coll_names_d I B R B w x y A T t ∧ Two_step_d M B R B b A T W C S ∧
      Name_pool_d M B A t W ∧ Cond_order_d M C S C ∧ Closed_d I C S C ω ∧
      ∃ q, KPair_d M q b t ∧ M.mem q C ∧ ∀ r, M.mem r C → Entry_d M r q S := by
  obtain ⟨B, R, h⟩ := coll_spec_exists_l hZF ω X₀ Y₀
  obtain ⟨b, hb⟩ := KP.exists_empty (ZF.modelsKP hZF)
  obtain ⟨hP, hbB, _⟩ := coll_spec_top_l I h hb
  have O : Cond_order_d M B R B := ⟨hP.1, hP.2,
    fun p _ hp => (KP.mem_irrefl_d (ZF.modelsKP hZF) B ((h.2.2 p B).mp hp).2.1).elim⟩
  have hc := coll_spec_closed_l hZFC hω h
  obtain ⟨x, hx, hxN, _⟩ := zf_check_l M hZF hbB X₁
  obtain ⟨y, hy, hyN, _⟩ := zf_check_l M hZF hbB Y₁
  obtain ⟨w, A, T, t, W, C, S, hw, hn, hs, hW, L, hcs, htop⟩ :=
    collapse_two_step_closed_l hZFC O hω hbB (fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) B (he ▸ hbB)) hc hxN hyN
  exact ⟨B, R, b, x, y, w, A, T, t, W, C, S, h, O, hc, hbB, hx, hy, hw, hn, hs, hW, L, hcs, htop⟩

/-- 在已有可数闭坐标阶段上实际追加塌缩，保留阶段链接及两种支撑约束。 -/
theorem row_collapse_closed_l {α β B R b ω X Y} (h : Row_stage_d M α B R b)
    (hβ : M.SuccessorOf β α) (hω : M.IsOmega ω) (hc : Closed_d I B R B ω)
    (hX : Name_d M B X) (hY : Name_d M B Y) : ∃ w A T t D V G,
      Check_d M b ω w ∧ Coll_names_d I B R B w X Y A T t ∧
      Row_stage_d M β D V b ∧ Row_next_d M α B R b A T t D V ∧ Reg_embed_d M B R B D V D G ∧
      (∀ p q, Entry_d M p q G ↔ M.mem p B ∧ q = p) ∧ Row_link_d I α B R D V ∧ Closed_d I D V D ω ∧
      ∀ k, (∀ p, M.mem p B → Row_supp_d I k ω p) → ∀ q, M.mem q D → Row_supp_d I k ω q := by
  obtain ⟨w, hw, hwN, _⟩ := zf_check_l M hZF h.base ω
  obtain ⟨A, T, t, hn⟩ := collapse_names_l h.order hZFC hwN hX hY
  have hb : b ≠ B := fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) B (he ▸ h.base)
  obtain ⟨hP, ht, hClosed⟩ := collapse_names_closed_l h.order hZFC hω h.base hw (below_refl_l h.order h.base hb) hn
  obtain ⟨D, V, G, hStage, hNext, hG, hId, hLink, hSupp⟩ := row_successor_l hZF h hβ hn.1.1 hn.1.2.1 hn.1.2.2 hP ht
  exact ⟨w, A, T, t, D, V, G, hw, hn, hStage, hNext, hG, hId, hLink,
    row_next_closed_l hZFC h hNext hn.1.2.1 hP hω hw hc hClosed, fun k => hSupp I k ω hω⟩

end YesMetaZFC.Model.Forcing.Internal
