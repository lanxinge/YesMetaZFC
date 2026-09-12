import YesMetaZFC.Model.Boolean.RootSum

/-! # 布尔名称的混合

把各分量的根成员按混合系数重新加权后并合；整个构造继续使用小节点域。
不交系数下，混合名称在每个系数所控制的部分与相应分量等同。
-/

namespace YesMetaZFC.Model.Boolean.BV_graph
universe u v x
variable {B : Type v} (𝔹 : CB_alg B) {ι : Type u}

def mix (F : ι → BV_graph.{u, v} B) (w : ι → B) : BV_graph.{u, v} B :=
  root_sum 𝔹.toSup_order
    (fun a : Σ i, (F i).Child (F i).root => (F a.1).at_node a.2)
    (fun a => 𝔹.meet (w a.1) ((F a.1).val a.2 (F a.1).root))

theorem mix_mem (F : ι → BV_graph.{u, v} B) (w : ι → B) (G : BV_graph.{x, v} B) :
    bv_mem 𝔹 G (mix 𝔹 F w) = 𝔹.iSup (fun i => 𝔹.meet (w i) (bv_mem 𝔹 G (F i))) := by
  rw [mix, sum_mem]
  simp only [BA_alg.meet_assoc]
  rw [𝔹.iSup_sigma (fun i (a : (F i).Child (F i).root) =>
    𝔹.meet (w i) (𝔹.meet ((F i).val a (F i).root) (bv_eq 𝔹 G ((F i).at_node a))))]
  apply congrArg 𝔹.iSup
  funext i
  exact (𝔹.meet_iSup (w i) (fun a : (F i).Child (F i).root =>
    𝔹.meet ((F i).val a (F i).root) (bv_eq 𝔹 G ((F i).at_node a)))).symm

theorem mix_eq (F : ι → BV_graph.{u, v} B) (w : ι → B)
    (hd : ∀ i j, i ≠ j → 𝔹.meet (w i) (w j) = 𝔹.bot) (i : ι) :
    𝔹.le (w i) (bv_eq 𝔹 (mix 𝔹 F w) (F i)) := by
  classical
  apply le_eq_of_mem 𝔹 (mix 𝔹 F w) (F i) (w i)
  · intro G
    rw [mix_mem, 𝔹.meet_iSup]
    apply (𝔹.iSup_le_iff _ _).mpr
    intro j
    by_cases h : j = i
    · subst j
      exact 𝔹.le_trans (𝔹.meet_le_right _ _) (𝔹.meet_le_right _ _)
    · rw [← 𝔹.meet_assoc, hd i j (Ne.symm h), 𝔹.bot_meet]
      exact 𝔹.bot_le _
  · intro G
    rw [mix_mem]
    exact 𝔹.le_iSup (fun j => 𝔹.meet (w j) (bv_mem 𝔹 G (F j))) i

end YesMetaZFC.Model.Boolean.BV_graph
