import YesMetaZFC.Model.Boolean.Equality
import YesMetaZFC.Model.Boolean.ChainFixedPoint

/-! # 模布尔等同的选择系数

不断把尚未覆盖的名称部分加入系数，链极限逐点取上确界。
不动点覆盖原族，且不同指标的系数在名称等同的部分不相交；无需预选名称的良序。
-/

namespace YesMetaZFC.Model.Boolean.BV_graph
universe u
variable {B : Type u} (𝔹 : CB_alg B) {ι : Type u}

/-- 对带权名称族作模等同的不交细化，同时保留每个名称的全部覆盖。 -/
theorem selection (F : ι → BV_graph.{u, u} B) (w : ι → B) :
    ∃ q : ι → B,
      (∀ i, 𝔹.le (q i) (w i)) ∧
      (∀ i j, i ≠ j → 𝔹.le (𝔹.meet (q i) (q j)) (𝔹.neg (bv_eq 𝔹 (F i) (F j)))) ∧
      (∀ i, 𝔹.le (w i) (𝔹.iSup (fun j => 𝔹.meet (q j) (bv_eq 𝔹 (F i) (F j))))) := by
  classical
  let R := (𝔹.toSup_order.pi ι).toCS
  let V (q : ι → B) := (∀ i, 𝔹.le (q i) (w i)) ∧
    ∀ i j, i ≠ j → 𝔹.le (𝔹.meet (q i) (q j)) (𝔹.neg (bv_eq 𝔹 (F i) (F j)))
  let c (q : ι → B) (i : ι) := 𝔹.iSup (fun j => 𝔹.meet (q j) (bv_eq 𝔹 (F i) (F j)))
  have hqc (q : ι → B) (i : ι) : 𝔹.le (q i) (c q i) := by
    simpa only [eq_refl, BA_alg.meet_top] using
      𝔹.le_iSup (fun j => 𝔹.meet (q j) (bv_eq 𝔹 (F i) (F j))) i
  have step (q : ι → B) : ∃ r, R.le q r ∧ (V q → V r) ∧
      (r = q → ∀ i, 𝔹.le (w i) (c q i)) := by
    by_cases h : ∀ i, 𝔹.le (w i) (c q i)
    · exact ⟨q, R.le_refl _, id, fun _ => h⟩
    · have hex : ∃ i, ¬ 𝔹.le (w i) (c q i) := Classical.not_forall.mp h
      obtain ⟨i, hi⟩ := hex
      let d := 𝔹.meet (w i) (𝔹.neg (c q i))
      let r (j : ι) := if j = i then 𝔹.join (q j) d else q j
      have hd (j : ι) : 𝔹.le (𝔹.meet d (q j)) (𝔹.neg (bv_eq 𝔹 (F i) (F j))) := by
        apply (𝔹.le_imp_iff _ _ _).mpr
        rw [𝔹.meet_assoc]
        apply (𝔹.le_imp_iff _ _ _).mp
        exact 𝔹.le_trans (𝔹.meet_le_right _ _) (𝔹.neg_antitone
          (𝔹.le_iSup (fun k => 𝔹.meet (q k) (bv_eq 𝔹 (F i) (F k))) j))
      refine ⟨r, ?_, ?_, ?_⟩
      · intro j; dsimp [r]; split <;> first | exact 𝔹.le_join_left _ _ | exact 𝔹.le_refl _
      · intro hv
        have hn (j : ι) (hij : i ≠ j) :
            𝔹.le (𝔹.meet (𝔹.join (q i) d) (q j)) (𝔹.neg (bv_eq 𝔹 (F i) (F j))) := by
          rw [← 𝔹.le_imp_iff, 𝔹.join_le_iff]
          exact ⟨(𝔹.le_imp_iff _ _ _).mpr (hv.2 i j hij), (𝔹.le_imp_iff _ _ _).mpr (hd j)⟩
        constructor
        · intro j; dsimp [r]; split
          · next hji => subst j; exact (𝔹.join_le_iff _ _ _).mpr ⟨hv.1 i, 𝔹.meet_le_left _ _⟩
          · exact hv.1 j
        · intro j k hjk
          by_cases hj : j = i
          · subst j; simpa only [r, if_pos rfl, if_neg (Ne.symm hjk)] using hn k hjk
          · by_cases hk : k = i
            · subst k
              rw [show r j = q j from if_neg hj, show r i = 𝔹.join (q i) d from if_pos rfl,
                𝔹.meet_comm, eq_symm 𝔹 (F j) (F i)]
              exact hn j (Ne.symm hjk)
            · simpa only [r, if_neg hj, if_neg hk] using hv.2 j k hjk
      · intro he
        apply False.elim
        apply hi
        apply (𝔹.le_iff_meet_neg _ _).mpr
        have hdi : 𝔹.le d (q i) := by
          have hr : 𝔹.le d (r i) := by simp only [r, if_pos rfl]; exact 𝔹.le_join_right _ _
          rwa [he] at hr
        have hz := 𝔹.le_meet (𝔹.le_trans hdi (hqc q i)) (𝔹.meet_le_right (w i) (𝔹.neg (c q i)))
        simpa only [𝔹.meet_neg] using hz
  obtain ⟨g, hg⟩ := Classical.axiomOfChoice step
  have hV (q : ι → B) (hq : FP_stage R g q) : V q := by
    induction hq with
    | bot => exact ⟨fun _ => 𝔹.bot_le _, fun _ _ _ => by
        change 𝔹.le (𝔹.meet 𝔹.bot 𝔹.bot) _; rw [𝔹.bot_meet]; exact 𝔹.bot_le _⟩
    | @step q _ ih => exact (hg q).2.1 ih
    | sup p _ hc ih =>
      constructor
      · intro i; exact (𝔹.iSup_le_iff _ _).mpr (fun q => (ih q.1 q.2).1 i)
      · intro i j hij
        change 𝔹.le (𝔹.meet (𝔹.iSup (fun q : {q // p q} => q.1 i))
          (𝔹.iSup (fun q : {q // p q} => q.1 j))) _
        rw [𝔹.meet_iSup, 𝔹.iSup_le_iff]
        intro q
        rw [𝔹.meet_comm, 𝔹.meet_iSup, 𝔹.iSup_le_iff]
        intro r
        rw [𝔹.meet_comm]
        rcases hc q.1 r.1 q.2 r.2 with h | h
        · exact 𝔹.le_trans (𝔹.meet_mono (𝔹.le_refl _) (h j)) ((ih r.1 r.2).2 i j hij)
        · exact 𝔹.le_trans (𝔹.meet_mono (h i) (𝔹.le_refl _)) ((ih q.1 q.2).2 i j hij)
  obtain ⟨q, hq, he, _⟩ := R.stage_max g (fun q => (hg q).1)
  exact ⟨q, (hV q hq).1, (hV q hq).2, (hg q).2.2 he⟩

end YesMetaZFC.Model.Boolean.BV_graph
