import YesMetaZFC.SetTheory.InnerModel.ProofCode.SetCover
import YesMetaZFC.SetTheory.InnerModel.Order.Selection

/-! # 构造树的字典序规则

先比较构造符；同为叶时比较序数参数，同为同一运算时比较三个子码。
这里的关系参数随后实例化为较低内部高度的比较历史，不是外部树递归。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project Internal
universe u
variable {M : Structure.{u}}

def Po_step_d (T : M.Domain) (R : M.Domain → M.Domain → Prop) (c d : M.Domain) : Prop :=
  (∃ a, M.mem a T ∧ ∃ b, M.mem b T ∧ Pc_leaf_d T c a ∧ Pc_leaf_d T d b ∧ M.mem a b) ∨
  (∃ t, M.mem t T ∧ ∃ s, M.mem s T ∧ ∃ a, M.mem a T ∧ ∃ b, M.mem b T ∧
    KPair_d M c t a ∧ KPair_d M d s b ∧ M.mem t s) ∨
  ∃ k a, M.mem a T ∧ ∃ b, M.mem b T ∧ ∃ e, M.mem e T ∧
    ∃ x, M.mem x T ∧ ∃ y, M.mem y T ∧ ∃ z, M.mem z T ∧
      Pc_node_d T k c a b e ∧ Pc_node_d T k d x y z ∧ Po_lex_d R a b e x y z

def po_node_s (k : Rd_sym) : Delta0BinarySchema 3 where
  -- 参数为 (高度,历史,集合界)；六个局部变量依次是左右两棵树的三个子码。
  body := Formula.existsMem (.bound 4) <| Formula.existsMem (.bound 5) <| Formula.existsMem (.bound 6) <|
    Formula.existsMem (.bound 7) <| Formula.existsMem (.bound 8) <| Formula.existsMem (.bound 9) <|
      .conj (pc_node_m (.bound 10) k (.bound 7) (.bound 5) (.bound 4) (.bound 3)) <|
        .conj (pc_node_m (.bound 10) k (.bound 6) (.bound 2) (.bound 1) .newest) <|
          .disj (pc_read_m (.bound 9) (.bound 8) (.bound 5) (.bound 2)) <|
            .conj (Formula.extensionalEq (.bound 5) (.bound 2)) <|
              .disj (pc_read_m (.bound 9) (.bound 8) (.bound 4) (.bound 1)) <|
                .conj (Formula.extensionalEq (.bound 4) (.bound 1))
                  (pc_read_m (.bound 9) (.bound 8) (.bound 3) .newest)
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]
  delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
    (.conj (pc_node_delta_l ..) (.conj (pc_node_delta_l ..) (.disj (pc_read_delta_l ..)
      (.conj (.atom _ _ _) (.disj (pc_read_delta_l ..) (.conj (.atom _ _ _) (pc_read_delta_l ..))))))))))))

def po_step_m {n} (T F h c d : Term n) : Formula 1 n :=
  .disj (Formula.existsMem T (Formula.existsMem T.weaken
    (.conj (pc_leaf_m T.weaken.weaken c.weaken.weaken (.bound 1))
      (.conj (pc_leaf_m T.weaken.weaken d.weaken.weaken .newest) (.mem (.bound 1) .newest)))))
  (.disj (Formula.existsMem T (Formula.existsMem T.weaken (Formula.existsMem T.weaken.weaken
    (Formula.existsMem T.weaken.weaken.weaken
      (.conj (kpair0_m c.weaken.weaken.weaken.weaken (.bound 3) (.bound 1))
        (.conj (kpair0_m d.weaken.weaken.weaken.weaken (.bound 2) .newest) (.mem (.bound 3) (.bound 2))))))))
    (rd_any_m rd_menu_l (fun k => binary_pred_m (po_node_s k).toBinarySchema
      (Fin.cases h (Fin.cases F (fun _ => T))) c d)))
derive_free_closed po_step_m

theorem po_step_delta_l {n} (T F h c d : Term n) : (po_step_m T F h c d).IsDelta0 :=
  .disj (.existsMem _ (.existsMem _ (.conj (pc_leaf_delta_l ..) (.conj (pc_leaf_delta_l ..) (.mem _ _)))))
    (.disj (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
      (.conj (kpair0_delta_l ..) (.conj (kpair0_delta_l ..) (.mem _ _)))))))
      (rd_any_delta_l _ _ (fun k => (po_node_s k).delta0.bind_l _)))

theorem po_step_sat_l (hE : Extensional M) {n} (ρ : Env M n) (T F h c d : Term n) :
    Formula.satisfies ρ (po_step_m T F h c d) ↔
      Po_step_d (T.eval ρ) (Pc_read_d (F.eval ρ) (h.eval ρ)) (c.eval ρ) (d.eval ρ) := by
  simp only [po_step_m, Po_step_d, Formula.satisfies_disj_iff, Formula.satisfies_existsMem_iff,
    Formula.satisfies_conj_iff, pc_leaf_sat_l hE, kpair0_sat_l hE, Formula.satisfies_mem_iff,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest, rd_any_sat_l, binary_pred_sat_l]
  apply or_congr Iff.rfl; apply or_congr Iff.rfl
  have hs k : (po_node_s k).toBinarySchema.denote
      ⟨fun i => ((Fin.cases h (Fin.cases F (fun _ => T)) : Fin 3 → Term n) i).eval ρ, ρ.free⟩ (c.eval ρ) (d.eval ρ) ↔
      ∃ a, M.mem a (T.eval ρ) ∧ ∃ b, M.mem b (T.eval ρ) ∧ ∃ e, M.mem e (T.eval ρ) ∧
        ∃ x, M.mem x (T.eval ρ) ∧ ∃ y, M.mem y (T.eval ρ) ∧ ∃ z, M.mem z (T.eval ρ) ∧
          Pc_node_d (T.eval ρ) k (c.eval ρ) a b e ∧ Pc_node_d (T.eval ρ) k (d.eval ρ) x y z ∧
            Po_lex_d (Pc_read_d (F.eval ρ) (h.eval ρ)) a b e x y z := by
    simp only [BinarySchema.denote, po_node_s, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      pc_node_sat_l hE, Formula.satisfies_disj_iff, Formula.satisfies_extensionalEq_iff_eq hE, pc_read_sat_l hE]
    rfl
  exact ⟨fun ⟨k, _, hk⟩ => ⟨k, (hs k).mp hk⟩, fun ⟨k, hk⟩ => ⟨k, rd_menu_mem_l k, (hs k).mpr hk⟩⟩

theorem po_step_mono_l {T U : M.Domain} {R S : M.Domain → M.Domain → Prop}
    (ht : M.MemberSubset T U) (hr : ∀ a b, R a b → S a b) {c d} :
    Po_step_d T R c d → Po_step_d U S c d := by
  have leaf {c a} : Pc_leaf_d T c a → Pc_leaf_d U c a := fun ⟨e, he, h⟩ => ⟨e, ht e he, h⟩
  have node {k c a b e} : Pc_node_d T k c a b e → Pc_node_d U k c a b e :=
    fun ⟨t, htt, v, hv, h⟩ => ⟨t, ht t htt, v, ht v hv, h⟩
  rintro (⟨a, ha, b, hb, hc, hd, h⟩ | ⟨t, htt, s, hs, a, ha, b, hb, hc, hd, h⟩ |
    ⟨k, a, ha, b, hb, e, he, x, hx, y, hy, z, hz, hc, hd, h⟩)
  · exact Or.inl ⟨a, ht a ha, b, ht b hb, leaf hc, leaf hd, h⟩
  · exact Or.inr (Or.inl ⟨t, ht t htt, s, ht s hs, a, ht a ha, b, ht b hb, hc, hd, h⟩)
  · refine Or.inr (Or.inr ⟨k, a, ht a ha, b, ht b hb, e, ht e he, x, ht x hx, y, ht y hy, z, ht z hz, node hc, node hd, ?_⟩)
    exact h.elim (fun h => Or.inl (hr _ _ h)) (fun ⟨h, g⟩ => Or.inr ⟨h,
      g.elim (fun h => Or.inl (hr _ _ h)) (fun ⟨h, g⟩ => Or.inr ⟨h, hr _ _ g⟩)⟩)

end YesMetaZFC.SetTheory.InnerModel
