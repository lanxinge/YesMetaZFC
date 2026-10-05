import YesMetaZFC.Model.SetTheory.Internal.FiniteSyntax

/-! # 有限真值表的 Δ₀ 检验证书

量词只遍历有限赋值空间、对象域和已有真值集。表仍解释原四种指令，
并明确保留全部行的函数图、值域界及 Tarski 方程。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Se_update0_d (b A f i x g : M.Domain) : Prop := Fn0_d b A g ∧
  ∀ j, M.mem j b → ∀ y, M.mem y A →
    (Rd_entry_d j y g ↔ (j = i ∧ y = x) ∨ (j ≠ i ∧ Rd_entry_d j y f))

def se_update0_m {n} (b A f i x g : Term n) : Formula 1 n := .conj (fn0_m b A g)
  (Formula.forallMem b (Formula.forallMem A.weaken (.iff
    (rd_entry0_m (.bound 1) .newest g.weaken.weaken)
    (.disj (.conj (Formula.extensionalEq (.bound 1) i.weaken.weaken) (Formula.extensionalEq .newest x.weaken.weaken))
      (.conj (.neg (Formula.extensionalEq (.bound 1) i.weaken.weaken)) (rd_entry0_m (.bound 1) .newest f.weaken.weaken))))))
derive_free_closed se_update0_m

theorem se_update0_delta_l {n} (b A f i x g : Term n) : (se_update0_m b A f i x g).IsDelta0 :=
  .conj (fn0_delta_l ..) (.forallMem _ (.forallMem _ (.iff (rd_entry0_delta_l ..)
    (.disj (.conj (.atom _ _ _) (.atom _ _ _)) (.conj (.neg (.atom _ _ _)) (rd_entry0_delta_l ..))))))

theorem se_update0_sat_l (hE : Extensional M) {n} (ρ : Env M n) (b A f i x g : Term n) :
    Formula.satisfies ρ (se_update0_m b A f i x g) ↔
      Se_update0_d (b.eval ρ) (A.eval ρ) (f.eval ρ) (i.eval ρ) (x.eval ρ) (g.eval ρ) := by
  simp only [se_update0_m, Se_update0_d, Formula.satisfies_conj_iff, fn0_sat_l hE,
    Formula.satisfies_forallMem_iff, Formula.satisfies_iff_iff, rd_entry0_sat_l hE,
    Formula.satisfies_disj_iff, Formula.satisfies_extensionalEq_iff_eq hE, Formula.satisfies_neg_iff,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]; rfl

theorem se_update0_l (hKP : M.Models KP) {b A f i x g : M.Domain}
    (hf : Fn0_d b A f) (hi : M.mem i b) (hx : M.mem x A) :
    Se_update0_d b A f i x g ↔ Senv_update_d (kp_pair_l hKP) f i x g := by
  refine ⟨fun ⟨hg, h⟩ => ⟨(fn0_function_l hKP hg).1.1, fun j y => ⟨?_, ?_⟩⟩, fun h => ?_⟩
  · intro hjy
    exact (h j (hg.bound_l hjy).1 y (hg.bound_l hjy).2).mp hjy
  · intro hy
    have bound : M.mem j b ∧ M.mem y A := hy.elim (fun ⟨rfl, rfl⟩ => ⟨hi, hx⟩) (fun h => hf.bound_l h.2)
    exact (h j bound.1 y bound.2).mpr hy
  · exact ⟨fn0_of_function_l hKP (h.function_l _ (fn0_function_l hKP hf) hi hx), fun j _ y _ => h.2 j y⟩

def Fv_arg_d (k : Nat) (b A R E C H f i j : M.Domain) : Prop := match k with
  | 0 => ∃ x, M.mem x A ∧ ∃ y, M.mem y A ∧ Rd_entry_d i x f ∧ Rd_entry_d j y f ∧ Rd_entry_d x y R
  | 1 => ∃ x, M.mem x A ∧ Rd_entry_d i x f ∧ Rd_entry_d j x f
  | 2 => ∃ Y, M.mem Y C ∧ ∃ Z, M.mem Z C ∧ Rd_entry_d i Y H ∧ Rd_entry_d j Z H ∧ ¬ (M.mem f Y ∨ M.mem f Z)
  | _ => ∃ Y, M.mem Y C ∧ Rd_entry_d j Y H ∧ ∃ x, M.mem x A ∧ ∃ g, M.mem g E ∧ Se_update0_d b A f i x g ∧ M.mem g Y

def fv_arg_m (k : Nat) {n} (b A R E C H f i j : Term n) : Formula 1 n := match k with
  | 0 => Formula.existsMem A (Formula.existsMem A.weaken (.conj
      (rd_entry0_m i.weaken.weaken (.bound 1) f.weaken.weaken) (.conj
        (rd_entry0_m j.weaken.weaken .newest f.weaken.weaken) (rd_entry0_m (.bound 1) .newest R.weaken.weaken))))
  | 1 => Formula.existsMem A (.conj (rd_entry0_m i.weaken .newest f.weaken) (rd_entry0_m j.weaken .newest f.weaken))
  | 2 => Formula.existsMem C (Formula.existsMem C.weaken (.conj
      (rd_entry0_m i.weaken.weaken (.bound 1) H.weaken.weaken) (.conj
        (rd_entry0_m j.weaken.weaken .newest H.weaken.weaken) (.neg (.disj (.mem f.weaken.weaken (.bound 1)) (.mem f.weaken.weaken .newest))))))
  | _ => Formula.existsMem C (.conj (rd_entry0_m j.weaken .newest H.weaken)
      (Formula.existsMem A.weaken (Formula.existsMem E.weaken.weaken (.conj
        (se_update0_m b.weaken.weaken.weaken A.weaken.weaken.weaken f.weaken.weaken.weaken
          i.weaken.weaken.weaken (.bound 1) .newest) (.mem .newest (.bound 2))))))

@[simp] theorem fv_arg_closed_l (k : Nat) {n} (b A R E C H f i j : Term n)
    (hb : b.freeSupport = []) (hA : A.freeSupport = []) (hR : R.freeSupport = []) (hE : E.freeSupport = [])
    (hC : C.freeSupport = []) (hH : H.freeSupport = []) (hf : f.freeSupport = [])
    (hi : i.freeSupport = []) (hj : j.freeSupport = []) : (fv_arg_m k b A R E C H f i j).FreeClosed := by
  rcases k with _ | (_ | (_ | k)) <;>
    simp -implicitDefEqProofs [fv_arg_m, Definitional.Formula.FreeClosed, hb, hA, hR, hE, hC, hH, hf, hi, hj]

theorem fv_arg_delta_l (k : Nat) {n} (b A R E C H f i j : Term n) : (fv_arg_m k b A R E C H f i j).IsDelta0 := by
  rcases k with _ | (_ | (_ | k))
  · exact .existsMem _ (.existsMem _ (.conj (rd_entry0_delta_l ..) (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..))))
  · exact .existsMem _ (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..))
  · exact .existsMem _ (.existsMem _ (.conj (rd_entry0_delta_l ..) (.conj (rd_entry0_delta_l ..) (.neg (.disj (.mem _ _) (.mem _ _))))))
  · exact .existsMem _ (.conj (rd_entry0_delta_l ..) (.existsMem _ (.existsMem _ (.conj (se_update0_delta_l ..) (.mem _ _)))))

theorem fv_arg_sat_l (hE : Extensional M) (k : Nat) {n} (ρ : Env M n) (b A R E C H f i j : Term n) :
    Formula.satisfies ρ (fv_arg_m k b A R E C H f i j) ↔
      Fv_arg_d k (b.eval ρ) (A.eval ρ) (R.eval ρ) (E.eval ρ) (C.eval ρ) (H.eval ρ) (f.eval ρ) (i.eval ρ) (j.eval ρ) := by
  rcases k with _ | (_ | (_ | k)) <;>
    simp only [fv_arg_m, Fv_arg_d, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      rd_entry0_sat_l hE, Formula.satisfies_neg_iff, Formula.satisfies_disj_iff, Formula.satisfies_mem_iff,
      se_update0_sat_l hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest] <;> rfl

def Fv_node_d (hKP : M.Models KP) (b A R E C H c f : M.Domain) : Prop :=
  ∃ k : Fin 4, ∃ i, M.mem i b ∧ ∃ j, M.mem j b ∧
    Sop_d (kp_pair_l hKP) k.val c i j ∧ Fv_arg_d k.val b A R E C H f i j

private def fv_case_m (k : Nat) {n} (b A R E C H c f : Term n) : Formula 1 n :=
  Formula.existsMem b (Formula.existsMem b.weaken (.conj (sop0_m k c.weaken.weaken (.bound 1) .newest)
    (fv_arg_m k b.weaken.weaken A.weaken.weaken R.weaken.weaken E.weaken.weaken C.weaken.weaken
      H.weaken.weaken f.weaken.weaken (.bound 1) .newest)))
derive_free_closed fv_case_m

def fv_node_m {n} (b A R E C H c f : Term n) : Formula 1 n :=
  .disj (fv_case_m 0 b A R E C H c f) (.disj (fv_case_m 1 b A R E C H c f)
    (.disj (fv_case_m 2 b A R E C H c f) (fv_case_m 3 b A R E C H c f)))
derive_free_closed fv_node_m

theorem fv_node_delta_l {n} (b A R E C H c f : Term n) : (fv_node_m b A R E C H c f).IsDelta0 := by
  have h k : (fv_case_m k b A R E C H c f).IsDelta0 :=
    .existsMem _ (.existsMem _ (.conj (sop0_delta_l ..) (fv_arg_delta_l ..)))
  exact .disj (h 0) (.disj (h 1) (.disj (h 2) (h 3)))

theorem fv_node_sat_l (hKP : M.Models KP) {n} (ρ : Env M n) (b A R E C H c f : Term n) :
    Formula.satisfies ρ (fv_node_m b A R E C H c f) ↔
      Fv_node_d hKP (b.eval ρ) (A.eval ρ) (R.eval ρ) (E.eval ρ) (C.eval ρ) (H.eval ρ) (c.eval ρ) (f.eval ρ) := by
  simp only [fv_node_m, Fv_node_d, Fin.exists_fin_succ, Fin.exists_fin_zero, or_false, fv_case_m,
    Formula.satisfies_disj_iff, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    sop0_sat_l hKP, fv_arg_sat_l hKP.1, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]; rfl

def Fv_eval_d (hKP : M.Models KP) (b A R E n L F C H : M.Domain) : Prop := Fn0_d n C H ∧
  ∀ r, M.mem r n → ∀ c, M.mem c L → ∀ Y, M.mem Y C → Rd_entry_d r c F → Rd_entry_d r Y H →
    M.MemberSubset Y E ∧ ∀ f, M.mem f E → (M.mem f Y ↔ Fv_node_d hKP b A R E C H c f)

def fv_eval_m {d} (b A R E n L F C H : Term d) : Formula 1 d := .conj (fn0_m n C H)
  (Formula.forallMem n (Formula.forallMem L.weaken (Formula.forallMem C.weaken.weaken (.imp
    (rd_entry0_m (.bound 2) (.bound 1) F.weaken.weaken.weaken) (.imp
      (rd_entry0_m (.bound 2) .newest H.weaken.weaken.weaken) (.conj (Formula.subset .newest E.weaken.weaken.weaken)
        (Formula.forallMem E.weaken.weaken.weaken (.iff (.mem .newest (.bound 1))
          (fv_node_m b.weaken.weaken.weaken.weaken A.weaken.weaken.weaken.weaken R.weaken.weaken.weaken.weaken
            E.weaken.weaken.weaken.weaken C.weaken.weaken.weaken.weaken H.weaken.weaken.weaken.weaken (.bound 2) .newest)))))))))
derive_free_closed fv_eval_m

theorem fv_eval_delta_l {d} (b A R E n L F C H : Term d) : (fv_eval_m b A R E n L F C H).IsDelta0 :=
  .conj (fn0_delta_l ..) (.forallMem _ (.forallMem _ (.forallMem _ (.imp (rd_entry0_delta_l ..)
    (.imp (rd_entry0_delta_l ..) (.conj (.atom _ _ _) (.forallMem _ (.iff (.mem _ _) (fv_node_delta_l ..)))))))))

theorem fv_eval_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (b A R E n L F C H : Term d) :
    Formula.satisfies ρ (fv_eval_m b A R E n L F C H) ↔ Fv_eval_d hKP
      (b.eval ρ) (A.eval ρ) (R.eval ρ) (E.eval ρ) (n.eval ρ) (L.eval ρ) (F.eval ρ) (C.eval ρ) (H.eval ρ) := by
  simp only [fv_eval_m, Fv_eval_d, Formula.satisfies_conj_iff, fn0_sat_l hKP.1,
    Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff, rd_entry0_sat_l hKP.1,
    Formula.satisfies_subset_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, fv_node_sat_l hKP,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]; rfl

/-- 用已有全部有限列作界，精确检查某一长度的赋值空间。 -/
def Fv_space_d (b A J E : M.Domain) : Prop := M.MemberSubset E J ∧
  ∀ f, M.mem f J → (M.mem f E ↔ Fn0_d b A f)

def fv_space_m {n} (b A J E : Term n) : Formula 1 n := .conj (Formula.subset E J)
  (Formula.forallMem J (.iff (.mem .newest E.weaken) (fn0_m b.weaken A.weaken .newest)))
derive_free_closed fv_space_m

theorem fv_space_delta_l {n} (b A J E : Term n) : (fv_space_m b A J E).IsDelta0 :=
  .conj (.atom _ _ _) (.forallMem _ (.iff (.mem _ _) (fn0_delta_l ..)))

theorem fv_space_sat_l (hE : Extensional M) {n} (ρ : Env M n) (b A J E : Term n) :
    Formula.satisfies ρ (fv_space_m b A J E) ↔ Fv_space_d (b.eval ρ) (A.eval ρ) (J.eval ρ) (E.eval ρ) := by
  simp only [fv_space_m, Fv_space_d, Formula.satisfies_conj_iff, Formula.satisfies_subset_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
    fn0_sat_l hE, Definitional.Term.eval_weaken]; rfl

def Fv_at_d (C H r f : M.Domain) : Prop := ∃ Y, M.mem Y C ∧ Rd_entry_d r Y H ∧ M.mem f Y

def fv_at_m {n} (C H r f : Term n) : Formula 1 n := Formula.existsMem C
  (.conj (rd_entry0_m r.weaken .newest H.weaken) (.mem f.weaken .newest))
derive_free_closed fv_at_m

theorem fv_at_delta_l {n} (C H r f : Term n) : (fv_at_m C H r f).IsDelta0 :=
  .existsMem _ (.conj (rd_entry0_delta_l ..) (.mem _ _))

theorem fv_at_sat_l (hE : Extensional M) {n} (ρ : Env M n) (C H r f : Term n) :
    Formula.satisfies ρ (fv_at_m C H r f) ↔ Fv_at_d (C.eval ρ) (H.eval ρ) (r.eval ρ) (f.eval ρ) := by
  simp only [fv_at_m, Fv_at_d, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    rd_entry0_sat_l hE, Formula.satisfies_mem_iff, Definitional.Term.eval_weaken]; rfl

end YesMetaZFC.SetTheory.Internal
