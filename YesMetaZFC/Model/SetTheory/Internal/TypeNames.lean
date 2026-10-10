import YesMetaZFC.Model.SetTheory.Internal.FiniteAssignment
import YesMetaZFC.SetTheory.CumulativeClosure
import YesMetaZFC.SetTheory.InnerModel.Recursion.Graph

/-! # 完整类型的变量名、常量名与赋值

内部自然数 i<n 表示第 i 个自由变量，n 表示指定常量 δ，(x,x) 表示集合常量 x。
有序对不传递，故两种名字互不混淆。任意内部有限名字列实际生成唯一赋值列；
列外取 δ，量词仍由原满足关系更新坐标。这里没有把内部有限列限制为外部有限列。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Tn_name_d (n U a : M.Domain) : Prop :=
  M.mem a n ∨ a = n ∨ ∃ x, M.mem x U ∧ KPair_d M a x x

def tn_name_m {d} (n U a : Term d) : Formula 1 d := .disj (.mem a n)
  (.disj (Formula.extensionalEq a n) (Formula.existsMem U (kpair0_m a.weaken .newest .newest)))
derive_free_closed tn_name_m

theorem tn_name_delta_l {d} (n U a : Term d) : (tn_name_m n U a).IsDelta0 :=
  .disj (.mem _ _) (.disj (.atom _ _ _) (.existsMem _ (kpair0_delta_l ..)))

theorem tn_name_sat_l (hE : Extensional M) {d} (ρ : Env M d) (n U a : Term d) :
    Formula.satisfies ρ (tn_name_m n U a) ↔ Tn_name_d (n.eval ρ) (U.eval ρ) (a.eval ρ) := by
  simp only [tn_name_m, Tn_name_d, Formula.satisfies_disj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_extensionalEq_iff_eq hE, Formula.satisfies_existsMem_iff, kpair0_sat_l hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

def Tn_names_d (n U N : M.Domain) : Prop := ∀ a, M.mem a N ↔ Tn_name_d n U a

theorem tn_names_exists_l (hZF : M.Models ZF) (n U : M.Domain) : ∃ N, Tn_names_d n U N := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨m, hm⟩ := KP.exists_successor (ZF.modelsKP hZF) n
  obtain ⟨P, hP⟩ := ZF.exists_cartesianProduct hZF I U U
  obtain ⟨B, hB⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) m P
  let φ : UnarySchema 2 := { body := tn_name_m (.bound 2) (.bound 1) .newest }
  let ρ : Env M 2 := ⟨Fin.cases U (fun _ => n), fun _ => n⟩
  obtain ⟨N, sep⟩ := ZF.separation_exists_d hZF φ ρ B
  have sat a : φ.denote ρ a ↔ Tn_name_d n U a := tn_name_sat_l hZF.1 ..
  refine ⟨N, fun a => (sep a).trans ((and_congr_right fun _ => sat a).trans ⟨And.right, fun ha => ⟨?_, ha⟩⟩)⟩
  rcases ha with ha | ha | ⟨x, hx, code⟩
  · exact (hB a).mpr (Or.inl ((hm a).mpr (Or.inl ha)))
  · exact (hB a).mpr (Or.inl ((hm a).mpr (Or.inr (ha ▸ fun _ => Iff.rfl))))
  · exact (hB a).mpr (Or.inr ((hP a).mpr ⟨x, hx, x, hx, code⟩))

def Tn_value_d (n s δ a x : M.Domain) : Prop :=
  Rd_entry_d a x s ∨ (a = n ∧ x = δ) ∨ KPair_d M a x x

def tn_value_m {d} (n s δ a x : Term d) : Formula 1 d := .disj (rd_entry0_m a x s)
  (.disj (.conj (Formula.extensionalEq a n) (Formula.extensionalEq x δ)) (kpair0_m a x x))
derive_free_closed tn_value_m

theorem tn_value_sat_l (hE : Extensional M) {d} (ρ : Env M d) (n s δ a x : Term d) :
    Formula.satisfies ρ (tn_value_m n s δ a x) ↔
      Tn_value_d (n.eval ρ) (s.eval ρ) (δ.eval ρ) (a.eval ρ) (x.eval ρ) := by
  simp only [tn_value_m, Tn_value_d, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_extensionalEq_iff_eq hE, rd_entry0_sat_l hE, kpair0_sat_l hE]

theorem tn_value_unique_l (hKP : M.Models KP) {n s δ Z a x y : M.Domain}
    (hn : M.IsOrdinal n) (hs : Fn0_d n Z s) (hx : Tn_value_d n s δ a x) (hy : Tn_value_d n s δ a y) : x = y := by
  have hf := fn0_function_l hKP hs
  have disjoint z (hz : M.mem a n) (hp : KPair_d M a z z) : False :=
    hp.not_transitive_l M (KP.mem_irrefl_d hKP) (hn.mem hz).transitive
  rcases hx with hx | ⟨rfl, rfl⟩ | hx <;> rcases hy with hy | ⟨he, rfl⟩ | hy
  · exact hf.1.2 a x y hx hy
  · exact (KP.mem_irrefl_d hKP n (he ▸ hf.input_mem_of_pairMember hx)).elim
  · exact (disjoint y (hf.input_mem_of_pairMember hx) hy).elim
  · exact (KP.mem_irrefl_d hKP a (hf.input_mem_of_pairMember hy)).elim
  · rfl
  · exact (hy.not_transitive_l M (KP.mem_irrefl_d hKP) hn.transitive).elim
  · exact (disjoint x (hf.input_mem_of_pairMember hy) hx).elim
  · exact (hx.not_transitive_l M (KP.mem_irrefl_d hKP) (he.symm ▸ hn.transitive)).elim
  · exact (kpair_injective_l M hx hy).1

theorem tn_value_exists_l (hKP : M.Models KP) {n s δ U Z a : M.Domain}
    (hs : Fn0_d n Z s) (hδ : M.mem δ Z) (hU : M.MemberSubset U Z) (ha : Tn_name_d n U a) :
    ∃ x, M.mem x Z ∧ Tn_value_d n s δ a x := by
  rcases ha with ha | rfl | ⟨x, hx, hp⟩
  · obtain ⟨x, hx, he⟩ := (fn0_function_l hKP hs).2.2 a ha
    exact ⟨x, hx, Or.inl he⟩
  · exact ⟨δ, hδ, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  · exact ⟨x, hU x hx, Or.inr (Or.inr hp)⟩

def Tn_assign_d (n s δ e r : M.Domain) : Prop :=
  (∀ p, M.mem p r → ∃ i x, KPair_d M p i x) ∧
    ∀ i x, Rd_entry_d i x r ↔ ∃ a, Rd_entry_d i a e ∧ Tn_value_d n s δ a x

def tn_assign_m {d} (n s δ e r : Term d) : Formula 1 d :=
  .conj (Formula.isRelation kpair_convention_l r) (.forallE (.forallE (.iff
    (rd_entry0_m (.bound 1) .newest r.weaken.weaken) (.existsE
      (.conj (rd_entry0_m (.bound 2) .newest e.weaken.weaken.weaken)
        (tn_value_m n.weaken.weaken.weaken s.weaken.weaken.weaken δ.weaken.weaken.weaken .newest (.bound 1)))))))
derive_free_closed tn_assign_m

theorem tn_assign_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (n s δ e r : Term d) :
    Formula.satisfies ρ (tn_assign_m n s δ e r) ↔
      Tn_assign_d (n.eval ρ) (s.eval ρ) (δ.eval ρ) (e.eval ρ) (r.eval ρ) := by
  simp only [tn_assign_m, Tn_assign_d, Formula.satisfies_conj_iff,
    Formula.satisfies_isRelation_iff (kp_pair_l hKP), Formula.satisfies_forall_iff,
    Formula.satisfies_iff_iff, rd_entry0_sat_l hKP.1, Formula.satisfies_exists_iff,
    tn_value_sat_l hKP.1, Definitional.Term.eval_weaken]
  rfl

theorem tn_assign_unique_l (hKP : M.Models KP) {n s δ e r t : M.Domain}
    (hr : Tn_assign_d n s δ e r) (ht : Tn_assign_d n s δ e t) : r = t :=
  Structure.IsSetRelation.eq_of_pairMember_iff (𝕀 := kp_pair_l hKP) hKP.1 hr.1 ht.1
    (fun i x => (hr.2 i x).trans (ht.2 i x).symm)

/-- 每一条合法名字列都生成实际函数；存在性和唯一性均来自原公式。 -/
theorem tn_assign_exists_l (hZF : M.Models ZF) {n s δ U Z N b e : M.Domain}
    (hn : M.IsOrdinal n) (hs : Fn0_d n Z s) (hδ : M.mem δ Z) (hU : M.MemberSubset U Z)
    (names : Tn_names_d n U N) (he : Fn0_d b N e) :
    ∃ r, Tn_assign_d n s δ e r ∧ Fn0_d b Z r := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have hf := fn0_function_l (ZF.modelsKP hZF) he
  let φ : BinarySchema 4 := { body := .existsE (.conj (rd_entry0_m (.bound 2) .newest (.bound 3))
    (tn_value_m (.bound 6) (.bound 5) (.bound 4) .newest (.bound 1))) }
  let ρ : Env M 4 := ⟨Fin.cases e (Fin.cases δ (Fin.cases s (fun _ => n))), fun _ => n⟩
  have sat i x : φ.denote ρ i x ↔ ∃ a, Rd_entry_d i a e ∧ Tn_value_d n s δ a x := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      rd_entry0_sat_l hZF.1, tn_value_sat_l hZF.1]; rfl
  have total i (hi : M.mem i b) : ∃ x, M.mem x Z ∧ φ.denote ρ i x := by
    obtain ⟨a, ha, hia⟩ := hf.2.2 i hi
    obtain ⟨x, hx, value⟩ := tn_value_exists_l (ZF.modelsKP hZF) hs hδ hU ((names a).mp ha)
    exact ⟨x, hx, (sat i x).mpr ⟨a, hia, value⟩⟩
  have unique i x y (hx : φ.denote ρ i x) (hy : φ.denote ρ i y) : x = y := by
    obtain ⟨a, ha, hx⟩ := (sat i x).mp hx
    obtain ⟨a', ha', hy⟩ := (sat i y).mp hy
    have eq := hf.1.2 i a a' ha ha'
    subst a'
    exact tn_value_unique_l (ZF.modelsKP hZF) hn hs hx hy
  obtain ⟨r, hr, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ
    (fun i hi => (total i hi).imp fun _ hx => hx.2) (fun i _ => unique i)
    (fun i x hi hx => by obtain ⟨y, hy, hy'⟩ := total i hi; exact unique i x y hx hy' ▸ hy)
  refine ⟨r, ⟨hr.1.1, fun i x => (spec i x).trans ((and_congr_right fun _ => sat i x).trans
    ⟨And.right, fun hh => ⟨?_, hh⟩⟩)⟩, fn0_of_function_l (ZF.modelsKP hZF) hr⟩
  obtain ⟨a, ha, _⟩ := hh
  exact hf.input_mem_of_pairMember ha

end YesMetaZFC.SetTheory.Internal
