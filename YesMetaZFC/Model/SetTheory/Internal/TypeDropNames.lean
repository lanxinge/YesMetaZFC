import YesMetaZFC.Model.SetTheory.Internal.TypeTruth

/-! # 类型投影的名字重编码

保留前 n 个变量时，它们的编号与集合常量不变；指定常量 δ 的名字
由 n 改为原元数 m。列变换由原公式替换构造，不选择宿主函数。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Td_name_d (n m a b : M.Domain) : Prop := (a = n ∧ b = m) ∨ (a ≠ n ∧ b = a)

def td_name_m {d} (n m a b : Term d) : Formula 1 d := set[d] ⟪
  (⌜a⌝ₛ = ⌜n⌝ₛ ∧ ⌜b⌝ₛ = ⌜m⌝ₛ) ∨ (¬ (⌜a⌝ₛ = ⌜n⌝ₛ) ∧ ⌜b⌝ₛ = ⌜a⌝ₛ)⟫
derive_free_closed td_name_m

theorem td_name_sat_l (hE : Extensional M) {d} (ρ : Env M d) (n m a b : Term d) :
    Formula.satisfies ρ (td_name_m n m a b) ↔ Td_name_d (n.eval ρ) (m.eval ρ) (a.eval ρ) (b.eval ρ) := by
  simp only [td_name_m, Td_name_d, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_neg_iff, Formula.satisfies_extensionalEq_iff_eq hE]

theorem td_name_exists_l (n m a : M.Domain) : ∃ b, Td_name_d n m a b := by
  by_cases h : a = n
  · exact ⟨m, Or.inl ⟨h, rfl⟩⟩
  · exact ⟨a, Or.inr ⟨h, rfl⟩⟩

theorem Td_name_d.unique_l {n m a b c : M.Domain} (h : Td_name_d n m a b) (k : Td_name_d n m a c) : b = c := by
  rcases h with ⟨rfl, rfl⟩ | ⟨ne, rfl⟩ <;> rcases k with ⟨eq, rfl⟩ | ⟨ne', rfl⟩
  · rfl
  · exact (ne' rfl).elim
  · exact (ne eq).elim
  · rfl

theorem Td_name_d.name_l {n m U a b : M.Domain} (h : Td_name_d n m a b)
    (sub : M.MemberSubset n m) (ha : Tn_name_d n U a) : Tn_name_d m U b := by
  rcases h with ⟨rfl, rfl⟩ | ⟨ne, rfl⟩
  · exact Or.inr (Or.inl rfl)
  · exact ha.elim (fun h => Or.inl (sub _ h)) (fun h => h.elim (fun eq => (ne eq).elim) (fun h => Or.inr (Or.inr h)))

variable (I : kpair_convention_l.Interpretation M)

def Td_column_d (n m E F : M.Domain) : Prop := M.IsSetRelation I F ∧ ∀ i b,
  M.PairMember I i b F ↔ ∃ a, M.PairMember I i a E ∧ Td_name_d n m a b

def td_column_m {d} (n m E F : Term d) : Formula 1 d := set[d] ⟪
  ⌜Formula.isRelation kpair_convention_l⌝ₚ(⌜F⌝ₛ) ∧ (∀ i b,
    ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(i, b, ⌜F⌝ₛ) ↔
      (∃ a, ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(i, a, ⌜E⌝ₛ) ∧ ⌜td_name_m⌝ₚ(⌜n⌝ₛ, ⌜m⌝ₛ, a, b)))⟫
derive_free_closed td_column_m

theorem td_column_sat_l (hE : Extensional M) {d} (ρ : Env M d) (n m E F : Term d) :
    Formula.satisfies ρ (td_column_m n m E F) ↔ Td_column_d I (n.eval ρ) (m.eval ρ) (E.eval ρ) (F.eval ρ) := by
  simp only [td_column_m, Td_column_d, Formula.satisfies_conj_iff, Formula.satisfies_isRelation_iff I,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_orderedPairMem_iff I, td_name_sat_l hE, Definitional.Term.eval_weaken]
  rfl

theorem Td_column_d.unique_l (hE : Extensional M) {n m E F G : M.Domain}
    (h : Td_column_d I n m E F) (k : Td_column_d I n m E G) : F = G :=
  Structure.IsSetRelation.eq_of_pairMember_iff hE h.1 k.1 (fun i x => (h.2 i x).trans (k.2 i x).symm)

theorem td_column_exists_l (hZF : M.Models ZF) {n m U N P b E : M.Domain}
    (sub : M.MemberSubset n m) (names : Tn_names_d n U N) (newNames : Tn_names_d m U P)
    (fn : M.IsSetFunctionFromTo I E b N) :
    ∃ F, Td_column_d I n m E F ∧ M.IsSetFunctionFromTo I F b P := by
  let φ : BinarySchema 3 := {
    body := set[5] ⟪∃ a, ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(⌜(.bound 1 : Term 5)⌝ₛ, a, ⌜(.bound 2 : Term 5)⌝ₛ) ∧
      ⌜td_name_m⌝ₚ(⌜(.bound 4 : Term 5)⌝ₛ, ⌜(.bound 3 : Term 5)⌝ₛ, a, ⌜(.newest : Term 5)⌝ₛ)⟫ }
  let ρ : Env M 3 := ⟨Fin.cases E (Fin.cases m (fun _ => n)), fun _ => n⟩
  have read i x : φ.denote ρ i x ↔ ∃ a, M.PairMember I i a E ∧ Td_name_d n m a x := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_orderedPairMem_iff I, td_name_sat_l hZF.1]
    rfl
  obtain ⟨F, ff, graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ
    (fun i hi => by
      obtain ⟨a, _, ha⟩ := fn.2.2 i hi
      obtain ⟨x, hx⟩ := td_name_exists_l n m a
      exact ⟨x, (read i x).mpr ⟨a, ha, hx⟩⟩)
    (fun i _ x y hx hy => by
      obtain ⟨a, ha, hx⟩ := (read i x).mp hx
      obtain ⟨a', ha', hy⟩ := (read i y).mp hy
      exact hx.unique_l (fn.1.2 i a' a ha' ha ▸ hy))
    (fun i x _ hx => by
      obtain ⟨a, ha, hx⟩ := (read i x).mp hx
      exact (newNames x).mpr (hx.name_l sub ((names a).mp (fn.output_mem_of_pairMember ha))))
  exact ⟨F, ⟨ff.1.1, fun i x => (graph i x).trans ((and_congr_right fun _ => read i x).trans
    ⟨And.right, fun h => ⟨h.elim (fun _ h => fn.input_mem_of_pairMember h.1), h⟩⟩)⟩, ff⟩

end YesMetaZFC.SetTheory.Internal
