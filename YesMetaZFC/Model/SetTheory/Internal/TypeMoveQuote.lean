import YesMetaZFC.Model.SetTheory.Internal.TypeMove

/-! # 从实际元组自动恢复共同名字列

逐项把指定高度写为空名字，把其余实际对象写为原对角常量名。
函数图在内部由替换生成，长度可以非标准；不预设任何坐标顺序。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Tm_move_d (ν μ s r : M.Domain) : Prop := ∀ i x, Rd_entry_d i x r ↔
  ∃ y, Rd_entry_d i y s ∧ ((y = ν ∧ x = μ) ∨ (y ≠ ν ∧ x = y))

def Tm_quote_d (e ν s E : M.Domain) : Prop := ∀ i a, Rd_entry_d i a E ↔
  ∃ x, Rd_entry_d i x s ∧ ((x = ν ∧ a = e) ∨ (x ≠ ν ∧ KPair_d M a x x))

variable (hZF : M.Models ZF)
local notation "Q" => kp_pair_l (ZF.modelsKP hZF)
include hZF

/-- 原元组是自动名字列的实际赋值；同一列在任意新高度的赋值恰好逐项移动该高度。 -/
theorem tm_quote_l {e ν n P Z A s : M.Domain} (he : ∀ x, ¬ M.mem x e)
    (names : Tn_names_d e P Z) (tuple : Fn0_d n A s)
    (values : ∀ i x, Rd_entry_d i x s → x = ν ∨ M.mem x P) :
    ∃ E, Fn0_d n Z E ∧ Tn_assign_d e e ν E s ∧ Tm_quote_d e ν s E ∧
      ∀ μ r, Tn_assign_d e e μ E r → Tm_move_d ν μ s r := by
  have fn := fn0_function_l (ZF.modelsKP hZF) tuple
  have empty : Fn0_d e A e := ⟨fun p hp => (he p hp).elim,
    fun i hi => (he i hi).elim, fun i hi => (he i hi).elim⟩
  let φ : BinarySchema 3 := { body := set[5] ⟪∃ x,
    ⌜rd_entry0_m⌝ₚ(⌜(.bound 1 : Term 5)⌝ₛ, x, ⌜(.bound 2 : Term 5)⌝ₛ) ∧
    ((x = ⌜(.bound 3 : Term 5)⌝ₛ ∧ ⌜(.newest : Term 5)⌝ₛ = ⌜(.bound 4 : Term 5)⌝ₛ) ∨
      (¬ (x = ⌜(.bound 3 : Term 5)⌝ₛ) ∧ ⌜kpair0_m⌝ₚ(⌜(.newest : Term 5)⌝ₛ, x, x)))⟫ }
  let ρ : Env M 3 := ⟨Fin.cases s (Fin.cases ν (fun _ => e)), fun _ => e⟩
  have read i a : φ.denote ρ i a ↔ ∃ x, Rd_entry_d i x s ∧
      ((x = ν ∧ a = e) ∨ (x ≠ ν ∧ KPair_d M a x x)) := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_disj_iff, Formula.satisfies_neg_iff, rd_entry0_sat_l hZF.1,
      Formula.satisfies_extensionalEq_iff_eq hZF.1, kpair0_sat_l hZF.1]
    rfl
  have total i (hi : M.mem i n) : ∃ a, φ.denote ρ i a := by
    obtain ⟨x, _, hx⟩ := fn.2.2 i hi
    by_cases eq : x = ν
    · exact ⟨e, (read i e).mpr ⟨x, hx, Or.inl ⟨eq, rfl⟩⟩⟩
    · obtain ⟨a, ha⟩ := (Q).total x x
      exact ⟨a, (read i a).mpr ⟨x, hx, Or.inr ⟨eq, ha⟩⟩⟩
  have unique i a b (ha : φ.denote ρ i a) (hb : φ.denote ρ i b) : a = b := by
    obtain ⟨x, hx, ha⟩ := (read i a).mp ha
    obtain ⟨y, hy, hb⟩ := (read i b).mp hb
    have eq := fn.1.2 i x y hx hy
    subst y
    rcases ha with ⟨h, rfl⟩ | ⟨h, ha⟩ <;> rcases hb with ⟨h', rfl⟩ | ⟨h', hb⟩
    · rfl
    · exact (h' h).elim
    · exact (h h').elim
    · exact (Q).unique ha hb
  have bound i a (ha : φ.denote ρ i a) : M.mem a Z := by
    obtain ⟨x, hx, ⟨_, hae⟩ | ⟨hne, hp⟩⟩ := (read i a).mp ha
    · exact hae.symm ▸ (names e).mpr (Or.inr (Or.inl rfl))
    · exact (names a).mpr (Or.inr (Or.inr ⟨x, (values i x hx).resolve_left hne, hp⟩))
  obtain ⟨E, ef, graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF Q φ ρ total
    (fun i _ => unique i) (fun i a _ => bound i a)
  have quote i a : Rd_entry_d i a E ↔ ∃ x, Rd_entry_d i x s ∧
      ((x = ν ∧ a = e) ∨ (x ≠ ν ∧ KPair_d M a x x)) :=
    (graph i a).trans ((and_congr_right fun _ => read i a).trans
      ⟨And.right, fun ⟨x, hx, ha⟩ => ⟨fn.input_mem_of_pairMember hx, x, hx, ha⟩⟩)
  have transfer {y a μ x} (mark : (y = ν ∧ a = e) ∨ (y ≠ ν ∧ KPair_d M a y y)) :
      Tn_value_d e e μ a x ↔ (y = ν ∧ x = μ) ∨ (y ≠ ν ∧ x = y) := by
    rcases mark with ⟨hy, ha⟩ | ⟨hne, code⟩
    · subst y a
      have v : Tn_value_d e e μ e μ := Or.inr (Or.inl ⟨rfl, rfl⟩)
      exact ⟨fun h => Or.inl ⟨rfl, tn_value_unique_l (ZF.modelsKP hZF) (Structure.IsOrdinal.of_no_members he) empty h v⟩,
        fun h => h.elim (fun h => h.2.symm ▸ v) (fun h => (h.1 rfl).elim)⟩
    · have v : Tn_value_d e e μ a y := Or.inr (Or.inr code)
      exact ⟨fun h => Or.inr ⟨hne, tn_value_unique_l (ZF.modelsKP hZF) (Structure.IsOrdinal.of_no_members he) empty h v⟩,
        fun h => h.elim (fun h => (hne h.1).elim) (fun h => h.2.symm ▸ v)⟩
  have select i y (hy : Rd_entry_d i y s) : ∃ a, Rd_entry_d i a E ∧
      ((y = ν ∧ a = e) ∨ (y ≠ ν ∧ KPair_d M a y y)) := by
    obtain ⟨a, _, ha⟩ := ef.2.2 i (fn.input_mem_of_pairMember hy)
    obtain ⟨x, hx, mark⟩ := (quote i a).mp ha
    exact ⟨a, ha, fn.1.2 i x y hx hy ▸ mark⟩
  have assign : Tn_assign_d e e ν E s := by
    refine ⟨fn.1.1, fun i x => ⟨?_, ?_⟩⟩
    · intro hx
      obtain ⟨a, ha, mark⟩ := select i x hx
      by_cases eq : x = ν
      · exact ⟨a, ha, (transfer mark).mpr (Or.inl ⟨eq, eq⟩)⟩
      · exact ⟨a, ha, (transfer mark).mpr (Or.inr ⟨eq, rfl⟩)⟩
    · rintro ⟨a, ha, value⟩
      obtain ⟨y, hy, mark⟩ := (quote i a).mp ha
      rcases (transfer mark).mp value with ⟨hyν, hxν⟩ | ⟨_, hxy⟩
      · exact (hyν.trans hxν.symm) ▸ hy
      · exact hxy.symm ▸ hy
  refine ⟨E, fn0_of_function_l (ZF.modelsKP hZF) ef, assign, quote, fun μ r hr i x => ?_⟩
  refine (hr.2 i x).trans ⟨?_, ?_⟩
  · rintro ⟨a, ha, value⟩
    obtain ⟨y, hy, mark⟩ := (quote i a).mp ha
    exact ⟨y, hy, (transfer mark).mp value⟩
  · rintro ⟨y, hy, move⟩
    obtain ⟨a, ha, mark⟩ := select i y hy
    exact ⟨a, ha, (transfer mark).mpr move⟩

end YesMetaZFC.SetTheory.Internal
