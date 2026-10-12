import YesMetaZFC.Model.SetTheory.Internal.TypeTruth

/-! # 定义域查询的实际名字列

列依次读取全部原变量、指定常量 δ 和集合常量 κ。只增加两个坐标，
长度仍是模型内部的自然数。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Tg_guard_code_d (n κ U l z p : M.Domain) : Prop := ∃ b k C N,
  M.SuccessorOf b n ∧ M.SuccessorOf l b ∧ Tn_names_d n U N ∧ Fn0_d l N C ∧
    KPair_d M k κ κ ∧ KPair_d M p z C ∧ (∀ i, M.mem i b → Rd_entry_d i i C) ∧ Rd_entry_d b k C

theorem tg_column_l {ω n κ U N : M.Domain} (hω : M.IsOmega ω) (hn : M.mem n ω)
    (hκ : M.mem κ U) (names : Tn_names_d n U N) : ∃ b l k e,
      M.SuccessorOf b n ∧ M.SuccessorOf l b ∧ M.mem l ω ∧ (I).Codes k κ κ ∧
      M.IsSetFunctionFromTo I e l N ∧
        ∀ i a, Rd_entry_d i a e ↔ (M.mem i b ∧ a = i) ∨ (i = b ∧ a = k) := by
  obtain ⟨b, hb, hbω⟩ := hω.1.2 n hn
  obtain ⟨l, hl, hlω⟩ := hω.1.2 b hbω
  obtain ⟨k, hk⟩ := (I).total κ κ
  have small i (hi : M.mem i b) : M.mem i N := by
    apply (names i).mpr
    rcases (hb i).mp hi with hi | hi
    · exact Or.inl hi
    · exact Or.inr (Or.inl (hZF.1.eq_of_same_members i n hi))
  have large := (names k).mpr (Or.inr (Or.inr ⟨κ, hκ, hk⟩))
  let ρ : Env M 2 := ⟨Fin.cases k (fun _ => b), fun _ => n⟩
  let φ : BinarySchema 2 := { body := (.disj (.conj (.mem (.bound 1) (.bound 3)) (Formula.extensionalEq .newest (.bound 1)))
    (.conj (Formula.extensionalEq (.bound 1) (.bound 3)) (Formula.extensionalEq .newest (.bound 2)))) }
  have read i a : φ.denote ρ i a ↔ (M.mem i b ∧ a = i) ∨ (i = b ∧ a = k) := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_mem_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1]; rfl
  obtain ⟨e, fn, graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := l) (target := N) (by
    intro i hi
    rcases (hl i).mp hi with hi | hi
    · exact ⟨i, (read i i).mpr (Or.inl ⟨hi, rfl⟩)⟩
    · exact ⟨k, (read i k).mpr (Or.inr ⟨hZF.1.eq_of_same_members i b hi, rfl⟩)⟩) (by
      intro i _ a c ha hc
      rcases (read i a).mp ha with ⟨hi, ha⟩ | ⟨hi, ha⟩ <;>
        rcases (read i c).mp hc with ⟨hi', hc⟩ | ⟨hi', hc⟩
      · exact ha.trans hc.symm
      · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) b (hi' ▸ hi)).elim
      · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) b (hi ▸ hi')).elim
      · exact ha.trans hc.symm) (by
        intro i a _ ha
        rcases (read i a).mp ha with ⟨hi, ha⟩ | ⟨_, ha⟩
        · exact ha.symm ▸ small i hi
        · exact ha.symm ▸ large)
  refine ⟨b, l, k, e, hb, hl, hlω, hk, fn, fun i a => (graph i a).trans ?_⟩
  exact ⟨fun h => (read i a).mp h.2, fun h => ⟨h.elim
    (fun h => (hl i).mpr (Or.inl h.1)) (fun h => h.1.symm ▸ hl.predecessor_mem), (read i a).mpr h⟩⟩

/-- 指定名字列的全部赋值恰由原元组、δ、κ 三部分组成。 -/
theorem tg_column_values_l {ω n b l k κ e Y X s δ a f : M.Domain}
    (hω : M.IsOmega ω) (hb : M.SuccessorOf b n) (hl : M.SuccessorOf l b)
    (hlω : M.mem l ω) (hk : (I).Codes k κ κ)
    (column : ∀ i z, Rd_entry_d i z e ↔ (M.mem i b ∧ z = i) ∨ (i = b ∧ z = k))
    (tuple : Fn0_d n Y s) (assign : Tn_assign_d n s δ e a) (fill : Senv_fill_d I ω δ l a f)
    (fn : M.IsSetFunctionFromTo I f ω Y) :
    (∀ i y, M.mem i l → Rd_entry_d i y f → M.mem y X) ↔ Fn0_d n X s ∧ M.mem δ X ∧ M.mem κ X := by
  have nbl i (hi : M.mem i n) : M.mem i l := (hl i).mpr (Or.inl ((hb i).mpr (Or.inl hi)))
  have nlt : M.mem n l := (hl n).mpr (Or.inl hb.predecessor_mem)
  have read i z y (hi : M.mem i l) (he : Rd_entry_d i z e) (value : Tn_value_d n s δ z y) : Rd_entry_d i y f :=
    (fill.2 i y).mpr ⟨hω.transitive hZF l hlω i hi, Or.inl ⟨hi, (assign.2 i y).mpr ⟨z, he, value⟩⟩⟩
  have old i y (he : Rd_entry_d i y s) : Rd_entry_d i y f :=
    read i i y (nbl i (tuple.bound_l he).1)
      ((column i i).mpr (Or.inl ⟨(hb i).mpr (Or.inl (tuple.bound_l he).1), rfl⟩)) (Or.inl he)
  have point := read n n δ nlt ((column n n).mpr (Or.inl ⟨hb.predecessor_mem, rfl⟩)) (Or.inr (Or.inl ⟨rfl, rfl⟩))
  have constant := read b k κ hl.predecessor_mem ((column b k).mpr (Or.inr ⟨rfl, rfl⟩)) (Or.inr (Or.inr hk))
  constructor
  · intro h
    have st := fn0_function_l (ZF.modelsKP hZF) tuple
    exact ⟨fn0_of_function_l (ZF.modelsKP hZF) ⟨st.1, st.2.1, fun i hi =>
      (st.2.2 i hi).imp fun y hy => ⟨h i y (nbl i hi) (old i y hy.2), hy.2⟩⟩,
      h n δ nlt point, h b κ hl.predecessor_mem constant⟩
  · rintro ⟨small, hδ, hκ⟩ i y hi he
    rcases (hl i).mp hi with hi | hi
    · rcases (hb i).mp hi with hi | hi
      · obtain ⟨x, hx, hix⟩ := small.2.1 i hi
        exact fn.1.2 i y x he (old i x hix) ▸ hx
      · have eq := hZF.1.eq_of_same_members i n hi
        subst i
        exact fn.1.2 n y δ he point ▸ hδ
    · have eq := hZF.1.eq_of_same_members i b hi
      subst i
      exact fn.1.2 b y κ he constant ▸ hκ

end YesMetaZFC.SetTheory.Internal
