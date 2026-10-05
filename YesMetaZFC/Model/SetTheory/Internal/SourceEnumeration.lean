import YesMetaZFC.Model.SetTheory.Internal.UniformizationSource

/-! # 向源内枚举加入指定参数

只移动自然数坐标：新参数占零，原自然数坐标移到后继，其余坐标不动。
因此保持原字母表，无须背景基数正确性，也不向源要求完整函数空间。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem sc_insert_enumeration_l {ω c Z R κ A f x : M.Domain} (hω : M.IsOmega ω)
    (hZ : M.TransitiveSet Z) (hm : Smem_d I c Z R) (theory : Sc_theory_d I ω Z R)
    (hωZ : M.mem ω Z) (hκZ : M.mem κ Z) (hωκ : M.MemberSubset ω κ)
    (hA : M.mem A Z) (hf : M.mem f Z) (hx : M.mem x Z) (bij : M.IsSetBijectionFromTo I f κ A) :
    ∃ B g, M.mem B Z ∧ M.mem g Z ∧ (∀ y, M.mem y B ↔ M.mem y A ∨ y = x) ∧ M.IsSetBijectionFromTo I g κ B := by
  classical
  obtain ⟨B, hB, insert⟩ := theory.algebra.insert_l hA hx
  by_cases hxA : M.mem x A
  · have eq := hZF.1.eq_of_same_members A B (fun y => ⟨fun h => (insert y).mpr (Or.inl h),
      fun h => ((insert y).mp h).elim id (fun e => e ▸ hxA)⟩)
    exact ⟨B, f, hB, hf, insert, eq ▸ bij⟩
  obtain ⟨z, hz, hzω⟩ := hω.1.1
  let shift i m := (M.mem m ω ∧ M.SuccessorOf i m) ∨ (¬ M.mem m ω ∧ i = m)
  have succω i m (hm : M.mem m ω) (hs : M.SuccessorOf i m) : M.mem i ω := by
    obtain ⟨j, hj, hjω⟩ := hω.1.2 m hm
    exact Structure.SuccessorOf.eq hZF.1 hj hs ▸ hjω
  have input i m n (h : shift i m) (k : shift i n) : m = n := by
    rcases h with ⟨hm, hs⟩ | ⟨hm, rfl⟩ <;> rcases k with ⟨hn, ht⟩ | ⟨hn, he⟩
    · exact Structure.SuccessorOf.predecessor_eq hZF.1 ((hω.isOrdinal hZF).mem hm) hs ht
    · exact (hn (he ▸ succω i m hm hs)).elim
    · exact (hm (succω _ n hn ht)).elim
    · exact he
  have output i j m (h : shift i m) (k : shift j m) : i = j := by
    rcases h with ⟨hm, hs⟩ | ⟨hm, hi⟩ <;> rcases k with ⟨hn, ht⟩ | ⟨hn, hj⟩
    · exact Structure.SuccessorOf.eq hZF.1 hs ht
    · exact (hn hm).elim
    · exact (hm hn).elim
    · exact hi.trans hj.symm
  let φ : BinarySchema 5 := {
    body := .disj (.conj (Formula.extensionalEq (.bound 1) (.bound 5)) (Formula.extensionalEq .newest (.bound 4)))
      (Formula.existsMem (.bound 6) (.conj (rd_entry0_m .newest (.bound 1) (.bound 3))
        (.disj (.conj (.mem .newest (.bound 4)) (KP.succ0_m (.bound 2) .newest))
          (.conj (.neg (.mem .newest (.bound 4))) (Formula.extensionalEq (.bound 2) .newest))))) }
  let ρ : Env M 5 := ⟨Fin.cases f (Fin.cases ω (Fin.cases x (Fin.cases z (fun _ => κ)))), fun _ => z⟩
  have read i y : φ.denote ρ i y ↔ (i = z ∧ y = x) ∨ ∃ m, M.mem m κ ∧ Rd_entry_d m y f ∧ shift i m := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_extensionalEq_iff_eq hZF.1, Formula.satisfies_existsMem_iff, rd_entry0_sat_l hZF.1,
      Formula.satisfies_mem_iff, KP.succ0_sat_l hZF.1, Formula.satisfies_neg_iff]; rfl
  have zero m : ¬ shift z m := fun h => h.elim
    (fun h => hz m h.2.predecessor_mem) (fun h => h.1 (h.2 ▸ hzω))
  have unique i y v (hy : φ.denote ρ i y) (hv : φ.denote ρ i v) : y = v := by
    rcases (read i y).mp hy with ⟨rfl, rfl⟩ | ⟨m, _, hmy, hs⟩ <;>
      rcases (read _ v).mp hv with ⟨he, hv⟩ | ⟨n, _, hnv, ht⟩
    · exact hv.symm
    · exact (zero n ht).elim
    · exact (zero m (he ▸ hs)).elim
    · exact bij.1.1.1.2 m y v hmy (input i m n hs ht ▸ hnv)
  have total i (hi : M.mem i κ) : ∃ y, M.mem y B ∧ φ.denote ρ i y := by
    by_cases hi0 : i = z
    · exact ⟨x, (insert x).mpr (Or.inr rfl), (read i x).mpr (Or.inl ⟨hi0, rfl⟩)⟩
    have prev : ∃ m, M.mem m κ ∧ shift i m := by
      by_cases hiω : M.mem i ω
      · have ne : ∃ a, M.mem a i := Classical.byContradiction (fun no => hi0 (hZF.1.eq_of_same_members i z
          (fun a => iff_of_false (fun ha => no ⟨a, ha⟩) (hz a))))
        obtain ⟨m, hm, hs⟩ := hω.exists_predecessor_of_mem_of_nonempty hZF hiω ne
        exact ⟨m, hωκ m hm, Or.inl ⟨hm, hs⟩⟩
      · exact ⟨i, hi, Or.inr ⟨hiω, rfl⟩⟩
    obtain ⟨m, hm, hs⟩ := prev
    obtain ⟨y, hy, hmy⟩ := bij.1.1.2.2 m hm
    exact ⟨y, (insert y).mpr (Or.inl hy), (read i y).mpr (Or.inr ⟨m, hm, hmy, hs⟩)⟩
  obtain ⟨g, hg, fn, select⟩ := sc_uniform_source_l hZF hω hZ hm theory φ
    (.disj (.conj (.atom ..) (.atom ..)) (.existsMem _ (.conj (rd_entry0_delta_l ..)
      (.disj (.conj (.mem _ _) (KP.succ0_delta_l ..)) (.conj (.neg (.mem _ _)) (.atom ..)))))) ρ
    (Fin.cases hf (Fin.cases hωZ (Fin.cases hx (Fin.cases (hZ ω hωZ z hzω) (fun _ => hκZ))))) hκZ hB total
  refine ⟨B, g, hB, hg, insert, ⟨fn0_function_l (ZF.modelsKP hZF) fn, ?_⟩, fun y hy => ?_⟩
  · intro i j y hi hj
    rcases (read i y).mp (select i y hi) with ⟨hi0, rfl⟩ | ⟨m, _, hmy, hs⟩ <;>
      rcases (read j _).mp (select j _ hj) with ⟨hj0, he⟩ | ⟨n, _, hny, ht⟩
    · exact hi0.trans hj0.symm
    · exact (hxA (bij.1.1.output_mem_of_pairMember hny)).elim
    · exact (hxA (he ▸ bij.1.1.output_mem_of_pairMember hmy)).elim
    · exact output i j m hs (bij.1.2 m n y hmy hny ▸ ht)
  · have pre : ∃ i, M.mem i κ ∧ φ.denote ρ i y := by
      rcases (insert y).mp hy with hy | rfl
      · obtain ⟨m, hm, hmy⟩ := bij.2 y hy
        by_cases hmω : M.mem m ω
        · obtain ⟨i, hs, hiω⟩ := hω.1.2 m hmω
          exact ⟨i, hωκ i hiω, (read i y).mpr (Or.inr ⟨m, hm, hmy, Or.inl ⟨hmω, hs⟩⟩)⟩
        · exact ⟨m, hm, (read m y).mpr (Or.inr ⟨m, hm, hmy, Or.inr ⟨hmω, rfl⟩⟩)⟩
      · exact ⟨z, hωκ z hzω, (read z y).mpr (Or.inl ⟨rfl, rfl⟩)⟩
    obtain ⟨i, hi, val⟩ := pre
    obtain ⟨v, _, hiv⟩ := fn.2.1 i hi
    exact ⟨i, hi, unique i v y (select i v hiv) val ▸ hiv⟩

end YesMetaZFC.SetTheory.Internal
