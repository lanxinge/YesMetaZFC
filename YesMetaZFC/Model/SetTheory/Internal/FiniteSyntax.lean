import YesMetaZFC.Model.SetTheory.Internal.FiniteTruth
import YesMetaZFC.SetTheory.InnerModel.Recursion.Graph
import YesMetaZFC.SetTheory.KP.Natural

/-! # 有限求值证书的有界语法

标签与指令从原 Kuratowski 码读取，程序保持原编号。给定坐标界和实际值域界，
合法性可由 Δ₀ 公式检查，覆盖模型内部的非标准有限程序。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def num0_m : (k : Nat) → {n : Nat} → Term n → Formula 1 n
  | 0, _, x => Formula.forallMem x .falsum
  | k+1, _, x => Formula.existsMem x (.conj (num0_m k .newest) (KP.succ0_m x.weaken .newest))

@[simp] theorem num0_closed_l (k : Nat) {n} (x : Term n) (hx : x.freeSupport = []) : (num0_m k x).FreeClosed := by
  induction k generalizing n with
  | zero => simp -implicitDefEqProofs [num0_m, Definitional.Formula.FreeClosed, hx]
  | succ k ih => simp -implicitDefEqProofs [num0_m, Definitional.Formula.FreeClosed, hx, ih]

theorem num0_delta_l (k : Nat) {n} (x : Term n) : (num0_m k x).IsDelta0 := by
  induction k generalizing n with
  | zero => exact .forallMem _ .falsum
  | succ k ih => exact .existsMem _ (.conj (ih _) (KP.succ0_delta_l ..))

theorem num0_sat_l (hE : Extensional M) (k : Nat) {n} (ρ : Env M n) (x : Term n) :
    Formula.satisfies ρ (num0_m k x) ↔ Num_d k (x.eval ρ) := by
  induction k generalizing n with
  | zero => simp only [num0_m, Num_d, Formula.satisfies_forallMem_iff, Formula.satisfies_falsum_iff]
  | succ k ih =>
    simp only [num0_m, Num_d, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      ih, KP.succ0_sat_l hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
    exact ⟨fun ⟨y, _, hy⟩ => ⟨y, hy⟩, fun ⟨y, hy, hs⟩ => ⟨y, hs.predecessor_mem, hy, hs⟩⟩

def sop0_m (k : Nat) {n} (c i j : Term n) : Formula 1 n :=
  Formula.existsMem c (Formula.existsMem .newest (Formula.existsMem c.weaken.weaken
    (Formula.existsMem .newest (.conj (num0_m k .newest) (.conj
      (kpair0_m (.bound 2) i.weaken.weaken.weaken.weaken j.weaken.weaken.weaken.weaken)
      (kpair0_m c.weaken.weaken.weaken.weaken .newest (.bound 2)))))))
derive_free_closed sop0_m

theorem sop0_delta_l (k : Nat) {n} (c i j : Term n) : (sop0_m k c i j).IsDelta0 :=
  .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.conj (num0_delta_l ..)
    (.conj (kpair0_delta_l ..) (kpair0_delta_l ..))))))

theorem sop0_sat_l (hKP : M.Models KP) (k : Nat) {n} (ρ : Env M n) (c i j : Term n) :
    Formula.satisfies ρ (sop0_m k c i j) ↔ Sop_d (kp_pair_l hKP) k (c.eval ρ) (i.eval ρ) (j.eval ρ) := by
  simp only [sop0_m, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    num0_sat_l hKP.1, kpair0_sat_l hKP.1, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  refine ⟨fun ⟨_, _, a, _, _, _, o, _, ho, ha, hc⟩ => ⟨a, o, ho, ha, hc⟩, ?_⟩
  rintro ⟨a, o, ho, ha, hc⟩
  obtain ⟨s, hs, has⟩ := (kpair_union_l M hc a).mpr (Or.inr rfl)
  obtain ⟨t, ht, hot⟩ := (kpair_union_l M hc o).mpr (Or.inl rfl)
  exact ⟨s, hs, a, has, t, ht, o, hot, ho, ha, hc⟩

def Fb_node_d (hKP : M.Models KP) (b r c : M.Domain) : Prop :=
  ∃ i, M.mem i b ∧ ∃ j, M.mem j b ∧
    (Sop_d (kp_pair_l hKP) 0 c i j ∨ Sop_d (kp_pair_l hKP) 1 c i j ∨
      (Sop_d (kp_pair_l hKP) 2 c i j ∧ M.mem i r ∧ M.mem j r) ∨
      (Sop_d (kp_pair_l hKP) 3 c i j ∧ M.mem j r))

def fb_node_m {n} (b r c : Term n) : Formula 1 n := Formula.existsMem b (Formula.existsMem b.weaken
  (.disj (sop0_m 0 c.weaken.weaken (.bound 1) .newest)
    (.disj (sop0_m 1 c.weaken.weaken (.bound 1) .newest)
      (.disj (.conj (sop0_m 2 c.weaken.weaken (.bound 1) .newest)
        (.conj (.mem (.bound 1) r.weaken.weaken) (.mem .newest r.weaken.weaken)))
        (.conj (sop0_m 3 c.weaken.weaken (.bound 1) .newest) (.mem .newest r.weaken.weaken))))))
derive_free_closed fb_node_m

theorem Fb_node_d.operands_l (hKP : M.Models KP) {b r c i j : M.Domain} {k : Nat}
    (h : Fb_node_d hKP b r c) (hs : Sop_d (kp_pair_l hKP) k c i j) : M.mem i b ∧ M.mem j b := by
  obtain ⟨a, ha, d, hd, code⟩ := h
  have same {l} (ht : Sop_d (kp_pair_l hKP) l c a d) : M.mem i b ∧ M.mem j b := by
    obtain ⟨_, rfl, rfl⟩ := sop_injective_l _ hKP hs ht
    exact ⟨ha, hd⟩
  rcases code with h | h | h | h
  · exact same h
  · exact same h
  · exact same h.1
  · exact same h.1

theorem fb_node_delta_l {n} (b r c : Term n) : (fb_node_m b r c).IsDelta0 :=
  .existsMem _ (.existsMem _ (.disj (sop0_delta_l ..) (.disj (sop0_delta_l ..)
    (.disj (.conj (sop0_delta_l ..) (.conj (.mem _ _) (.mem _ _))) (.conj (sop0_delta_l ..) (.mem _ _))))))

theorem fb_node_sat_l (hKP : M.Models KP) {n} (ρ : Env M n) (b r c : Term n) :
    Formula.satisfies ρ (fb_node_m b r c) ↔ Fb_node_d hKP (b.eval ρ) (r.eval ρ) (c.eval ρ) := by
  simp only [fb_node_m, Fb_node_d, Formula.satisfies_existsMem_iff, Formula.satisfies_disj_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, sop0_sat_l hKP,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]; rfl

def Fb_program_d (hKP : M.Models KP) (ω b n L F : M.Domain) : Prop :=
  M.mem b ω ∧ M.mem n ω ∧ Fn0_d n L F ∧
    ∀ r, M.mem r n → ∀ c, M.mem c L → Rd_entry_d r c F → Fb_node_d hKP b r c

def fb_program_m {n} (ω b l L F : Term n) : Formula 1 n :=
  .conj (.mem b ω) (.conj (.mem l ω) (.conj (fn0_m l L F)
    (Formula.forallMem l (Formula.forallMem L.weaken
      (.imp (rd_entry0_m (.bound 1) .newest F.weaken.weaken) (fb_node_m b.weaken.weaken (.bound 1) .newest))))))
derive_free_closed fb_program_m

theorem fb_program_delta_l {n} (ω b l L F : Term n) : (fb_program_m ω b l L F).IsDelta0 :=
  .conj (.mem _ _) (.conj (.mem _ _) (.conj (fn0_delta_l ..)
    (.forallMem _ (.forallMem _ (.imp (rd_entry0_delta_l ..) (fb_node_delta_l ..))))))

theorem fb_program_sat_l (hKP : M.Models KP) {n} (ρ : Env M n) (ω b l L F : Term n) :
    Formula.satisfies ρ (fb_program_m ω b l L F) ↔
      Fb_program_d hKP (ω.eval ρ) (b.eval ρ) (l.eval ρ) (L.eval ρ) (F.eval ρ) := by
  simp only [fb_program_m, Fb_program_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    fn0_sat_l hKP.1, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    rd_entry0_sat_l hKP.1, fb_node_sat_l hKP, Definitional.Term.eval_weaken]; rfl

theorem fb_program_of_l (hKP : M.Models KP) {ω b n L F : M.Domain}
    (hF : Sfm_d (kp_pair_l hKP) ω n F) (hb : M.mem b ω) (bound : Sbound_d (kp_pair_l hKP) F b)
    (hf : Fn0_d n L F) : Fb_program_d hKP ω b n L F := by
  refine ⟨hb, hF.1, hf, fun r _ c _ hc => ?_⟩
  rcases hF.2.2 r c hc with ⟨i, j, hs, _, _⟩ | ⟨i, j, hs, _, _⟩ |
    ⟨i, j, hs, hi, hj⟩ | ⟨i, j, hs, _, hj⟩
  · exact ⟨i, (bound.operands_l _ hc hs).1, j, (bound.operands_l _ hc hs).2, Or.inl hs⟩
  · exact ⟨i, (bound.operands_l _ hc hs).1, j, (bound.operands_l _ hc hs).2, Or.inr (Or.inl hs)⟩
  · exact ⟨i, (bound.operands_l _ hc hs).1, j, (bound.operands_l _ hc hs).2, Or.inr (Or.inr (Or.inl ⟨hs, hi, hj⟩))⟩
  · exact ⟨i, (bound.operands_l _ hc hs).1, j, (bound.operands_l _ hc hs).2, Or.inr (Or.inr (Or.inr ⟨hs, hj⟩))⟩

theorem Fb_program_d.read_l (hZF : M.Models ZF) {ω b n L F : M.Domain} (hω : M.IsOmega ω)
    (h : Fb_program_d (ZF.modelsKP hZF) ω b n L F) : Sfm_d (kp_pair_l (ZF.modelsKP hZF)) ω n F ∧
      Sbound_d (kp_pair_l (ZF.modelsKP hZF)) F b := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have row r c (hc : Rd_entry_d r c F) := h.2.2.2 r (h.2.2.1.bound_l hc).1 c (h.2.2.1.bound_l hc).2 hc
  refine ⟨⟨h.2.1, ⟨(hω.isOrdinal hZF).mem h.2.1, (fn0_function_l (ZF.modelsKP hZF) h.2.2.1).1,
    (fn0_function_l (ZF.modelsKP hZF) h.2.2.1).2.1⟩, fun r c hc => ?_⟩, fun r i j coord => ?_⟩
  · obtain ⟨i, hi, j, hj, hs | hs | hs | hs⟩ := row r c hc
    · exact Or.inl ⟨i, j, hs, hω.transitive hZF b h.1 i hi, hω.transitive hZF b h.1 j hj⟩
    · exact Or.inr (Or.inl ⟨i, j, hs, hω.transitive hZF b h.1 i hi, hω.transitive hZF b h.1 j hj⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨i, j, hs⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨i, j, hs.1, hω.transitive hZF b h.1 i hi, hs.2⟩))
  · obtain ⟨c, o, a, hc, hco, ha⟩ := coord
    have finish {k i' j'} (hi : M.mem i' b) (hj : M.mem j' b) (hs : Sop_d I k c i' j') :
        M.mem i b ∧ M.mem j b := by
      obtain ⟨a', o', _, ha', hc'⟩ := hs
      obtain ⟨_, e⟩ := I.injective hco hc'
      obtain ⟨rfl, rfl⟩ := I.injective ha (e.symm ▸ ha')
      exact ⟨hi, hj⟩
    obtain ⟨i', hi, j', hj, hs | hs | hs | hs⟩ := row r c hc
    · exact finish hi hj hs
    · exact finish hi hj hs
    · exact finish hi hj hs.1
    · exact finish hi hj hs.1

end YesMetaZFC.SetTheory.Internal
