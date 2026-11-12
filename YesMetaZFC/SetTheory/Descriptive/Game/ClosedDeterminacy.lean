import YesMetaZFC.SetTheory.Descriptive.Tree.TreeTail
import YesMetaZFC.SetTheory.Descriptive.Game.GameShift
import YesMetaZFC.SetTheory.Ord.DefinableMinimum
import YesMetaZFC.SetTheory.Ord.Recursion

/-! # 首次违规者输的闭收益集合

L 是逐步检查通过的实际有限历史集合，J 是玩家 I 负责的内部时刻集合。
先构造玩家 I 首次违规的有限证据，再排除所有含有这些证据的前缀。
玩家 II 先违规后继续落子的记录因此仍被判给 I。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Cg_first_d (ω A S L i p : M.Domain) : Prop :=
  ∃ j, M.mem j ω ∧ Fn0_d j A p ∧ M.SuccessorOf j i ∧ ¬ M.mem p L ∧
    ∀ q, M.mem q S → M.MemberSubset q p → ¬ M.MemberSubset p q → M.mem q L

def cg_first_m {d} (ω A S L i p : Term d) : Formula 1 d := set[d] ⟪∃ j ∈ ⌜ω⌝ₛ,
  ⌜fn0_m⌝ₚ(j, ⌜A⌝ₛ, ⌜p⌝ₛ) ∧ ⌜Formula.isSuccessor⌝ₚ(j, ⌜i⌝ₛ) ∧ ¬ (⌜p⌝ₛ ∈ ⌜L⌝ₛ) ∧
  (∀ q ∈ ⌜S⌝ₛ, q ⊆ ⌜p⌝ₛ → ¬ (⌜p⌝ₛ ⊆ q) → q ∈ ⌜L⌝ₛ)⟫
derive_free_closed cg_first_m

theorem cg_first_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A S L i p : Term d) :
    Formula.satisfies ρ (cg_first_m ω A S L i p) ↔ Cg_first_d
      (ω.eval ρ) (A.eval ρ) (S.eval ρ) (L.eval ρ) (i.eval ρ) (p.eval ρ) := by
  simp only [cg_first_m, Cg_first_d, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    fn0_sat_l hE, Formula.satisfies_isSuccessor_iff, Formula.satisfies_neg_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff, Formula.satisfies_subset_iff, Definitional.Term.eval_weaken]
  rfl

def Cg_bad_d (ω A S L J D : M.Domain) : Prop :=
  ∀ p, M.mem p D ↔ M.mem p S ∧ ∃ i, M.mem i J ∧ Cg_first_d ω A S L i p

def Cg_safe_d (S D T : M.Domain) : Prop :=
  ∀ p, M.mem p T ↔ M.mem p S ∧ ∀ q, M.mem q D → ¬ M.MemberSubset q p

def Cg_payoff_d (ω A S L J B W : M.Domain) : Prop :=
  ∃ D T, Cg_bad_d ω A S L J D ∧ Cg_safe_d S D T ∧ Body_d S B T W

/-- 收益集和其开补集都由对象模型的分离构造，参数不含外部历史列表。 -/
theorem cg_payoff_l (hZF : M.Models ZF) (ω A S L J B : M.Domain) :
    ∃ W O, Cg_payoff_d ω A S L J B W ∧
      (∀ f, M.mem f O ↔ M.mem f B ∧ ¬ M.mem f W) ∧ Open_d S B O := by
  let ρ : Env M 5 := (((((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push A).push S).push L).push J)
  let φ : UnarySchema 5 := { body := set[6] ⟪∃ i ∈ ⌜(.bound 1 : Term 6)⌝ₛ,
    ⌜cg_first_m⌝ₚ(⌜(.bound 5 : Term 6)⌝ₛ, ⌜(.bound 4 : Term 6)⌝ₛ, ⌜(.bound 3 : Term 6)⌝ₛ,
      ⌜(.bound 2 : Term 6)⌝ₛ, i, ⌜(.newest : Term 6)⌝ₛ)⟫ }
  obtain ⟨D, sep⟩ := ZF.separation_exists_d hZF φ ρ S
  have bad : Cg_bad_d ω A S L J D := by
    intro p
    refine (sep p).trans (and_congr Iff.rfl ?_)
    simp only [φ, Formula.satisfies_existsMem_iff, cg_first_sat_l hZF.1, Definitional.Term.eval_weaken]
    rfl
  let η : Env M 1 := ⟨fun _ => D, fun _ => D⟩
  let ψ : UnarySchema 1 := { body := set[2] ⟪∀ q ∈ ⌜(.bound 1 : Term 2)⌝ₛ, ¬ (q ⊆ ⌜(.newest : Term 2)⌝ₛ)⟫ }
  obtain ⟨T, cut⟩ := ZF.separation_exists_d hZF ψ η S
  have safe : Cg_safe_d S D T := by
    intro p
    refine (cut p).trans (and_congr Iff.rfl ?_)
    simp only [ψ, Formula.satisfies_forallMem_iff, Formula.satisfies_neg_iff,
      Formula.satisfies_subset_iff, Definitional.Term.eval_weaken]
    rfl
  obtain ⟨W, body⟩ := tree_body_exists_l (ZF.modelsKP hZF) S B T
  obtain ⟨O, complement, opened⟩ := tree_body_closed_l (ZF.modelsKP hZF) body
  exact ⟨W, O, ⟨D, T, bad, safe, body⟩, complement, opened⟩

theorem Cg_safe_d.tree_l {S D T : M.Domain} (safe : Cg_safe_d (M := M) S D T) : Tree_d S T := by
  refine ⟨fun p hp => ((safe p).mp hp).1, fun p hp q hq sub => ?_⟩
  exact (safe q).mpr ⟨hq, fun b hb bs => ((safe p).mp hp).2 b hb (fun x hx => sub x (bs x hx))⟩

/-- 玩家 I 的败局恰由有限的首次违规证据见证；否则对局属于闭收益集。 -/
theorem Cg_payoff_d.read_l {ω A S L J B W f : M.Domain}
    (payoff : Cg_payoff_d (M := M) ω A S L J B W) (hf : M.mem f B) :
    ¬ M.mem f W ↔ ∃ p i, M.mem p S ∧ M.MemberSubset p f ∧ M.mem i J ∧ Cg_first_d ω A S L i p := by
  classical
  obtain ⟨D, T, bad, safe, body⟩ := payoff
  constructor
  · intro lose
    have witness : ∃ p, M.mem p S ∧ M.MemberSubset p f ∧ ¬ M.mem p T := by
      apply Classical.byContradiction
      intro h
      exact lose ((body f).mpr ⟨hf, fun p hp sub => Classical.byContradiction (fun no => h ⟨p, hp, sub, no⟩)⟩)
    obtain ⟨p, hp, sub, no⟩ := witness
    have witness : ∃ q, M.mem q D ∧ M.MemberSubset q p := by
      apply Classical.byContradiction
      intro h
      exact no ((safe p).mpr ⟨hp, fun q hq qp => h ⟨q, hq, qp⟩⟩)
    obtain ⟨q, hq, qp⟩ := witness
    obtain ⟨hqS, i, hi, first⟩ := (bad q).mp hq
    exact ⟨q, i, hqS, fun x hx => sub x (qp x hx), hi, first⟩
  · rintro ⟨p, i, hp, sub, hi, first⟩ win
    have pt := ((body f).mp win).2 p hp sub
    exact ((safe p).mp pt).2 p ((bad p).mpr ⟨hp, i, hi, first⟩) (fun _ h => h)

theorem Cg_payoff_d.all_legal_l {ω A S L J B W f : M.Domain}
    (payoff : Cg_payoff_d (M := M) ω A S L J B W) (hf : M.mem f B)
    (legal : ∀ p, M.mem p S → M.MemberSubset p f → M.mem p L) : M.mem f W := by
  apply Classical.byContradiction
  intro no
  obtain ⟨p, _, hp, sub, _, _, _, _, _, bad, _⟩ := (payoff.read_l hf).mp no
  exact bad (legal p hp sub)

end YesMetaZFC.SetTheory.Descriptive

/-! ## 首次违规的唯一性及玩家 II 违规后的吸收

同一对局的两个有限前缀按包含可比较。较长的首次违规证据会把较短的
证据判为合法，故两者必须相同；无需对外部 ω 作良基归纳。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem cg_first_unique_l (hKP : M.Models KP) {ω A S L i j p q f : M.Domain}
    (hω : M.IsOrdinal ω) (hf : M.IsSetFunction (kp_pair_l hKP) f)
    (hp : M.mem p S) (hq : M.mem q S) (pf : M.MemberSubset p f) (qf : M.MemberSubset q f)
    (first : Cg_first_d ω A S L i p) (second : Cg_first_d ω A S L j q) : p = q ∧ i = j := by
  classical
  obtain ⟨m, hm, fm, sm, badp, beforep⟩ := first
  obtain ⟨n, hn, fn, sn, badq, beforeq⟩ := second
  have eq : p = q := by
    rcases ds_prefix_compare_l (kp_pair_l hKP) hKP.1 hω hm hn (fn0_function_l hKP fm)
      (fn0_function_l hKP fn) hf pf qf with pq | qp
    · have qp : M.MemberSubset q p := Classical.byContradiction (fun no => badp (beforeq p hp pq no))
      exact hKP.1.eq_of_same_members p q (fun x => ⟨pq x, qp x⟩)
    · have pq : M.MemberSubset p q := Classical.byContradiction (fun no => badq (beforep q hq qp no))
      exact hKP.1.eq_of_same_members p q (fun x => ⟨pq x, qp x⟩)
  subst q
  have lengths := fm.domain_eq_l hKP.1 fn
  subst n
  exact ⟨rfl, Structure.SuccessorOf.predecessor_eq hKP.1 ((hω.mem hm).mem sm.predecessor_mem) sm sn⟩

theorem Cg_payoff_d.ii_first_l (hKP : M.Models KP) {ω A S L J B W f p i : M.Domain}
    (payoff : Cg_payoff_d (M := M) ω A S L J B W) (hω : M.IsOrdinal ω)
    (hf : M.IsSetFunction (kp_pair_l hKP) f) (hfB : M.mem f B) (hp : M.mem p S)
    (pf : M.MemberSubset p f) (first : Cg_first_d ω A S L i p) (turn : ¬ M.mem i J) : M.mem f W := by
  apply Classical.byContradiction
  intro no
  obtain ⟨q, j, hq, qf, hj, second⟩ := (payoff.read_l hfB).mp no
  exact turn ((cg_first_unique_l hKP hω hf hp hq pf qf first second).2.symm ▸ hj)

end YesMetaZFC.SetTheory.Descriptive

/-! ## 首次违规收益的完整一阶表示

坏前缀、吸收树和树体逐项使用已有数学定义。收益公式可随同实际
检查表搬运，也可用于分离补树游戏的 I 获胜参数集合。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def cg_bad_m {d} (ω A F L J D : Term d) : Formula 1 d := set[d] ⟪∀ p,
  p ∈ ⌜D⌝ₛ ↔ p ∈ ⌜F⌝ₛ ∧ (∃ i ∈ ⌜J⌝ₛ, ⌜cg_first_m⌝ₚ(⌜ω⌝ₛ,⌜A⌝ₛ,⌜F⌝ₛ,⌜L⌝ₛ,i,p))⟫
derive_free_closed cg_bad_m

theorem cg_bad_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A F L J D : Term d) :
    Formula.satisfies ρ (cg_bad_m ω A F L J D) ↔
      Cg_bad_d (ω.eval ρ) (A.eval ρ) (F.eval ρ) (L.eval ρ) (J.eval ρ) (D.eval ρ) := by
  simp only [cg_bad_m,Cg_bad_d,Formula.satisfies_forall_iff,Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff,Formula.satisfies_conj_iff,Formula.satisfies_existsMem_iff,
    cg_first_sat_l hE,Definitional.Term.eval_weaken]
  rfl

def cg_safe_m {d} (F D T : Term d) : Formula 1 d := set[d] ⟪∀ p,
  p ∈ ⌜T⌝ₛ ↔ p ∈ ⌜F⌝ₛ ∧ (∀ q ∈ ⌜D⌝ₛ, ¬ (q ⊆ p))⟫
derive_free_closed cg_safe_m

theorem cg_safe_sat_l {d} (ρ : Env M d) (F D T : Term d) :
    Formula.satisfies ρ (cg_safe_m F D T) ↔ Cg_safe_d (M := M) (F.eval ρ) (D.eval ρ) (T.eval ρ) := by
  simp only [cg_safe_m,Cg_safe_d,Formula.satisfies_forall_iff,Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff,Formula.satisfies_conj_iff,Formula.satisfies_forallMem_iff,
    Formula.satisfies_neg_iff,Formula.satisfies_subset_iff,Definitional.Term.eval_weaken]
  rfl

def cg_payoff_m {d} (ω A F L J B W : Term d) : Formula 1 d := set[d] ⟪∃ D T,
  ⌜cg_bad_m⌝ₚ(⌜ω⌝ₛ,⌜A⌝ₛ,⌜F⌝ₛ,⌜L⌝ₛ,⌜J⌝ₛ,D) ∧
    ⌜cg_safe_m⌝ₚ(⌜F⌝ₛ,D,T) ∧ ⌜body_m⌝ₚ(⌜F⌝ₛ,⌜B⌝ₛ,T,⌜W⌝ₛ)⟫
derive_free_closed cg_payoff_m

theorem cg_payoff_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A F L J B W : Term d) :
    Formula.satisfies ρ (cg_payoff_m ω A F L J B W) ↔
      Cg_payoff_d (ω.eval ρ) (A.eval ρ) (F.eval ρ) (L.eval ρ) (J.eval ρ) (B.eval ρ) (W.eval ρ) := by
  simp only [cg_payoff_m,Cg_payoff_d,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    cg_bad_sat_l hE,cg_safe_sat_l,body_sat_l,Definitional.Term.eval_weaken]
  rfl

end YesMetaZFC.SetTheory.Descriptive

/-! ## 全部有限轮均合法的内部历史树

逐步检查集合 L 只检查最新走法；本树要求历史的每个前缀都通过检查。
它与首次违规后吸收的胜负树各司其职，二者均由同一实际检查集合构造。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}}

def Cg_legal_d (F L G : M.Domain) : Prop := ∀ h,
  M.mem h G ↔ M.mem h F ∧ ∀ q, M.mem q F → M.MemberSubset q h → M.mem q L

def cg_legal_m {d} (F L G : Term d) : Formula 1 d := set[d] ⟪∀ h,
  h ∈ ⌜G⌝ₛ ↔ h ∈ ⌜F⌝ₛ ∧ (∀ q ∈ ⌜F⌝ₛ, q ⊆ h → q ∈ ⌜L⌝ₛ)⟫
derive_free_closed cg_legal_m

theorem cg_legal_sat_l {d} (ρ : Env M d) (F L G : Term d) :
    Formula.satisfies ρ (cg_legal_m F L G) ↔ Cg_legal_d (M := M) (F.eval ρ) (L.eval ρ) (G.eval ρ) := by
  simp only [cg_legal_m, Cg_legal_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_subset_iff, Definitional.Term.eval_weaken]
  rfl

theorem cg_legal_l (hKP : M.Models KP) (F L : M.Domain) : ∃ G, Cg_legal_d (M := M) F L G ∧ Tree_d F G := by
  let ρ : Env M 2 := (⟨fun _ => F, fun _ => F⟩ : Env M 1).push L
  let φ : Delta0UnarySchema 2 := {
    body := set[3] ⟪∀ q ∈ ⌜(.bound 2 : Term 3)⌝ₛ, q ⊆ ⌜(.newest : Term 3)⌝ₛ → q ∈ ⌜(.bound 1 : Term 3)⌝ₛ⟫
    delta0 := .forallMem _ (.imp (.atom _ _ _) (.mem _ _)) }
  obtain ⟨G, sep⟩ := KP.separation_exists_d hKP φ ρ F
  have legal : Cg_legal_d F L G := by
    intro h
    refine (sep h).trans (and_congr Iff.rfl ?_)
    simp only [φ, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff, Formula.satisfies_subset_iff,
      Formula.satisfies_mem_iff, Definitional.Term.eval_weaken]
    rfl
  exact ⟨G, legal, fun h hh => ((legal h).mp hh).1, fun h hh q hq sub =>
    (legal q).mpr ⟨hq, fun t ht tq => ((legal h).mp hh).2 t ht (fun x hx => sub x (tq x hx))⟩⟩

theorem Cg_legal_d.current_l {F L G h : M.Domain} (legal : Cg_legal_d (M := M) F L G) (hh : M.mem h G) : M.mem h L :=
  ((legal h).mp hh).2 h ((legal h).mp hh).1 (fun _ hx => hx)

theorem Cg_legal_d.prefix_l {F L G h q : M.Domain} (legal : Cg_legal_d (M := M) F L G)
    (hh : M.mem h G) (hq : M.mem q F) (sub : M.MemberSubset q h) : M.mem q G :=
  (legal q).mpr ⟨hq, fun t ht tq => ((legal h).mp hh).2 t ht (fun x hx => sub x (tq x hx))⟩

end YesMetaZFC.SetTheory.Descriptive

/-! ## 枚举中的最小合法走法

合法性只读取既定有限历史集合 L，故同一算法可用于地模型及其力迫扩张。
无合法项时返回内部零；有合法项时返回真正的最小编号，整个选择表由 ZF 构造。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Cg_admit_d (ω L h a : M.Domain) : Prop := ∃ t, M.mem t L ∧ Fseq_end_d I ω t h a
def cg_admit_m {d} (ω L h a : Term d) : Formula 1 d := set[d] ⟪∃ t ∈ ⌜L⌝ₛ,
  ⌜fseq_end_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, t, ⌜h⌝ₛ, ⌜a⌝ₛ)⟫
derive_free_closed cg_admit_m

theorem cg_admit_sat_l {d} (ρ : Env M d) (ω L h a : Term d) :
    Formula.satisfies ρ (cg_admit_m ω L h a) ↔ Cg_admit_d hZF (ω.eval ρ) (L.eval ρ) (h.eval ρ) (a.eval ρ) := by
  simp only [cg_admit_m, Cg_admit_d, Formula.satisfies_existsMem_iff, fseq_end_sat_l I hZF.1,
    Definitional.Term.eval_weaken]; rfl

def Cg_scan_d (ω L g h i : M.Domain) : Prop := M.mem i ω ∧
  (∃ a, Rd_entry_d i a g ∧ Cg_admit_d hZF ω L h a) ∧
  ∀ j a, M.mem j i → Rd_entry_d j a g → ¬ Cg_admit_d hZF ω L h a

def cg_scan_m {d} (ω L g h i : Term d) : Formula 1 d := set[d] ⟪⌜i⌝ₛ ∈ ⌜ω⌝ₛ ∧
  (∃ a, ⌜rd_entry0_m⌝ₚ(⌜i⌝ₛ, a, ⌜g⌝ₛ) ∧ ⌜cg_admit_m⌝ₚ(⌜ω⌝ₛ, ⌜L⌝ₛ, ⌜h⌝ₛ, a)) ∧
  (∀ j a, j ∈ ⌜i⌝ₛ → ⌜rd_entry0_m⌝ₚ(j, a, ⌜g⌝ₛ) → ¬ ⌜cg_admit_m⌝ₚ(⌜ω⌝ₛ, ⌜L⌝ₛ, ⌜h⌝ₛ, a))⟫
derive_free_closed cg_scan_m

theorem cg_scan_sat_l {d} (ρ : Env M d) (ω L g h i : Term d) :
    Formula.satisfies ρ (cg_scan_m ω L g h i) ↔ Cg_scan_d hZF (ω.eval ρ) (L.eval ρ) (g.eval ρ) (h.eval ρ) (i.eval ρ) := by
  simp only [cg_scan_m, Cg_scan_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_exists_iff, rd_entry0_sat_l hZF.1, cg_admit_sat_l hZF,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_neg_iff, Definitional.Term.eval_weaken]; rfl

theorem Cg_scan_d.le_l {ω L g h i j a : M.Domain} (hw : M.IsOmega ω) (scan : Cg_scan_d hZF ω L g h i)
    (hj : M.mem j ω) (ja : Rd_entry_d j a g) (legal : Cg_admit_d hZF ω L h a) : M.mem i j ∨ i = j := by
  rcases (hw.isOrdinal (ZF.modelsKP hZF)).wellOrder.linear.compare i scan.1 j hj with eq | lt | gt
  · exact Or.inr (hZF.1.eq_of_same_members i j eq)
  · exact Or.inl lt
  · exact (scan.2.2 j a gt ja legal).elim

theorem Cg_scan_d.unique_l {ω L g h i j : M.Domain} (hw : M.IsOmega ω)
    (scan : Cg_scan_d hZF ω L g h i) (other : Cg_scan_d hZF ω L g h j) : i = j := by
  obtain ⟨a, ja, legal⟩ := other.2.1
  rcases scan.le_l hZF hw other.1 ja legal with lt | eq
  · obtain ⟨b, ib, legal⟩ := scan.2.1
    exact (other.2.2 i b lt ib legal).elim
  · exact eq

theorem cg_scan_exists_l {ω L g h : M.Domain} (hw : M.IsOmega ω)
    (hit : ∃ i a, M.mem i ω ∧ Rd_entry_d i a g ∧ Cg_admit_d hZF ω L h a) :
    ∃ i, Cg_scan_d hZF ω L g h i := by
  let ρ : Env M 4 := ⟨fun i => [ω, L, g, h].get i, fun _ => ω⟩
  let φ : UnarySchema 4 := { body := set[5] ⟪⌜(.newest : Term 5)⌝ₛ ∈ ⌜(.bound 1 : Term 5)⌝ₛ ∧
    (∃ a, ⌜rd_entry0_m⌝ₚ(⌜(.newest : Term 5)⌝ₛ, a, ⌜(.bound 3 : Term 5)⌝ₛ) ∧
      ⌜cg_admit_m⌝ₚ(⌜(.bound 1 : Term 5)⌝ₛ, ⌜(.bound 2 : Term 5)⌝ₛ, ⌜(.bound 4 : Term 5)⌝ₛ, a))⟫ }
  have sat i : φ.denote ρ i ↔ M.mem i ω ∧ ∃ a, Rd_entry_d i a g ∧ Cg_admit_d hZF ω L h a := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_exists_iff, rd_entry0_sat_l hZF.1, cg_admit_sat_l hZF, Definitional.Term.eval_weaken]; rfl
  obtain ⟨i, a, hi, ia, legal⟩ := hit
  obtain ⟨j, _, hj, least⟩ := ZF.ordinal_min_l hZF φ ρ (hw.members_areOrdinals (ZF.modelsKP hZF) i hi)
    ((sat i).mpr ⟨hi, a, ia, legal⟩)
  have hj := (sat j).mp hj
  exact ⟨j, hj.1, hj.2, fun k a hk ka legal => least k hk
    ((sat k).mpr ⟨hw.transitive (ZF.modelsKP hZF) j hj.1 k hk, a, ka, legal⟩)⟩

/-- 对全部有限历史一次构造最小编号表；不要求每个历史都存在合法后继。 -/
theorem cg_selector_l {ω e F L g : M.Domain} (hw : M.IsOmega ω) (he : ∀ x, ¬ M.mem x e) :
    ∃ K, Fn0_d F ω K ∧ ∀ h i, Rd_entry_d h i K →
      (∃ j a, M.mem j ω ∧ Rd_entry_d j a g ∧ Cg_admit_d hZF ω L h a) → Cg_scan_d hZF ω L g h i := by
  classical
  let ρ : Env M 4 := ⟨fun i => [ω, e, L, g].get i, fun _ => ω⟩
  let φ : BinarySchema 4 := { body := set[6] ⟪
    ⌜cg_scan_m⌝ₚ(⌜(.bound 2 : Term 6)⌝ₛ, ⌜(.bound 4 : Term 6)⌝ₛ, ⌜(.bound 5 : Term 6)⌝ₛ,
      ⌜(.bound 1 : Term 6)⌝ₛ, ⌜(.bound 0 : Term 6)⌝ₛ) ∨
    (⌜(.bound 0 : Term 6)⌝ₛ = ⌜(.bound 3 : Term 6)⌝ₛ ∧ ¬ (∃ i a, i ∈ ⌜(.bound 2 : Term 6)⌝ₛ ∧
      ⌜rd_entry0_m⌝ₚ(i, a, ⌜(.bound 5 : Term 6)⌝ₛ) ∧
      ⌜cg_admit_m⌝ₚ(⌜(.bound 2 : Term 6)⌝ₛ, ⌜(.bound 4 : Term 6)⌝ₛ, ⌜(.bound 1 : Term 6)⌝ₛ, a)))⟫ }
  let hit h := ∃ j a, M.mem j ω ∧ Rd_entry_d j a g ∧ Cg_admit_d hZF ω L h a
  have sat h i : φ.denote ρ h i ↔ Cg_scan_d hZF ω L g h i ∨ i = e ∧ ¬ hit h := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_disj_iff, cg_scan_sat_l hZF,
      Formula.satisfies_conj_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1, Formula.satisfies_neg_iff,
      Formula.satisfies_exists_iff, Formula.satisfies_mem_iff, rd_entry0_sat_l hZF.1,
      cg_admit_sat_l hZF, Definitional.Term.eval_weaken]; rfl
  have seen h i (scan : Cg_scan_d hZF ω L g h i) : hit h :=
    scan.2.1.elim fun a ha => ⟨i, a, scan.1, ha⟩
  obtain ⟨K, fn, graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := F) (target := ω) (by
    intro h _
    by_cases yes : hit h
    · obtain ⟨i, scan⟩ := cg_scan_exists_l hZF hw yes
      exact ⟨i, (sat h i).mpr (Or.inl scan)⟩
    · exact ⟨e, (sat h e).mpr (Or.inr ⟨rfl, yes⟩)⟩) (by
    intro h _ i j hi hj
    rcases (sat h i).mp hi with si | ⟨ie, no⟩ <;> rcases (sat h j).mp hj with sj | ⟨je, no'⟩
    · exact si.unique_l hZF hw sj
    · exact (no' (seen h i si)).elim
    · exact (no (seen h j sj)).elim
    · exact ie.trans je.symm) (by
    intro h i _ hi
    exact ((sat h i).mp hi).elim And.left (fun h => h.1.symm ▸ num_mem_l hZF.1 hw (show Num_d 0 e from he)))
  exact ⟨K, fn0_of_function_l (ZF.modelsKP hZF) fn, fun h i hi yes =>
    ((sat h i).mp ((graph h i).mp hi).2).elim id (fun no => (no.2 yes).elim)⟩

end YesMetaZFC.SetTheory.Descriptive

/-! ## 合法追加的有界读法

在既定有限历史空间中，追加关系只量化旧 L、ω 和实际图的成员。
这个等价式用于成员满地嵌入，避免把含类型语义的游戏规则重新解释于扩张。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def ds_end_bound_m {d} (ω X t h a : Term d) : Formula 1 d := set[d] ⟪∃ n ∈ ⌜ω⌝ₛ, ∃ m ∈ ⌜ω⌝ₛ,
  ⌜fn0_m⌝ₚ(n, ⌜X⌝ₛ, ⌜h⌝ₛ) ∧ ⌜fn0_m⌝ₚ(m, ⌜X⌝ₛ, ⌜t⌝ₛ) ∧ ⌜KP.succ0_m⌝ₚ(m, n) ∧
  ⌜h⌝ₛ ⊆ ⌜t⌝ₛ ∧ ⌜rd_entry0_m⌝ₚ(n, ⌜a⌝ₛ, ⌜t⌝ₛ)⟫
derive_free_closed ds_end_bound_m

theorem ds_end_bound_delta_l {d} (ω X t h a : Term d) : (ds_end_bound_m ω X t h a).IsDelta0 :=
  .existsMem _ (.existsMem _ (.conj (fn0_delta_l ..) (.conj (fn0_delta_l ..)
    (.conj (KP.succ0_delta_l ..) (.conj (.atom _ (by decide) _) (rd_entry0_delta_l ..))))))

theorem ds_end_bound_sat_l {d} (ρ : Env M d) (ω X t h a : Term d)
    (hw : M.IsOmega (ω.eval ρ)) {F : M.Domain} (space : Fseq_space_d I (ω.eval ρ) (X.eval ρ) F)
    (ht : M.mem (t.eval ρ) F) (hh : M.mem (h.eval ρ) F) :
    Formula.satisfies ρ (ds_end_bound_m ω X t h a) ↔ Fseq_end_d I (ω.eval ρ) (t.eval ρ) (h.eval ρ) (a.eval ρ) := by
  simp only [ds_end_bound_m, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    fn0_sat_l hZF.1, KP.succ0_sat_l hZF.1, Formula.satisfies_subset_iff, rd_entry0_sat_l hZF.1, Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨n, hn, m, hm, fh, ft, succ, sub, last⟩
    have fh := fn0_function_l (ZF.modelsKP hZF) fh
    have ft := fn0_function_l (ZF.modelsKP hZF) ft
    exact ⟨m, n, ⟨hm, hw.members_areOrdinals (ZF.modelsKP hZF) m hm, ft.1, ft.2.1⟩, hn, succ,
      ⟨hn, hw.members_areOrdinals (ZF.modelsKP hZF) n hn, fh.1, fh.2.1⟩, (ds_restrict_iff_l I fh ft.1).mpr sub, last⟩
  · rintro ⟨m, n, decomp⟩
    obtain ⟨j, hj, fh⟩ := (space (h.eval ρ)).mp hh
    obtain ⟨k, hk, ft⟩ := (space (t.eval ρ)).mp ht
    have ej := fh.2.1.eq hZF.1 decomp.prefix_sequence.2.2.2
    have ek := ft.2.1.eq hZF.1 decomp.source.2.2.2
    subst j k
    exact ⟨n, hj, m, hk, fn0_of_function_l (ZF.modelsKP hZF) fh, fn0_of_function_l (ZF.modelsKP hZF) ft,
      decomp.length_successor, Fseq_end_d.subset_l I ⟨m, n, decomp⟩, decomp.last_value⟩

def cg_admit_bound_m {d} (ω X L h a : Term d) : Formula 1 d :=
  .existsMem L (ds_end_bound_m ω.weaken X.weaken .newest h.weaken a.weaken)
derive_free_closed cg_admit_bound_m

theorem cg_admit_bound_delta_l {d} (ω X L h a : Term d) : (cg_admit_bound_m ω X L h a).IsDelta0 :=
  .existsMem _ (ds_end_bound_delta_l ..)

theorem cg_admit_bound_sat_l {d} (ρ : Env M d) (ω X L h a : Term d)
    (hw : M.IsOmega (ω.eval ρ)) {F : M.Domain} (space : Fseq_space_d I (ω.eval ρ) (X.eval ρ) F)
    (legal : M.MemberSubset (L.eval ρ) F) (hh : M.mem (h.eval ρ) F) :
    Formula.satisfies ρ (cg_admit_bound_m ω X L h a) ↔ Cg_admit_d hZF (ω.eval ρ) (L.eval ρ) (h.eval ρ) (a.eval ρ) := by
  simp only [cg_admit_bound_m, Formula.satisfies_existsMem_iff, Cg_admit_d]
  refine exists_congr fun t => and_congr_right fun ht => ?_
  simpa only [Definitional.Term.eval_weaken, Definitional.Term.eval_newest] using
    ds_end_bound_sat_l hZF (ρ.push t) ω.weaken X.weaken .newest h.weaken a.weaken
      (by simpa only [Definitional.Term.eval_weaken] using hw)
      (by simpa only [Definitional.Term.eval_weaken] using space) (legal t ht)
      (by simpa only [Definitional.Term.eval_weaken] using hh)

end YesMetaZFC.SetTheory.Descriptive

/-! ## 集合字母表与固定时序上的内部策略

J 指定玩家 I 的时刻，补集指定玩家 II。策略仍是全部有限历史上的实际
集合编码函数，服从条件逐个内部时刻检查；允许同一玩家连续负责两个阶段。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Cg_follows_d (p : Bool) (ω J σ f : M.Domain) : Prop :=
  ∀ i, M.mem i ω → (if p then M.mem i J else ¬ M.mem i J) →
    ∀ h, M.IsRestrictionOf I h f i → ∀ v, Rd_entry_d i v f → Rd_entry_d h v σ

def Cg_win_d (p : Bool) (ω X F J B W σ : M.Domain) : Prop := Fn0_d F X σ ∧
  ∀ f, M.mem f B → Cg_follows_d I p ω J σ f → if p then M.mem f W else ¬ M.mem f W

def cg_follows_m (p : Bool) {d} (ω J σ f : Term d) : Formula 1 d :=
  Formula.forallMem ω (.imp (if p then .mem .newest J.weaken else .neg (.mem .newest J.weaken))
    (.forallE (.imp (Formula.isRestriction kpair_convention_l .newest f.weaken.weaken (.bound 1))
      (.forallE (.imp (rd_entry0_m (.bound 2) .newest f.weaken.weaken.weaken)
        (rd_entry0_m (.bound 1) .newest σ.weaken.weaken.weaken))))))

@[simp] theorem cg_follows_closed_l (p : Bool) {d} (ω J σ f : Term d)
    (hw : ω.freeSupport = []) (hj : J.freeSupport = []) (hs : σ.freeSupport = []) (hf : f.freeSupport = []) :
    (cg_follows_m p ω J σ f).FreeClosed := by
  cases p <;> simp -implicitDefEqProofs [cg_follows_m, Definitional.Formula.FreeClosed, hw, hj, hs, hf]

theorem cg_follows_sat_l (hE : Extensional M) (p : Bool) {d} (ρ : Env M d) (ω J σ f : Term d) :
    Formula.satisfies ρ (cg_follows_m p ω J σ f) ↔ Cg_follows_d I p (ω.eval ρ) (J.eval ρ) (σ.eval ρ) (f.eval ρ) := by
  cases p <;> simp only [cg_follows_m, Cg_follows_d, Bool.false_eq_true, ↓reduceIte,
    Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_neg_iff, Formula.satisfies_forall_iff, Formula.satisfies_isRestriction_iff I,
    rd_entry0_sat_l hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest] <;> rfl

def cg_win_m (p : Bool) {d} (ω X F J B W σ : Term d) : Formula 1 d :=
  .conj (fn0_m F X σ) (Formula.forallMem B (.imp
    (cg_follows_m p ω.weaken J.weaken σ.weaken .newest)
    (if p then .mem .newest W.weaken else .neg (.mem .newest W.weaken))))

@[simp] theorem cg_win_closed_l (p : Bool) {d} (ω X F J B W σ : Term d)
    (hw : ω.freeSupport = []) (hx : X.freeSupport = []) (hf : F.freeSupport = []) (hj : J.freeSupport = [])
    (hb : B.freeSupport = []) (ha : W.freeSupport = []) (hs : σ.freeSupport = []) :
    (cg_win_m p ω X F J B W σ).FreeClosed := by
  cases p <;> simp -implicitDefEqProofs [cg_win_m, Definitional.Formula.FreeClosed, hw, hx, hf, hj, hb, ha, hs]

theorem cg_win_sat_l (hE : Extensional M) (p : Bool) {d} (ρ : Env M d) (ω X F J B W σ : Term d) :
    Formula.satisfies ρ (cg_win_m p ω X F J B W σ) ↔ Cg_win_d I p
      (ω.eval ρ) (X.eval ρ) (F.eval ρ) (J.eval ρ) (B.eval ρ) (W.eval ρ) (σ.eval ρ) := by
  cases p <;> simp only [cg_win_m, Cg_win_d, Bool.false_eq_true, ↓reduceIte,
    Formula.satisfies_conj_iff, fn0_sat_l hE, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    cg_follows_sat_l I hE, Formula.satisfies_mem_iff, Formula.satisfies_neg_iff, Definitional.Term.eval_weaken] <;> rfl

end YesMetaZFC.SetTheory.Descriptive

/-! ## 固定局面之后的内部获胜策略

续局只约束包含给定历史的后续决策。策略仍在全部有限历史上有定义；
获胜局面由原公式分离得到，存在量词遍历模型自己的策略图。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Cg_tail_follows_d (p : Bool) (ω J s σ f : M.Domain) : Prop :=
  ∀ i, M.mem i ω → (if p then M.mem i J else ¬ M.mem i J) →
    ∀ h, M.IsRestrictionOf I h f i → M.MemberSubset s h →
      ∀ v, Rd_entry_d i v f → Rd_entry_d h v σ

def cg_tail_follows_m (p : Bool) {d} (ω J s σ f : Term d) : Formula 1 d :=
  Formula.forallMem ω (.imp (if p then .mem .newest J.weaken else .neg (.mem .newest J.weaken))
    (.forallE (.imp (Formula.isRestriction kpair_convention_l .newest f.weaken.weaken (.bound 1))
      (.imp (Formula.subset s.weaken.weaken .newest) (.forallE (.imp
        (rd_entry0_m (.bound 2) .newest f.weaken.weaken.weaken)
        (rd_entry0_m (.bound 1) .newest σ.weaken.weaken.weaken)))))))

@[simp] theorem cg_tail_follows_closed_l (p : Bool) {d} (ω J s σ f : Term d)
    (hw : ω.freeSupport = []) (hj : J.freeSupport = []) (hs : s.freeSupport = [])
    (hσ : σ.freeSupport = []) (hf : f.freeSupport = []) :
    (cg_tail_follows_m p ω J s σ f).FreeClosed := by
  cases p <;> simp -implicitDefEqProofs [cg_tail_follows_m, Definitional.Formula.FreeClosed, hw, hj, hs, hσ, hf]

theorem cg_tail_follows_sat_l (hE : Extensional M) (p : Bool) {d} (ρ : Env M d) (ω J s σ f : Term d) :
    Formula.satisfies ρ (cg_tail_follows_m p ω J s σ f) ↔ Cg_tail_follows_d I p
      (ω.eval ρ) (J.eval ρ) (s.eval ρ) (σ.eval ρ) (f.eval ρ) := by
  cases p <;> simp only [cg_tail_follows_m, Cg_tail_follows_d, Bool.false_eq_true, ↓reduceIte,
    Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_neg_iff, Formula.satisfies_forall_iff, Formula.satisfies_isRestriction_iff I,
    Formula.satisfies_subset_iff, rd_entry0_sat_l hE, Definitional.Term.eval_weaken,
    Definitional.Term.eval_newest] <;> rfl

def Cg_tail_win_d (p : Bool) (ω X F J B W s σ : M.Domain) : Prop := Fn0_d F X σ ∧
  ∀ f, M.mem f B → M.MemberSubset s f → Cg_tail_follows_d I p ω J s σ f →
    if p then M.mem f W else ¬ M.mem f W

def cg_tail_win_m (p : Bool) {d} (ω X F J B W s σ : Term d) : Formula 1 d :=
  .conj (fn0_m F X σ) (Formula.forallMem B (.imp (Formula.subset s.weaken .newest) (.imp
    (cg_tail_follows_m p ω.weaken J.weaken s.weaken σ.weaken .newest)
    (if p then .mem .newest W.weaken else .neg (.mem .newest W.weaken)))))

@[simp] theorem cg_tail_win_closed_l (p : Bool) {d} (ω X F J B W s σ : Term d)
    (hw : ω.freeSupport = []) (hx : X.freeSupport = []) (hf : F.freeSupport = []) (hj : J.freeSupport = [])
    (hb : B.freeSupport = []) (ha : W.freeSupport = []) (hs : s.freeSupport = []) (hσ : σ.freeSupport = []) :
    (cg_tail_win_m p ω X F J B W s σ).FreeClosed := by
  cases p <;> simp -implicitDefEqProofs [cg_tail_win_m, Definitional.Formula.FreeClosed, hw, hx, hf, hj, hb, ha, hs, hσ]

theorem cg_tail_win_sat_l (hE : Extensional M) (p : Bool) {d} (ρ : Env M d) (ω X F J B W s σ : Term d) :
    Formula.satisfies ρ (cg_tail_win_m p ω X F J B W s σ) ↔ Cg_tail_win_d I p
      (ω.eval ρ) (X.eval ρ) (F.eval ρ) (J.eval ρ) (B.eval ρ) (W.eval ρ) (s.eval ρ) (σ.eval ρ) := by
  cases p <;> simp only [cg_tail_win_m, Cg_tail_win_d, Bool.false_eq_true, ↓reduceIte,
    Formula.satisfies_conj_iff, fn0_sat_l hE, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_subset_iff, cg_tail_follows_sat_l I hE, Formula.satisfies_mem_iff,
    Formula.satisfies_neg_iff, Definitional.Term.eval_weaken] <;> rfl

theorem Cg_tail_win_d.root_l {p ω X F J B W e σ}
    (win : Cg_tail_win_d I p ω X F J B W e σ) (he : ∀ x, ¬ M.mem x e) : Cg_win_d I p ω X F J B W σ :=
  ⟨win.1, fun f hf follows => win.2 f hf (fun x hx => (he x hx).elim)
    (fun i hi turn h hr _ v hv => follows i hi turn h hr v hv)⟩

def Cg_ii_d (ω X F J B W Q : M.Domain) : Prop := ∀ s,
  M.mem s Q ↔ M.mem s F ∧ ∃ σ, Cg_tail_win_d I false ω X F J B W s σ

theorem cg_ii_l (hZF : M.Models ZF) (ω X F J B W : M.Domain) : ∃ Q, Cg_ii_d I ω X F J B W Q := by
  let ρ : Env M 6 := (((((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push X).push F).push J).push B).push W
  let φ : UnarySchema 6 := { body := .existsE (cg_tail_win_m false
      (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest) }
  obtain ⟨Q, sep⟩ := ZF.separation_exists_d hZF φ ρ F
  refine ⟨Q, fun s => (sep s).trans (and_congr Iff.rfl ?_)⟩
  simp only [φ, Formula.satisfies_exists_iff, cg_tail_win_sat_l I hZF.1]
  rfl

end YesMetaZFC.SetTheory.Descriptive

/-! ## 给定有限历史之后的实际策略对局

先复制指定前缀，之后在指定玩家的时刻调用原策略，其余时刻使用给定字母。
固定目标集的序数递归直接产生模型内部 ω 列；不需要选择公理或外部标准性。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem cg_tail_play_l {ι : Bool} {ω X F J σ n s a : M.Domain} (hω : M.IsOmega ω)
    (space : Fseq_space_d I ω X F) (strategy : Fn0_d F X σ)
    (hn : M.mem n ω) (fs : M.IsSetFunctionFromTo I s n X) (ha : M.mem a X) :
    ∃ f, M.IsSetFunctionFromTo I f ω X ∧ M.MemberSubset s f ∧ Cg_tail_follows_d I ι ω J s σ f := by
  classical
  let P i := if ι then ¬ M.mem i J else M.mem i J
  let opp {d} (i J : Term d) : Formula 1 d := if ι then .neg (.mem i J) else .mem i J
  have oppSat {d} (η : Env M d) (i J : Term d) : Formula.satisfies η (opp i J) ↔
      (if ι then ¬ M.mem (i.eval η) (J.eval η) else M.mem (i.eval η) (J.eval η)) := by
    cases ι <;> simp only [opp, Bool.false_eq_true, ↓reduceIte, Formula.satisfies_neg_iff, Formula.satisfies_mem_iff]
  let ρ : Env M 7 := ⟨fun i => [a, σ, J, s, n, X, ω].get i, fun _ => ω⟩
  let φ : BinarySchema 7 := {
    body := set[9] ⟪∃ i ∈ ⌜(.bound 8 : Term 9)⌝ₛ,
    ⌜fn0_m⌝ₚ(i, ⌜(.bound 7 : Term 9)⌝ₛ, ⌜(.bound 1 : Term 9)⌝ₛ) ∧
    ((i ∈ ⌜(.bound 6 : Term 9)⌝ₛ ∧ ⌜rd_entry0_m⌝ₚ(i, ⌜(.newest : Term 9)⌝ₛ, ⌜(.bound 5 : Term 9)⌝ₛ)) ∨
      (¬ (i ∈ ⌜(.bound 6 : Term 9)⌝ₛ) ∧
        ((¬ (⌜opp⌝ₚ(i, ⌜(.bound 4 : Term 9)⌝ₛ)) ∧
          ⌜rd_entry0_m⌝ₚ(⌜(.bound 1 : Term 9)⌝ₛ, ⌜(.newest : Term 9)⌝ₛ, ⌜(.bound 3 : Term 9)⌝ₛ)) ∨
          (⌜opp⌝ₚ(i, ⌜(.bound 4 : Term 9)⌝ₛ) ∧ ⌜(.newest : Term 9)⌝ₛ = ⌜(.bound 2 : Term 9)⌝ₛ))))⟫
    freeClosed := by cases ι <;> simp -implicitDefEqProofs [opp, Definitional.Formula.FreeClosed] }
  have sat g v : φ.denote ρ g v ↔ ∃ i, M.mem i ω ∧ Fn0_d i X g ∧
      ((M.mem i n ∧ Rd_entry_d i v s) ∨
        (¬ M.mem i n ∧ ((¬ P i ∧ Rd_entry_d g v σ) ∨ (P i ∧ v = a)))) := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      fn0_sat_l hZF.1, Formula.satisfies_disj_iff, Formula.satisfies_mem_iff, Formula.satisfies_neg_iff,
      rd_entry0_sat_l hZF.1, Formula.satisfies_extensionalEq_iff_eq hZF.1, oppSat, Definitional.Term.eval_weaken]
    rfl
  have function : M.IsClassFunctionOnSequencesInBelow I (φ.denote ρ) ω X := by
    rintro g ⟨_, i, hi, _, fg⟩
    have fg₀ := fn0_of_function_l (ZF.modelsKP hZF) fg
    have total : ∃ v, φ.denote ρ g v := by
      by_cases hin : M.mem i n
      · obtain ⟨v, _, hv⟩ := fs.2.2 i hin
        exact ⟨v, (sat g v).mpr ⟨i, hi, fg₀, Or.inl ⟨hin, hv⟩⟩⟩
      · by_cases hij : P i
        · exact ⟨a, (sat g a).mpr ⟨i, hi, fg₀, Or.inr ⟨hin, Or.inr ⟨hij, rfl⟩⟩⟩⟩
        · obtain ⟨v, _, hv⟩ := strategy.2.1 g ((space g).mpr ⟨i, hi, fg⟩)
          exact ⟨v, (sat g v).mpr ⟨i, hi, fg₀, Or.inr ⟨hin, Or.inl ⟨hij, hv⟩⟩⟩⟩
    obtain ⟨v, hv⟩ := total
    refine ⟨v, hv, fun w hw => ?_⟩
    obtain ⟨k, _, fk, hk⟩ := (sat g v).mp hv
    obtain ⟨l, _, fl, hl⟩ := (sat g w).mp hw
    have ek := fk.domain_eq_l hZF.1 fg₀
    have el := fl.domain_eq_l hZF.1 fg₀
    subst k l
    rcases hl with ⟨hin, hw⟩ | ⟨hn', ⟨hj', hw⟩ | ⟨hj', rfl⟩⟩
    · rcases hk with ⟨_, hv⟩ | ⟨bad, _⟩
      · exact fs.1.2 i w v hw hv
      · exact (bad hin).elim
    · rcases hk with ⟨hn, _⟩ | ⟨_, ⟨_, hv⟩ | ⟨hj, _⟩⟩
      · exact (hn' hn).elim
      · exact (fn0_function_l (ZF.modelsKP hZF) strategy).1.2 g w v hw hv
      · exact (hj' hj).elim
    · rcases hk with ⟨hn, _⟩ | ⟨_, ⟨hj, _⟩ | ⟨_, rfl⟩⟩
      · exact (hn' hn).elim
      · exact (hj hj').elim
      · rfl
  have into : M.MapsSequencesInBelowInto I (φ.denote ρ) ω X := by
    intro g v _ hv
    obtain ⟨i, _, _, ⟨_, hv⟩ | ⟨_, ⟨_, hv⟩ | ⟨_, rfl⟩⟩⟩ := (sat g v).mp hv
    · exact fs.output_mem_of_pairMember hv
    · exact (strategy.bound_l hv).2
    · exact ha
  obtain ⟨f, rec⟩ := ZF.recursiveSequenceIn_exists hZF I ρ φ
    (hω.isOrdinal (ZF.modelsKP hZF)) (hω.isOrdinal (ZF.modelsKP hZF)) (Or.inl rfl) function into
  have ff := rec.1.2
  have read i v (hi : M.mem i ω) (hv : Rd_entry_d i v f) : ∃ g, M.IsRestrictionOf I g f i ∧
      ((M.mem i n ∧ Rd_entry_d i v s) ∨
        (¬ M.mem i n ∧ ((¬ P i ∧ Rd_entry_d g v σ) ∨ (P i ∧ v = a)))) := by
    obtain ⟨g, hg, value⟩ := rec.2 i hi v hv
    obtain ⟨k, _, fk, hk⟩ := (sat g v).mp value
    have fi := fn0_of_function_l (ZF.modelsKP hZF) (hg.isSetFunctionFromTo ff (hω.transitive (ZF.modelsKP hZF) i hi))
    have eq := fk.domain_eq_l hZF.1 fi
    exact ⟨g, hg, eq ▸ hk⟩
  have sub : M.MemberSubset s f := by
    intro p hp
    obtain ⟨i, v, pair⟩ := fs.1.1 p hp
    have his : Rd_entry_d i v s := ⟨p, pair, hp⟩
    have hin := fs.input_mem_of_pairMember his
    obtain ⟨w, _, hiw⟩ := ff.2.2 i (hω.transitive (ZF.modelsKP hZF) n hn i hin)
    obtain ⟨_, _, ⟨_, hws⟩ | ⟨bad, _⟩⟩ := read i w (hω.transitive (ZF.modelsKP hZF) n hn i hin) hiw
    · have eq := fs.1.2 i w v hws his
      obtain ⟨q, qp, hq⟩ := eq ▸ hiw
      exact kpair_unique_l M hZF.1 qp pair ▸ hq
    · exact (bad hin).elim
  refine ⟨f, ff, sub, ?_⟩
  intro i hi turn h hr sh v hv
  obtain ⟨g, gr, ⟨hin, hsv⟩ | ⟨_, ⟨_, value⟩ | ⟨bad, _⟩⟩⟩ := read i v hi hv
  · have hhv : Rd_entry_d i v h := hsv.elim fun p hp => ⟨p, hp.1, sh p hp.2⟩
    exact (KP.mem_irrefl_d (ZF.modelsKP hZF) i ((hr.2 i v).mp hhv).1).elim
  · exact gr.eq hZF.1 hr ▸ value
  · have hn : ¬ P i := by cases ι <;> simpa [P] using turn
    exact (hn bad).elim

end YesMetaZFC.SetTheory.Descriptive

/-! ## 两条策略的实际对弈

按回合集 J 在两张策略图之间选择下一项。固定目标集的序数递归产生整个
内部 ω 对局，故不需要选择公理，也不要求 ω 外部标准。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem cg_battle_l {ω X F J σ τ : M.Domain} (hw : M.IsOmega ω)
    (space : Fseq_space_d I ω X F) (hs : Fn0_d F X σ) (ht : Fn0_d F X τ) :
    ∃ f, M.IsSetFunctionFromTo I f ω X ∧
      Cg_follows_d I true ω J σ f ∧ Cg_follows_d I false ω J τ f := by
  classical
  let ρ : Env M 5 := ⟨fun i => [τ, σ, J, X, ω].get i, fun _ => ω⟩
  let φ : BinarySchema 5 := {
    body := set[7] ⟪∃ i ∈ ⌜(.bound 6 : Term 7)⌝ₛ,
      ⌜fn0_m⌝ₚ(i, ⌜(.bound 5 : Term 7)⌝ₛ, ⌜(.bound 1 : Term 7)⌝ₛ) ∧
      ((i ∈ ⌜(.bound 4 : Term 7)⌝ₛ ∧
        ⌜rd_entry0_m⌝ₚ(⌜(.bound 1 : Term 7)⌝ₛ, ⌜(.newest : Term 7)⌝ₛ, ⌜(.bound 3 : Term 7)⌝ₛ)) ∨
       (¬ (i ∈ ⌜(.bound 4 : Term 7)⌝ₛ) ∧
        ⌜rd_entry0_m⌝ₚ(⌜(.bound 1 : Term 7)⌝ₛ, ⌜(.newest : Term 7)⌝ₛ, ⌜(.bound 2 : Term 7)⌝ₛ)))⟫ }
  have sat g v : φ.denote ρ g v ↔ ∃ i, M.mem i ω ∧ Fn0_d i X g ∧
      ((M.mem i J ∧ Rd_entry_d g v σ) ∨ (¬ M.mem i J ∧ Rd_entry_d g v τ)) := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      fn0_sat_l hZF.1, Formula.satisfies_disj_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_neg_iff, rd_entry0_sat_l hZF.1, Definitional.Term.eval_weaken]; rfl
  have function : M.IsClassFunctionOnSequencesInBelow I (φ.denote ρ) ω X := by
    rintro g ⟨_, i, hi, _, fg⟩
    have fg₀ := fn0_of_function_l (ZF.modelsKP hZF) fg
    have hg := (space g).mpr ⟨i, hi, fg⟩
    have total : ∃ v, φ.denote ρ g v := by
      by_cases turn : M.mem i J
      · obtain ⟨v, _, hv⟩ := hs.2.1 g hg
        exact ⟨v, (sat g v).mpr ⟨i, hi, fg₀, Or.inl ⟨turn, hv⟩⟩⟩
      · obtain ⟨v, _, hv⟩ := ht.2.1 g hg
        exact ⟨v, (sat g v).mpr ⟨i, hi, fg₀, Or.inr ⟨turn, hv⟩⟩⟩
    obtain ⟨v, hv⟩ := total
    refine ⟨v, hv, fun w hw => ?_⟩
    obtain ⟨k, _, fk, hk⟩ := (sat g v).mp hv
    obtain ⟨l, _, fl, hl⟩ := (sat g w).mp hw
    have ek := fk.domain_eq_l hZF.1 fg₀
    have el := fl.domain_eq_l hZF.1 fg₀
    subst k l
    rcases hl with ⟨turn, hw⟩ | ⟨turn, hw⟩ <;> rcases hk with ⟨own, hv⟩ | ⟨own, hv⟩
    · exact (fn0_function_l (ZF.modelsKP hZF) hs).1.2 g w v hw hv
    · exact (own turn).elim
    · exact (turn own).elim
    · exact (fn0_function_l (ZF.modelsKP hZF) ht).1.2 g w v hw hv
  have into : M.MapsSequencesInBelowInto I (φ.denote ρ) ω X := by
    intro g v _ hv
    obtain ⟨_, _, _, ⟨_, hv⟩ | ⟨_, hv⟩⟩ := (sat g v).mp hv
    · exact (hs.bound_l hv).2
    · exact (ht.bound_l hv).2
  obtain ⟨f, rec⟩ := ZF.recursiveSequenceIn_exists hZF I ρ φ
    (hw.isOrdinal (ZF.modelsKP hZF)) (hw.isOrdinal (ZF.modelsKP hZF)) (Or.inl rfl) function into
  have read i v (hi : M.mem i ω) (hv : Rd_entry_d i v f) : ∃ g, M.IsRestrictionOf I g f i ∧
      ((M.mem i J ∧ Rd_entry_d g v σ) ∨ (¬ M.mem i J ∧ Rd_entry_d g v τ)) := by
    obtain ⟨g, cut, step⟩ := rec.2 i hi v hv
    obtain ⟨k, _, fk, step⟩ := (sat g v).mp step
    have eq := fk.domain_eq_l hZF.1 (fn0_of_function_l (ZF.modelsKP hZF)
      (cut.isSetFunctionFromTo rec.1.2 (hw.transitive (ZF.modelsKP hZF) i hi)))
    exact ⟨g, cut, eq ▸ step⟩
  refine ⟨f, rec.1.2, ?_, ?_⟩
  · intro i hi turn h cut v hv
    obtain ⟨g, cut', ⟨_, value⟩ | ⟨bad, _⟩⟩ := read i v hi hv
    · exact cut'.eq hZF.1 cut ▸ value
    · exact (bad turn).elim
  · intro i hi turn h cut v hv
    obtain ⟨g, cut', ⟨bad, _⟩ | ⟨_, value⟩⟩ := read i v hi hv
    · exact (turn bad).elim
    · exact cut'.eq hZF.1 cut ▸ value

/-- 同一无限图的相邻限制恰为一次实际末项追加。 -/
theorem ds_cut_end_l {ω V h n m s t z : M.Domain} (hw : M.IsOmega ω)
    (hf : M.IsSetFunctionFromTo I h ω V) (hn : M.mem n ω) (succ : M.SuccessorOf m n)
    (left : M.IsRestrictionOf I s h n) (right : M.IsRestrictionOf I t h m)
    (point : Rd_entry_d n z h) : Fseq_end_d I ω t s z := by
  have fs := left.isSetFunctionFromTo hf (hw.transitive (ZF.modelsKP hZF) n hn)
  obtain ⟨m',u,_,fu,ends⟩ := ZF.fseq_end_exists_l I hZF hw hn fs (hf.output_mem_of_pairMember point)
  have data := ends
  obtain ⟨a,b,d⟩ := data
  have eqb := d.prefix_sequence.2.2.2.eq hZF.1 fs.2.1
  have eqa := d.source.2.2.2.eq hZF.1 fu.2.1
  subst b a
  have eq := d.length_successor.eq hZF.1 succ
  subst m'
  have sub := (ds_restrict_iff_l I fs hf.1).mp left
  have sub' := ds_append_sub_l I hZF.1 fs ends sub point
  have rest := (ds_restrict_iff_l I fu hf.1).mpr sub'
  exact rest.eq hZF.1 right ▸ ends

end YesMetaZFC.SetTheory.Descriptive

/-! ## 按第一步落子拼接实际策略

K 给每个字母指定一个策略图。在尚无第 n 项的历史上取 a，
已有第 n 项时转交给 K 指定的策略。这里只用 ZF 的函数图替换。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Cg_splice_d (n a K h v : M.Domain) : Prop :=
  ((¬ ∃ x, Rd_entry_d n x h) ∧ v = a) ∨
    ∃ x σ, Rd_entry_d n x h ∧ Rd_entry_d x σ K ∧ Rd_entry_d h v σ

def cg_splice_m {d} (n a K h v : Term d) : Formula 1 d := set[d] ⟪
  (¬ (∃ x, ⌜rd_entry0_m⌝ₚ(⌜n⌝ₛ, x, ⌜h⌝ₛ)) ∧ ⌜v⌝ₛ = ⌜a⌝ₛ) ∨
  (∃ x, ∃ σ, ⌜rd_entry0_m⌝ₚ(⌜n⌝ₛ, x, ⌜h⌝ₛ) ∧
    ⌜rd_entry0_m⌝ₚ(x, σ, ⌜K⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜h⌝ₛ, ⌜v⌝ₛ, σ))⟫
derive_free_closed cg_splice_m

theorem cg_splice_sat_l (hE : Extensional M) {d} (ρ : Env M d) (n a K h v : Term d) :
    Formula.satisfies ρ (cg_splice_m n a K h v) ↔
      Cg_splice_d (n.eval ρ) (a.eval ρ) (K.eval ρ) (h.eval ρ) (v.eval ρ) := by
  simp only [cg_splice_m, Cg_splice_d, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_neg_iff, Formula.satisfies_exists_iff, rd_entry0_sat_l hE,
    Formula.satisfies_extensionalEq_iff_eq hE, Definitional.Term.eval_weaken]
  rfl

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem cg_splice_l {ω X F Z n a K : M.Domain} (space : Fseq_space_d I ω X F)
    (strategies : M.IsFunctionSpace I Z F X) (ha : M.mem a X) (table : M.IsSetFunctionFromTo I K X Z) :
    ∃ σ, M.IsSetFunctionFromTo I σ F X ∧
      ∀ h v, Rd_entry_d h v σ ↔ M.mem h F ∧ Cg_splice_d n a K h v := by
  classical
  let ρ : Env M 3 := ((⟨fun _ => n, fun _ => n⟩ : Env M 1).push a).push K
  let φ : BinarySchema 3 := { body := cg_splice_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have sat h v : φ.denote ρ h v ↔ Cg_splice_d n a K h v := cg_splice_sat_l hZF.1 _ _ _ _ _ _
  have total h (hh : M.mem h F) : ∃ v, Cg_splice_d n a K h v := by
    by_cases read : ∃ x, Rd_entry_d n x h
    · obtain ⟨x, hx⟩ := read
      obtain ⟨_, _, fn⟩ := (space h).mp hh
      obtain ⟨τ, hτ, ht⟩ := table.2.2 x (fn.output_mem_of_pairMember hx)
      obtain ⟨v, _, hv⟩ := ((strategies τ).mp hτ).2.2 h hh
      exact ⟨v, Or.inr ⟨x, τ, hx, ht, hv⟩⟩
    · exact ⟨a, Or.inl ⟨read, rfl⟩⟩
  have unique h (hh : M.mem h F) v w (hv : Cg_splice_d n a K h v) (hw : Cg_splice_d n a K h w) : v = w := by
    rcases hv with ⟨no, rfl⟩ | ⟨x, σ, hx, hσ, hv⟩
    · exact hw.elim (fun h => h.2.symm) (fun ⟨x, _, hx, _⟩ => (no ⟨x, hx⟩).elim)
    · rcases hw with ⟨no, _⟩ | ⟨y, τ, hy, hτ, hw⟩
      · exact (no ⟨x, hx⟩).elim
      · obtain ⟨_, _, fn⟩ := (space h).mp hh
        have e := fn.1.2 n x y hx hy
        subst y
        have e := table.1.2 x σ τ hσ hτ
        subst τ
        exact ((strategies σ).mp (table.output_mem_of_pairMember hσ)).1.2 h v w hv hw
  obtain ⟨σ, fn, read⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ
    (fun h hh => (total h hh).imp fun v hv => (sat h v).mpr hv)
    (fun h hh v w hv hw => unique h hh v w ((sat h v).mp hv) ((sat h w).mp hw)) (by
      intro h v _ hv
      rcases (sat h v).mp hv with ⟨_, rfl⟩ | ⟨_, τ, _, hτ, hv⟩
      · exact ha
      · exact ((strategies τ).mp (table.output_mem_of_pairMember hτ)).output_mem_of_pairMember hv)
  exact ⟨σ, fn, fun h v => (read h v).trans (and_congr Iff.rfl (sat h v))⟩

end YesMetaZFC.SetTheory.Descriptive

/-! ## 一轮之后的获胜策略拼接

玩家 I 落子时同时接好全部分支；玩家 II 落子时先走选定字母。
同一个拼接图处理这两种情形，因而不需要超限指定获胜等级。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem cg_glue_l {ω X F J B W Z s n a K : M.Domain} (hω : M.IsOmega ω)
    (space : Fseq_space_d I ω X F) (runs : M.IsFunctionSpace I B ω X)
    (strategies : M.IsFunctionSpace I Z F X) (hn : M.mem n ω)
    (hs : M.IsSetFunctionFromTo I s n X) (ha : M.mem a X) (table : M.IsSetFunctionFromTo I K X Z)
    (wins : ∀ x, M.mem x X → (¬ M.mem n J → x = a) → ∀ τ, Rd_entry_d x τ K →
      ∀ t, Fseq_end_d I ω t s x → Cg_tail_win_d I false ω X F J B W t τ) :
    ∃ σ, Cg_tail_win_d I false ω X F J B W s σ := by
  obtain ⟨σ, fn, read⟩ := cg_splice_l hZF space strategies ha table
  refine ⟨σ, fn0_of_function_l (ZF.modelsKP hZF) fn, fun f hf sf follows => ?_⟩
  have ff := (runs f).mp hf
  obtain ⟨x, hx, hfx⟩ := ff.2.2 n hn
  have head : ¬ M.mem n J → x = a := by
    intro turn
    have play := follows n hn turn s ((ds_restrict_iff_l I hs ff.1).mpr sf) (fun _ h => h) x hfx
    rcases ((read s x).mp play).2 with ⟨_, eq⟩ | ⟨v, _, hv, _⟩
    · exact eq
    · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) n (hs.input_mem_of_pairMember hv)).elim
  obtain ⟨τ, _, hτ⟩ := table.2.2 x hx
  obtain ⟨m, t, hm, ft, endt⟩ := ZF.fseq_end_exists_l I hZF hω hn hs hx
  have tf := ds_append_sub_l I hZF.1 hs endt sf hfx
  have tail := wins x hx head τ hτ t endt
  refine tail.2 f hf tf (fun i hi turn h hr th v hv => ?_)
  obtain ⟨j, k, next⟩ := endt
  have kn := next.prefix_sequence.2.2.2.eq hZF.1 hs.2.1
  subst k
  have st := (ds_restrict_iff_l I hs ft.1).mp next.prefix_restriction
  have hnx : Rd_entry_d n x h := next.last_value.elim fun p hp => ⟨p, hp.1, th p hp.2⟩
  have play := follows i hi turn h hr (fun p hp => th p (st p hp)) v hv
  rcases ((read h v).mp play).2 with ⟨no, _⟩ | ⟨y, υ, hny, hυ, move⟩
  · exact (no ⟨x, hnx⟩).elim
  · have fh := hr.isSetFunctionFromTo ff (hω.transitive (ZF.modelsKP hZF) i hi)
    have eq := fh.1.2 n x y hnx hny
    subst y
    have eq := table.1.2 x τ υ hτ hυ
    exact eq.symm ▸ move

end YesMetaZFC.SetTheory.Descriptive

/-! ## 玩家 II 获胜局面的闭包性质

所有后继均可获胜时，模型内选择给出各后继的策略，再按首项拼接。
轮到 II 时，一个可获胜后继已经足够。两种闭包均用于同一实际局面集合。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

section Choice
variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem cg_ii_all_l {ω X F J B W Z Q s n a : M.Domain} (hω : M.IsOmega ω)
    (space : Fseq_space_d I ω X F) (runs : M.IsFunctionSpace I B ω X)
    (strategies : M.IsFunctionSpace I Z F X) (positions : Cg_ii_d I ω X F J B W Q)
    (hn : M.mem n ω) (hs : M.IsSetFunctionFromTo I s n X) (ha : M.mem a X)
    (all : ∀ x, M.mem x X → ∀ t, Fseq_end_d I ω t s x → M.mem t Q) : M.mem s Q := by
  let ρ : Env M 7 := ((((((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push X).push F).push J).push B).push W).push s
  let φ : BinarySchema 7 := { body := .existsE (.conj
      (fseq_end_m (𝒞 := kpair_convention_l) (.bound 9) .newest (.bound 3) (.bound 2))
      (cg_tail_win_m false (.bound 9) (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4) .newest (.bound 1))) }
  have sat x τ : φ.denote ρ x τ ↔ ∃ t, Fseq_end_d I ω t s x ∧ Cg_tail_win_d I false ω X F J B W t τ := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      fseq_end_sat_l I hZF.1, cg_tail_win_sat_l I hZF.1]
    rfl
  obtain ⟨K, table, read⟩ := ZFC.uniformize_formula_l I hZFC φ ρ (X := X) (Y := Z) (by
    intro x hx
    obtain ⟨_, t, _, _, endt⟩ := ZF.fseq_end_exists_l I hZF hω hn hs hx
    obtain ⟨_, τ, win⟩ := (positions t).mp (all x hx t endt)
    exact ⟨τ, (strategies τ).mpr (fn0_function_l (ZF.modelsKP hZF) win.1), (sat x τ).mpr ⟨t, endt, win⟩⟩)
  refine (positions s).mpr ⟨(space s).mpr ⟨n, hn, hs⟩, ?_⟩
  apply cg_glue_l hZF hω space runs strategies hn hs ha table
  intro x _ _ τ hτ t endt
  obtain ⟨u, endu, win⟩ := (sat x τ).mp (read x τ hτ)
  exact fseq_end_rebuild_l I hZF.1 endu endt ▸ win

end Choice

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem cg_ii_some_l {ω X F J B W Z Q s n a t : M.Domain} (hω : M.IsOmega ω)
    (space : Fseq_space_d I ω X F) (runs : M.IsFunctionSpace I B ω X)
    (strategies : M.IsFunctionSpace I Z F X) (positions : Cg_ii_d I ω X F J B W Q)
    (hn : M.mem n ω) (hs : M.IsSetFunctionFromTo I s n X) (ha : M.mem a X)
    (turn : ¬ M.mem n J) (endt : Fseq_end_d I ω t s a) (ht : M.mem t Q) : M.mem s Q := by
  obtain ⟨_, τ, win⟩ := (positions t).mp ht
  obtain ⟨K, table, read⟩ := ZF.exists_constantFunction hZF I (source := X)
    ((strategies τ).mpr (fn0_function_l (ZF.modelsKP hZF) win.1))
  refine (positions s).mpr ⟨(space s).mpr ⟨n, hn, hs⟩, ?_⟩
  apply cg_glue_l hZF hω space runs strategies hn hs ha table
  intro x _ head υ hυ u endu
  have eq := head turn
  subst x
  have eq := table.1.2 a τ υ ((read a τ).mpr ⟨ha, rfl⟩) hυ
  subst υ
  exact fseq_end_rebuild_l I hZF.1 endt endu ▸ win

/-- 不在收益树中的有限证据使 II 立即获胜；常值图就是所需的真实策略。 -/
theorem cg_ii_bad_l {ω X F J B W Q T s a : M.Domain} (positions : Cg_ii_d I ω X F J B W Q)
    (body : Body_d F B T W) (hs : M.mem s F) (bad : ¬ M.mem s T) (ha : M.mem a X) : M.mem s Q := by
  obtain ⟨σ, fn, _⟩ := ZF.exists_constantFunction hZF I (source := F) ha
  exact (positions s).mpr ⟨hs, σ, fn0_of_function_l (ZF.modelsKP hZF) fn,
    fun f _ sf _ win => bad (((body f).mp win).2 s hs sf)⟩

end YesMetaZFC.SetTheory.Descriptive

/-! ## 避开玩家 II 获胜局面的策略

补集在 II 的走法下封闭；轮到 I 时至少有一个后继仍在补集中。
本层用选择公理把实际可走字母关系单值化为策略图。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Cg_avoid_d (ω X J Q s x : M.Domain) : Prop := ∀ n, Fn0_d n X s →
  M.mem n J → ¬ M.mem s Q → ∀ t, Fseq_end_d I ω t s x → ¬ M.mem t Q

def cg_avoid_m {d} (ω X J Q s x : Term d) : Formula 1 d := .forallE (.imp
  (fn0_m .newest X.weaken s.weaken) (.imp (.mem .newest J.weaken) (.imp (.neg (.mem s.weaken Q.weaken))
    (.forallE (.imp (fseq_end_m (𝒞 := kpair_convention_l) ω.weaken.weaken .newest s.weaken.weaken x.weaken.weaken)
      (.neg (.mem .newest Q.weaken.weaken)))))))
derive_free_closed cg_avoid_m

theorem cg_avoid_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω X J Q s x : Term d) :
    Formula.satisfies ρ (cg_avoid_m ω X J Q s x) ↔
      Cg_avoid_d I (ω.eval ρ) (X.eval ρ) (J.eval ρ) (Q.eval ρ) (s.eval ρ) (x.eval ρ) := by
  simp only [cg_avoid_m, Cg_avoid_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    fn0_sat_l hE, Formula.satisfies_mem_iff, Formula.satisfies_neg_iff,
    fseq_end_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "K" => kp_pair_l (ZF.modelsKP hZF)

theorem cg_avoid_l {ω X F J B W Z Q a : M.Domain} (hω : M.IsOmega ω)
    (space : Fseq_space_d K ω X F) (runs : M.IsFunctionSpace K B ω X)
    (strategies : M.IsFunctionSpace K Z F X) (positions : Cg_ii_d K ω X F J B W Q) (ha : M.mem a X) :
    ∃ σ, Fn0_d F X σ ∧ ∀ s x, Rd_entry_d s x σ → Cg_avoid_d K ω X J Q s x := by
  classical
  let ρ : Env M 4 := (((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push X).push J).push Q
  let φ : BinarySchema 4 := { body := cg_avoid_m (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have sat s x : φ.denote ρ s x ↔ Cg_avoid_d K ω X J Q s x := cg_avoid_sat_l K hZF.1 _ _ _ _ _ _ _
  obtain ⟨σ, fn, read⟩ := ZFC.uniformize_formula_l K hZFC φ ρ (X := F) (Y := X) (by
    intro s hsF
    obtain ⟨n, hn, hs⟩ := (space s).mp hsF
    by_cases outside : ¬ M.mem s Q
    · by_cases turn : M.mem n J
      · have good : ∃ x, M.mem x X ∧ ∀ t, Fseq_end_d K ω t s x → ¬ M.mem t Q := by
          apply Classical.byContradiction
          intro no
          apply outside (cg_ii_all_l hZFC hω space runs strategies positions hn hs ha ?_)
          intro x hx t endt
          apply Classical.byContradiction
          intro bad
          exact no ⟨x, hx, fun u endu hu => bad (fseq_end_rebuild_l K hZF.1 endu endt ▸ hu)⟩
        obtain ⟨x, hx, good⟩ := good
        exact ⟨x, hx, (sat s x).mpr (fun _ _ _ _ => good)⟩
      · refine ⟨a, ha, (sat s a).mpr (fun m hm hmJ _ => ?_)⟩
        have eq := hm.domain_eq_l hZF.1 (fn0_of_function_l (ZF.modelsKP hZF) hs)
        exact (turn (eq ▸ hmJ)).elim
    · exact ⟨a, ha, (sat s a).mpr (fun _ _ _ bad => (outside bad).elim)⟩)
  exact ⟨σ, fn0_of_function_l (ZF.modelsKP hZF) fn, fun s x hx => (sat s x).mp (read s x hx)⟩

end YesMetaZFC.SetTheory.Descriptive

/-! ## 避让策略的全部内部有限前缀

若一条服从策略的对局进入 II 获胜区，取模型内部最早进入的长度。
其前驱局面尚在补集中，两位玩家的闭包性质都排除这一步。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem cg_avoid_run_l {ω X F J B W Z Q e σ f : M.Domain} (hω : M.IsOmega ω)
    (space : Fseq_space_d I ω X F) (runs : M.IsFunctionSpace I B ω X)
    (strategies : M.IsFunctionSpace I Z F X) (positions : Cg_ii_d I ω X F J B W Q)
    (he : ∀ x, ¬ M.mem x e) (root : ¬ M.mem e Q)
    (avoid : ∀ s x, Rd_entry_d s x σ → Cg_avoid_d I ω X J Q s x)
    (hf : M.mem f B) (follows : Cg_follows_d I true ω J σ f) :
    ∀ s, M.mem s F → M.MemberSubset s f → ¬ M.mem s Q := by
  classical
  have ff := (runs f).mp hf
  let ρ : Env M 4 := (((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push X).push Q).push f
  let φ : UnarySchema 4 := { body := set[5] ⟪⌜(.newest : Term 5)⌝ₛ ∈ ⌜(.bound 4 : Term 5)⌝ₛ ∧
    (∃ t ∈ ⌜(.bound 2 : Term 5)⌝ₛ, ⌜fn0_m⌝ₚ(⌜(.newest : Term 5)⌝ₛ, ⌜(.bound 3 : Term 5)⌝ₛ, t) ∧
      t ⊆ ⌜(.bound 1 : Term 5)⌝ₛ)⟫ }
  have sat n : φ.denote ρ n ↔ M.mem n ω ∧ ∃ t, M.mem t Q ∧ Fn0_d n X t ∧ M.MemberSubset t f := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_existsMem_iff, fn0_sat_l hZF.1, Formula.satisfies_subset_iff, Definitional.Term.eval_weaken]
    rfl
  intro s hs sf hit
  obtain ⟨k, hk, fs⟩ := (space s).mp hs
  obtain ⟨n, no, hn, least⟩ := ZF.ordinal_min_l hZF φ ρ (hω.members_areOrdinals (ZF.modelsKP hZF) k hk)
    ((sat k).mpr ⟨hk, s, hit, fn0_of_function_l (ZF.modelsKP hZF) fs, sf⟩)
  obtain ⟨hn, t, ht, ft₀, tf⟩ := (sat n).mp hn
  have ft := fn0_function_l (ZF.modelsKP hZF) ft₀
  have nonempty : ∃ x, M.mem x n := by
    apply Classical.byContradiction
    intro empty
    have eq : t = e := hZF.1.eq_of_same_members t e (fun p => iff_of_false (fun hp => by
      obtain ⟨i, hi, _, _, _⟩ := ft₀.1 p hp
      exact empty ⟨i, hi⟩) (he p))
    exact root (eq ▸ ht)
  obtain ⟨i, hi, next⟩ := hω.exists_predecessor_of_mem_of_nonempty hZF hn nonempty
  obtain ⟨p, fp, pr, _⟩ := ds_prefix_l I hZF hω ff hi
  have pf := (ds_restrict_iff_l I fp ff.1).mp pr
  have outside : ¬ M.mem p Q := fun hp => least i next.predecessor_mem ((sat i).mpr
    ⟨hi, p, hp, fn0_of_function_l (ZF.modelsKP hZF) fp, pf⟩)
  have tr := (ds_restrict_iff_l I ft ff.1).mpr tf
  have pt := ds_prefix_mono_l I fp ft.1 pr tr (no.transitive i next.predecessor_mem)
  obtain ⟨x, hx, read⟩ := ff.2.2 i hi
  have endt : Fseq_end_d I ω t p x := ⟨n, i,
    ⟨⟨hn, no, ft.1, ft.2.1⟩, hi, next, ⟨hi, (hω.isOrdinal (ZF.modelsKP hZF)).mem hi, fp.1, fp.2.1⟩,
      (ds_restrict_iff_l I fp ft.1).mpr pt, (tr.2 i x).mpr ⟨next.predecessor_mem, read⟩⟩⟩
  by_cases turn : M.mem i J
  · exact avoid p x (follows i hi turn p pr x read) i
      (fn0_of_function_l (ZF.modelsKP hZF) fp) turn outside t endt ht
  · exact outside (cg_ii_some_l hZF hω space runs strategies positions hi fp hx turn endt ht)

end YesMetaZFC.SetTheory.Descriptive

/-! ## 集合字母表上的闭博弈决定性

Gale–Stewart 证明采用 Neeman 4.16 的获胜局面集合：空局面若属于 II
获胜区便已有策略；否则 I 避开该区，所有有限前缀因而都在收益树中。
时序 J 任意，允许同一玩家连续行动；全程使用模型内部历史、策略与对局。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Cg_det_d (ω X F J B W : M.Domain) : Prop :=
  (∃ σ, Cg_win_d I true ω X F J B W σ) ∨ ∃ τ, Cg_win_d I false ω X F J B W τ

def cg_det_m {d} (ω X F J B W : Term d) : Formula 1 d := .disj
  (.existsE (cg_win_m true ω.weaken X.weaken F.weaken J.weaken B.weaken W.weaken .newest))
  (.existsE (cg_win_m false ω.weaken X.weaken F.weaken J.weaken B.weaken W.weaken .newest))
derive_free_closed cg_det_m

theorem cg_det_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω X F J B W : Term d) :
    Formula.satisfies ρ (cg_det_m ω X F J B W) ↔ Cg_det_d I
      (ω.eval ρ) (X.eval ρ) (F.eval ρ) (J.eval ρ) (B.eval ρ) (W.eval ρ) := by
  simp only [cg_det_m, Cg_det_d, Formula.satisfies_disj_iff, Formula.satisfies_exists_iff,
    cg_win_sat_l I hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "K" => kp_pair_l (ZF.modelsKP hZF)

/-- 全部内部有限历史中的树体作为 I 收益时，至少一方有实际内部获胜策略。 -/
theorem cg_tree_det_l {ω X F J B W T a : M.Domain} (hω : M.IsOmega ω)
    (space : Fseq_space_d K ω X F) (runs : M.IsFunctionSpace K B ω X)
    (body : Body_d F B T W) (ha : M.mem a X) : Cg_det_d K ω X F J B W := by
  classical
  obtain ⟨Z, strategies⟩ := ZF.exists_functionSpace hZF K F X
  obtain ⟨Q, positions⟩ := cg_ii_l K hZF ω X F J B W
  obtain ⟨e, he, _⟩ := hω.1.1
  by_cases root : M.mem e Q
  · obtain ⟨_, σ, win⟩ := (positions e).mp root
    exact Or.inr ⟨σ, win.root_l K he⟩
  · obtain ⟨σ, fn, avoid⟩ := cg_avoid_l hZFC hω space runs strategies positions ha
    refine Or.inl ⟨σ, fn, fun f hf follows => (body f).mpr ⟨hf, fun s hs sf => ?_⟩⟩
    apply Classical.byContradiction
    intro bad
    exact cg_avoid_run_l hZF hω space runs strategies positions he root avoid hf follows s hs sf
      (cg_ii_bad_l hZF positions body hs bad ha)

/-- 相对补集开放的收益集合均决定；前缀树由闭集本身自动构造。 -/
theorem cg_closed_det_l {ω X F J B W O a : M.Domain} (hω : M.IsOmega ω)
    (space : Fseq_space_d K ω X F) (runs : M.IsFunctionSpace K B ω X) (ha : M.mem a X)
    (sub : M.MemberSubset W B) (complement : ∀ f, M.mem f O ↔ M.mem f B ∧ ¬ M.mem f W)
    (opened : Open_d F B O) : Cg_det_d K ω X F J B W := by
  obtain ⟨T, _, _, body⟩ := tree_of_closed_l (ZF.modelsKP hZF) sub complement opened
  exact cg_tree_det_l hZFC hω space runs body ha

end YesMetaZFC.SetTheory.Descriptive
