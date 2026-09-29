import YesMetaZFC.Model.SetTheory.CountableSyntax
import YesMetaZFC.Model.FirstOrder.Substructure
import YesMetaZFC.Model.FirstOrder.Valuation
import YesMetaZFC.Model.SmallGraph.ZFC

/-! # 纯集合论结构的实际可数初等子模型

逐层枚举有限参数公式并加入存在见证。每层仍由自然数枚举，有限参数总落在同一层；
共同使用原 Tarski–Vaught 判据得到初等性。最后实例化原小图 ZFC 模型，并继承外部良基性。
-/

namespace YesMetaZFC.SetTheory
open Logic Logic.FirstOrder Automation.RelationalTranslation Automation.ModelClosure
universe u
variable (M : Logic.FirstOrder.Structure.{0,0,0,u} ℒ)

def values_enum_l (e : Nat → M.Carrier .set) : (ss : SortContext ℒ) → Nat → Values M.Carrier ss
  | [], _ => .nil
  | .set :: ss, n => .cons (e (NatPairing.first n)) (values_enum_l e ss (NatPairing.second n))

theorem values_hits_l (e : Nat → M.Carrier .set) {ss} (a : Assignment M ss)
    (ha : ∀ {s} (i : Variable ss s), ∃ n, e n = (by cases s; exact a i)) :
    ∃ n, values_enum_l M e ss n = valuesOfAssignment a := by
  induction ss with
  | nil => exact ⟨0, rfl⟩
  | cons s ss ih =>
    cases s
    obtain ⟨i, hi⟩ := ha .here
    obtain ⟨j, hj⟩ := ih (fun k => a (.there k)) (fun k => ha (.there k))
    exact ⟨NatPairing.pair i j, by simp only [values_enum_l, NatPairing.first_pair, NatPairing.second_pair,
      valuesOfAssignment, hi, hj]⟩

def env_enum_l (e : Nat → M.Carrier .set) (b f : SortContext ℒ) (n : Nat) : Logic.FirstOrder.Env M b f where
  boundVal := valuesAssignment (values_enum_l M e b (NatPairing.first n))
  freeVal := valuesAssignment (values_enum_l M e f (NatPairing.second n))

def query_holds_l (q : Query_code_l) (e : Nat → M.Carrier .set) (a : M.Carrier .set) : Prop :=
  match q with
  | ⟨[], _, _, _⟩ => True
  | ⟨.set :: b, f, φ, n⟩ => Formula.satisfies ((env_enum_l M e b f n).pushBound a) φ

/-- 任意纯隶属结构都有实际可枚举的初等子结构。 -/
theorem countable_elementary_l : ∃ A : Substructure_m M, A.Elementary_m ∧
    ∃ e : Nat → A.structure_m.Carrier .set, Function.Surjective e := by
  classical
  obtain ⟨a₀⟩ := M.nonempty .set
  obtain ⟨q, hq⟩ := enum_exists_l query_coding_l ⟨[], [], .truth, 0⟩
  have hw (q : Query_code_l) (g : Nat → M.Carrier .set) :
      ∃ a, (∃ x, query_holds_l M q g x) → query_holds_l M q g a := by
    by_cases h : ∃ x, query_holds_l M q g x
    · obtain ⟨a, ha⟩ := h
      exact ⟨a, fun _ => ha⟩
    · exact ⟨a₀, fun h' => False.elim (h h')⟩
  obtain ⟨w, hw⟩ := Classical.axiomOfChoice (fun q => Classical.axiomOfChoice (hw q))
  let T : Nat → Nat → M.Carrier .set := Nat.rec (fun _ => a₀) (fun _ g n =>
    if NatPairing.first n = 0 then g (NatPairing.second n) else w (q (NatPairing.second n)) g)
  have old k n : T (k+1) (NatPairing.pair 0 n) = T k n := by
    simp only [T, NatPairing.first_pair, NatPairing.second_pair, ↓reduceIte]
  have fresh k n : T (k+1) (NatPairing.pair 1 n) = w (q n) (T k) := by
    simp only [T, NatPairing.first_pair, NatPairing.second_pair, Nat.one_ne_zero, ↓reduceIte]
  have lift {k l : Nat} (h : k ≤ l) {a} (ha : ∃ n, T k n = a) : ∃ n, T l n = a := by
    induction h with
    | refl => exact ha
    | @step l _ ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨NatPairing.pair 0 n, (old l n).trans hn⟩
  let A : Substructure_m M := {
    carrier := fun | .set, a => ∃ k n, T k n = a
    nonempty := fun | .set => ⟨a₀, 0, 0, rfl⟩
    closed := fun f => nomatch f }
  have stage {ss} (a : Assignment M ss) (ha : ∀ {s} (i : Variable ss s), A.carrier s (a i)) :
      ∃ k, ∀ {s} (i : Variable ss s), ∃ n, T k n = (by cases s; exact a i) := by
    induction ss with
    | nil => exact ⟨0, fun i => nomatch i⟩
    | cons s ss ih =>
      cases s
      obtain ⟨k, n, hn⟩ := ha .here
      obtain ⟨l, hl⟩ := ih (fun i => a (.there i)) (fun i => ha (.there i))
      refine ⟨max k l, fun i => ?_⟩
      cases i with
      | here => exact lift (Nat.le_max_left k l) ⟨n, hn⟩
      | there i => exact lift (Nat.le_max_right k l) (hl i)
  have hA : A.WitnessClosed_m := by
    intro b f s φ ρ hρ hex
    cases s
    obtain ⟨k, hk⟩ := stage ρ.boundVal hρ.1
    obtain ⟨l, hl⟩ := stage ρ.freeVal hρ.2
    let m := max k l
    obtain ⟨nb, hb⟩ := values_hits_l M (T m) ρ.boundVal (fun i => lift (Nat.le_max_left k l) (hk i))
    obtain ⟨nf, hf⟩ := values_hits_l M (T m) ρ.freeVal (fun i => lift (Nat.le_max_right k l) (hl i))
    let n := NatPairing.pair nb nf
    have henv : env_enum_l M (T m) b f n = ρ := by
      apply Logic.FirstOrder.Env.ext
      · intro s i
        simp only [env_enum_l, n, NatPairing.first_pair, hb, assignment_values]
      · intro s i
        simp only [env_enum_l, n, NatPairing.second_pair, hf, assignment_values]
    let c : Query_code_l := ⟨.set :: b, f, φ, n⟩
    obtain ⟨j, hj⟩ := hq c
    refine ⟨w c (T m), ⟨m+1, NatPairing.pair 1 j, (fresh m j).trans (congrArg (fun q => w q (T m)) hj)⟩, ?_⟩
    have h : ∃ x, query_holds_l M c (T m) x := by simpa only [query_holds_l, c, henv] using hex
    simpa only [query_holds_l, c, henv] using hw c (T m) h
  let e (n : Nat) : A.structure_m.Carrier .set :=
    ⟨T (NatPairing.first n) (NatPairing.second n), NatPairing.first n, NatPairing.second n, rfl⟩
  refine ⟨A, A.tarski_vaught_m.mpr hA, e, fun a => ?_⟩
  obtain ⟨k, n, hn⟩ := a.2
  exact ⟨NatPairing.pair k n, Subtype.ext (by simpa only [e, NatPairing.first_pair, NatPairing.second_pair] using hn)⟩

/-- 原小图 ZFC 模型的可数初等子模型，保留其外部良基性。 -/
theorem countable_ground_l : ∃ M : SetTheory.Structure.{1}, M.Models ZFC ∧
    _root_.WellFounded M.mem ∧ ∃ e : Nat → M.Domain, Function.Surjective e := by
  obtain ⟨A, hA, e, he⟩ := countable_elementary_l Model.SmallGraph.sg_model.{0}
  let M := Definitional.Project.FirstOrderSemantics.reduct A.structure_m
  have hM := Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureModel.project_models
    ((A.models_iff_m hA _).mpr Model.SmallGraph.sg_models_zfc)
  refine ⟨M, hM, ?_, e, he⟩
  exact InvImage.wf (fun x : A.structure_m.Carrier .set => x.1) Model.SmallGraph.SG_set.mem_wf

end YesMetaZFC.SetTheory
