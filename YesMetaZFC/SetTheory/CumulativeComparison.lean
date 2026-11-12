import YesMetaZFC.SetTheory.CumulativeRelative
import YesMetaZFC.SetTheory.KP.TransitiveInduction

/-! # KP 中两份实际秩历史的比较

所有层值已经由给定历史提供。只在两份历史的实际值域中作有界成员归纳，
不要求全局累积层级存在，也不使用全幂集或替换模式。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hKP : M.Models KP)
local notation "I" => kp_pair_l hKP

theorem KP.v_compare_l {α β V W : M.Domain} (h : V_d I α V) (k : V_d I β W)
    (sub : M.MemberSubset α β) : M.MemberSubset V W ∧ (M.mem α β → M.mem V W) := by
  obtain ⟨B, F, left⟩ := vc_complete_l hKP h
  obtain ⟨C, G, right⟩ := vc_complete_l hKP k
  have f := (left V).2.1
  have g := (right W).2.1
  have eq_step {δ P Q : M.Domain} (da : M.MemberSubset δ α) (db : M.MemberSubset δ β)
      (p : ∀ t, Vc_step_d δ B F P t) (q : ∀ t, Vc_step_d δ C G Q t)
      (prev : ∀ ε, M.mem ε δ → ∀ A A', Rd_entry_d ε A F → Rd_entry_d ε A' G → A = A') : P = Q := by
    apply hKP.1.eq_of_same_members P Q
    intro t
    constructor
    · intro ht
      obtain ⟨ε, he, A, _, ha, ta⟩ := (p t).mp ht
      obtain ⟨A', ha', ea'⟩ := g.2.1 ε (db ε he)
      exact (q t).mpr ⟨ε, he, A', ha', ea', prev ε he A A' ha ea' ▸ ta⟩
    · intro ht
      obtain ⟨ε, he, A', _, ha', ta'⟩ := (q t).mp ht
      obtain ⟨A, ha, ea⟩ := f.2.1 ε (da ε he)
      exact (p t).mpr ⟨ε, he, A, ha, ea, (prev ε he A A' ea ha').symm ▸ ta'⟩
  let ρ : Env M 4 := ⟨Fin.cases B (Fin.cases C (Fin.cases F (fun _ => G))), fun _ => α⟩
  let φ : Delta0UnarySchema 4 := {
    body := Formula.forallMem (.bound 1) (Formula.forallMem (.bound 3) (.imp
      (rd_entry0_m (.bound 2) (.bound 1) (.bound 5)) (.imp
        (rd_entry0_m (.bound 2) .newest (.bound 6)) (Formula.extensionalEq (.bound 1) .newest))))
    delta0 := .forallMem _ (.forallMem _ (.imp (rd_entry0_delta_l ..) (.imp (rd_entry0_delta_l ..) (.atom ..)))) }
  have read δ : φ.toUnarySchema.denote ρ δ ↔ ∀ P, M.mem P B → ∀ Q, M.mem Q C →
      Rd_entry_d δ P F → Rd_entry_d δ Q G → P = Q := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
      rd_entry0_sat_l hKP.1, Formula.satisfies_extensionalEq_iff_eq hKP.1]; rfl
  have all := KP.transitive_induction_l hKP (v_ordinal_l I h).transitive φ ρ (by
    intro δ hδ ih
    apply (read δ).mpr
    intro P hP Q hQ eP eQ
    exact eq_step ((v_ordinal_l I h).transitive δ hδ)
      (fun ε he => sub ε ((v_ordinal_l I h).transitive δ hδ ε he))
      (fun t => (left t).2.2.1 δ hδ P hP eP)
      (fun t => (right t).2.2.1 δ (sub δ hδ) Q hQ eQ)
      (fun ε he A A' ea ea' => (read ε).mp (ih ε he) A (f.bound_l ea).2 A' (g.bound_l ea').2 ea ea'))
  have same δ (hδ : M.mem δ α) P Q (eP : Rd_entry_d δ P F) (eQ : Rd_entry_d δ Q G) : P = Q :=
    (read δ).mp (all δ hδ) P (f.bound_l eP).2 Q (g.bound_l eQ).2 eP eQ
  refine ⟨?_, ?_⟩
  · intro t ht
    obtain ⟨δ, hδ, P, _, eP, tp⟩ := (left t).2.2.2.mp ht
    obtain ⟨Q, hQ, eQ⟩ := g.2.1 δ (sub δ hδ)
    exact (right t).2.2.2.mpr ⟨δ, sub δ hδ, Q, hQ, eQ, same δ hδ P Q eP eQ ▸ tp⟩
  · intro ha
    obtain ⟨Q, hQ, eQ⟩ := g.2.1 α ha
    have eq := eq_step (fun _ h => h) sub (fun t => (left t).2.2.2)
      (fun t => (right t).2.2.1 α ha Q hQ eQ) same
    exact (right V).2.2.2.mpr ⟨α, ha, Q, hQ, eQ, fun t ht => eq ▸ ht⟩

/-- 用层值自身容纳历史值域；原函数图由较高极限层的关系闭包回收。 -/
theorem KP.v_history_inside_l {δ U α V : M.Domain} (upper : V_d I δ U) (limit : M.IsLimitOrdinal δ)
    (hα : M.mem α U) (hV : M.mem V U) (lower : V_d I α V) :
    ∃ F, M.mem F U ∧ ∀ t, Vc_d α V V F t := by
  obtain ⟨B, F, cert⟩ := vc_complete_l hKP lower
  have f := (cert V).2.1
  have range ε A (ea : Rd_entry_d ε A F) : M.mem A V :=
    (cert A).2.2.2.mpr ⟨ε, (f.bound_l ea).1, A, (f.bound_l ea).2, ea, fun _ h => h⟩
  have fv := f.retarget_l range
  obtain ⟨Z, hZ, az, vz⟩ := v_joint_bound_l I upper hα hV
  have hF := v_relation_mem_l I upper limit hZ (F := F) (fun p hp =>
    (fv.1 p hp).elim fun a ha => ha.2.elim fun b hb => ⟨a, az a ha.1, b, vz b hb.1, hb.2⟩)
  have step δ P (eqn : ∀ t, Vc_step_d δ B F P t) t : Vc_step_d δ V F P t :=
    (eqn t).trans ⟨fun ⟨ε, he, A, _, ea, ta⟩ => ⟨ε, he, A, range ε A ea, ea, ta⟩,
      fun ⟨ε, he, A, _, ea, ta⟩ => ⟨ε, he, A, (f.bound_l ea).2, ea, ta⟩⟩
  exact ⟨F, hF, fun t => ⟨(cert t).1, fv,
    fun ε he A _ ea => step ε A (fun s => (cert s).2.2.1 ε he A (f.bound_l ea).2 ea) t,
    step α V (fun s => (cert s).2.2.2) t⟩⟩

end YesMetaZFC.SetTheory
