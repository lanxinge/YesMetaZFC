import YesMetaZFC.SetTheory.LargeCardinal.ExtenderNormal
import YesMetaZFC.SetTheory.LargeCardinal.DerivedSeparation

/-! # 扩展器的标准坐标与临界点

有限坐标上的等号和序保持，临界点以下的种子给出主测度；含不小于临界点
坐标的种子给出非主测度。空支撑及小种子不被错误地要求非主。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Ea_test_d (p : Bool) (κ i r s : M.Domain) : Prop := ∃ x y, M.mem x κ ∧ M.mem y κ ∧
  Rd_entry_d i x s ∧ Rd_entry_d r y s ∧ if p then x = y else M.mem x y

def ea_test_m {d} (p : Bool) (κ i r s : Term d) : Formula 1 d := Formula.existsMem κ
  (Formula.existsMem κ.weaken (.conj (rd_entry0_m i.weaken.weaken (.bound 1) s.weaken.weaken)
    (.conj (rd_entry0_m r.weaken.weaken .newest s.weaken.weaken)
      (if p then Formula.extensionalEq (.bound 1) .newest else .mem (.bound 1) .newest))))
@[simp] theorem ea_test_closed_l {d} (p : Bool) (κ i r s : Term d)
    (hκ : κ.freeSupport = []) (hi : i.freeSupport = []) (hr : r.freeSupport = []) (hs : s.freeSupport = []) :
    (ea_test_m p κ i r s).FreeClosed := by
  cases p <;> simp -implicitDefEqProofs [ea_test_m, Definitional.Formula.FreeClosed, hκ, hi, hr, hs]
theorem ea_test_delta_l {d} (p : Bool) (κ i r s : Term d) : (ea_test_m p κ i r s).IsDelta0 := by
  cases p
  · exact .existsMem _ (.existsMem _ (.conj (rd_entry0_delta_l ..) (.conj (rd_entry0_delta_l ..) (.mem _ _))))
  · exact .existsMem _ (.existsMem _ (.conj (rd_entry0_delta_l ..) (.conj (rd_entry0_delta_l ..) (.atom _ _ _))))
theorem ea_test_sat_l (hE : Extensional M) {d} (ρ : Env M d) (p : Bool) (κ i r s : Term d) :
    Formula.satisfies ρ (ea_test_m p κ i r s) ↔ Ea_test_d p (κ.eval ρ) (i.eval ρ) (r.eval ρ) (s.eval ρ) := by
  cases p <;> simp only [ea_test_m, Ea_test_d, Bool.false_eq_true, ↓reduceIte,
    Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, rd_entry0_sat_l hE,
    Formula.satisfies_extensionalEq_iff_eq hE, Formula.satisfies_mem_iff, Definitional.Term.eval_weaken] <;>
    exact exists_congr fun x => ⟨fun ⟨hx, y, hy, hi, hr, ht⟩ => ⟨y, hx, hy, hi, hr, ht⟩,
      fun ⟨y, hx, hy, hi, hr, ht⟩ => ⟨hx, y, hy, hi, hr, ht⟩⟩

theorem ea_test_read_l (p : Bool) {n κ s i r x y : M.Domain} (hs : Fn0_d n κ s)
    (hi : Rd_entry_d i x s) (hr : Rd_entry_d r y s) : Ea_test_d p κ i r s ↔ if p then x = y else M.mem x y := by
  refine ⟨fun ⟨x', y', hx, hy, hi', hr', ht⟩ => ?_, fun ht => ⟨x, y, (hs.bound_l hi).2, (hs.bound_l hr).2, hi, hr, ht⟩⟩
  have ex := hs.2.2 i (hs.bound_l hi).1 x' hx x (hs.bound_l hi).2 hi' hi
  have ey := hs.2.2 r (hs.bound_l hr).1 y' hy y (hs.bound_l hr).2 hr' hr
  exact ex ▸ ey ▸ ht

def Ea_part_d (p : Bool) (ω κ L F : M.Domain) : Prop := ∀ n a U i r α β,
  M.mem n ω → Fn0_d n L a → Rd_entry_d a U F → Rd_entry_d i α a → Rd_entry_d r β a →
  ∃ T, (∀ s, M.mem s T ↔ Fn0_d n κ s ∧ Ea_test_d p κ i r s) ∧
    (M.mem T U ↔ if p then α = β else M.mem α β)

def Ea_atoms_d (ω κ L F : M.Domain) : Prop := ∀ p, Ea_part_d p ω κ L F

variable (hZF : M.Models ZF) {ω δ X C Y E j κ k L S F : M.Domain}
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable (hω : M.IsOmega ω) (hX : V_d (kp_pair_l (ZF.modelsKP hZF)) δ X) (hδ : M.IsLimitOrdinal δ)
  (h : Spred_emb_d (kp_pair_l (ZF.modelsKP hZF)) ω X C Y E j) (hY : M.TransitiveSet Y)
  (hc : Wd_crit_d (kp_pair_l (ZF.modelsKP hZF)) X j κ k)
include hZF hω hX hδ h hY hc

/-- 域小于临界点的 κ 值函数由 j 逐点固定。 -/
theorem ed_bounded_function_fixed_l {n f : M.Domain} (hn : M.mem n κ) (hf : Fn0_d n κ f) :
    Rd_entry_d f f j := by
  have ht := ZF.v_transitive_l I hZF hX
  have hj : M.IsSetFunctionFromTo I j X Y := by obtain ⟨_, _, _, _, _, _, hj⟩ := h; exact hj.1.1
  have hκk : M.MemberSubset κ k := fun x hx => (ed_member_l I hZF hω h ht hY (hc.fixed x hx) hc.image).mp hx
  have hfX := ZF.v_relation_mem_l I hZF hX hδ hc.source (F := f) (fun p hp => by
    obtain ⟨i, hi, x, hx, hp⟩ := hf.1 p hp
    exact ⟨i, hc.ordinal.transitive n hn i hi, x, hx, hp⟩)
  obtain ⟨f', _, hjf⟩ := hj.2.2 f hfX
  have hg := (spred_function_l I hZF hω h ht hY (hc.fixed n hn) hc.image hjf).mp hf
  have eq := (hf.mono_target_l hκk).ext_l hZF.1 hg fun i hi => by
    obtain ⟨x, hx, hix⟩ := hf.2.1 i hi
    exact ⟨x, hix, (spred_entry_l I hZF hω h ht hY (hc.fixed i (hc.ordinal.transitive n hn i hi)) (hc.fixed x hx) hjf).mp hix⟩
  exact eq.symm ▸ hjf

theorem es_atoms_l (hL : M.MemberSubset L k)
    (hSY : M.MemberSubset S Y) (hF : Es_family_d I j κ L S F) : Ea_atoms_d ω κ L F := by
  have ht := ZF.v_transitive_l I hZF hX
  have hj : M.IsSetFunctionFromTo I j X Y := by obtain ⟨_, _, _, _, _, _, hj⟩ := h; exact hj.1.1
  have hωκ := ed_critical_omega_l I hZF hω h ht hY hc
  intro p n a U i r α β hn ha haU hi hr
  obtain ⟨hs, m, D, hm, hD, hU⟩ := (hF.2.2 a U).mp haU
  have en := hm.domain_eq_l hZF.1 ha
  subst m
  have hnκ := hc.ordinal.transitive ω hωκ n hn
  have hDX := ZF.v_function_space_mem_l I hZF hX hδ hc.source (hc.ordinal.transitive n hnκ)
    (fun s => (hD s).trans ⟨fn0_function_l (ZF.modelsKP hZF), fn0_of_function_l (ZF.modelsKP hZF)⟩)
  obtain ⟨D', _, hjD⟩ := hj.2.2 D hDX
  have haD := es_seed_l I hZF hω h ht hY (hc.fixed n hnκ) hc.image hjD hD hL (hSY a hs) ha
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF D
  let φ : Delta0UnarySchema 3 := {
    body := ea_test_m p (.bound 3) (.bound 2) (.bound 1) .newest
    delta0 := ea_test_delta_l .. }
  obtain ⟨T, _, spec, read⟩ := ed_separate_delta_l I hZF hω h ht hY hP (ht P (ZF.v_power_mem_l I hZF hX hδ hDX hP))
    hjD haD hU φ ⟨Fin.cases r (Fin.cases i (fun _ => κ)), fun _ => n⟩
    ⟨Fin.cases r (Fin.cases i (fun _ => k)), fun _ => n⟩
    (Fin.cases (hc.fixed r (hc.ordinal.transitive n hnκ r (ha.bound_l hr).1))
      (Fin.cases (hc.fixed i (hc.ordinal.transitive n hnκ i (ha.bound_l hi).1)) (fun _ => hc.image)))
  simp only [φ, UnarySchema.denote, ea_test_sat_l hZF.1] at spec read
  exact ⟨T, fun s => (spec s).trans (and_congr_left fun _ => hD s),
    read.trans (ea_test_read_l p (ha.mono_target_l hL) hi hr)⟩

theorem es_principal_l (hF : Es_family_d I j κ L S F) {n a U : M.Domain}
    (hn : M.mem n κ) (ha : Fn0_d n κ a) (haU : Rd_entry_d a U F) :
    ∀ A, M.mem A U ↔ (∀ s, M.mem s A → Fn0_d n κ s) ∧ M.mem a A := by
  have ht := ZF.v_transitive_l I hZF hX
  have hj : M.IsSetFunctionFromTo I j X Y := by obtain ⟨_, _, _, _, _, _, hj⟩ := h; exact hj.1.1
  have fixed := ed_bounded_function_fixed_l hZF hω hX hδ h hY hc hn ha
  obtain ⟨_, m, D, hm, hD, hU⟩ := (hF.2.2 a U).mp haU
  have en := hm.domain_eq_l hZF.1 ha
  subst m
  intro A
  constructor
  · intro hA
    obtain ⟨sub, A', hjA, haA⟩ := (hU A).mp hA
    exact ⟨fun s hs => (hD s).mp (sub s hs), (ed_member_l I hZF hω h ht hY fixed hjA).mpr haA⟩
  · rintro ⟨sub, haA⟩
    have hDX := ZF.v_function_space_mem_l I hZF hX hδ hc.source (hc.ordinal.transitive n hn)
      (fun s => (hD s).trans ⟨fn0_function_l (ZF.modelsKP hZF), fn0_of_function_l (ZF.modelsKP hZF)⟩)
    obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF D
    have hAD : M.MemberSubset A D := fun s hs => (hD s).mpr (sub s hs)
    obtain ⟨A', _, hjA⟩ := hj.2.2 A (ht P (ZF.v_power_mem_l I hZF hX hδ hDX hP) A ((hP A).mpr hAD))
    exact (hU A).mpr ⟨hAD, A', hjA, (ed_member_l I hZF hω h ht hY fixed hjA).mp haA⟩

theorem es_nonprincipal_l (hF : Es_family_d I j κ L S F) {a U i α : M.Domain}
    (haU : Rd_entry_d a U F) (hiα : Rd_entry_d i α a) (hα : ¬ M.mem α κ)
    (hS : Fseq_space_d I ω L S) : Ed_nonprincipal_d U := by
  have ht := ZF.v_transitive_l I hZF hX
  have hωκ := ed_critical_omega_l I hZF hω h ht hY hc
  obtain ⟨haS, n, D, ha, hD, hU⟩ := (hF.2.2 a U).mp haU
  obtain ⟨m, hm, hma⟩ := (hS a).mp haS
  have en := ha.domain_eq_l hZF.1 (fn0_of_function_l (ZF.modelsKP hZF) hma)
  subst m
  intro s A hs hAU
  obtain ⟨sub, A', hjA, haA⟩ := (hU A).mp hAU
  have hsf := (hD s).mp (sub s ((hs s).mpr rfl))
  have fixed := ed_bounded_function_fixed_l hZF hω hX hδ h hY hc (hc.ordinal.transitive ω hωκ n hm) hsf
  have tr := spred_delta_l I hZF hω h ht hY (n := 2)
    (Formula.forallMem (.bound 1) (Formula.extensionalEq .newest (.bound 1)))
    (by simp) (.forallMem _ (.atom _ _ _))
    ⟨Fin.cases s (fun _ => A), fun _ => s⟩ ⟨Fin.cases s (fun _ => A'), fun _ => s⟩ (Fin.cases fixed (fun _ => hjA))
  simp only [Formula.satisfies_forallMem_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1] at tr
  have eq : a = s := tr.mp (fun x hx => (hs x).mp hx) a haA
  exact hα (hsf.bound_l (eq ▸ hiα)).2

end YesMetaZFC.SetTheory.LargeCardinal
