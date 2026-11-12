import YesMetaZFC.SetTheory.LargeCardinal.Extender.NormalSyntax
import YesMetaZFC.SetTheory.LargeCardinal.Cardinals.DerivedPredicate
import YesMetaZFC.SetTheory.LargeCardinal.Extender.Product
import YesMetaZFC.SetTheory.Descriptive.Coding.Prefix
import YesMetaZFC.SetTheory.OrdinalChoice
import YesMetaZFC.SetTheory.LargeCardinal.Cardinals.JointFiber

/-! # 派生有限支撑测度的正规性

若 f(s)<s(i) 在 U_a 上几乎处处成立，则 β=j(f)(a)<a(i)。把 β 添入支撑，
由 f 的图的初等性得到 f(s↾n)=s(n) 几乎处处成立。只使用 ZF。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Internal InnerModel
universe u
variable {M : Structure.{u}}

theorem es_normal_l (hZF : M.Models ZF) {ω δ X C Y E j κ k L S F : M.Domain}
    (hω : M.IsOmega ω) (hX : V_d (kp_pair_l (ZF.modelsKP hZF)) δ X) (hδ : M.IsLimitOrdinal δ)
    (h : Spred_emb_d (kp_pair_l (ZF.modelsKP hZF)) ω X C Y E j) (hY : M.TransitiveSet Y)
    (hc : Wd_crit_d (kp_pair_l (ZF.modelsKP hZF)) X j κ k) (hL : M.IsOrdinal L)
    (hLk : M.MemberSubset L k) (hS : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω L S)
    (hSY : M.MemberSubset S Y) (hF : Es_family_d (kp_pair_l (ZF.modelsKP hZF)) j κ L S F) :
    En_normal_d ω κ L F := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have ht := v_transitive_l I hX
  have hj : M.IsSetFunctionFromTo I j X Y := by obtain ⟨_, _, _, _, _, _, hj⟩ := h; exact hj.1.1
  have hωκ := ed_critical_omega_l I hZF hω h ht hY hc
  have small n (hn : M.mem n ω) := hc.ordinal.transitive ω hωκ n hn
  have space n D (hn : M.mem n ω) (hd : ∀ s, M.mem s D ↔ Fn0_d n κ s) : M.mem D X :=
    ZF.v_function_space_mem_l I hZF hX hδ hc.source (hc.ordinal.transitive n (small n hn))
      (fun s => (hd s).trans ⟨fn0_function_l (ZF.modelsKP hZF), fn0_of_function_l (ZF.modelsKP hZF)⟩)
  intro n a U D f i α A hn ha haU hD hf hiα hAU below
  obtain ⟨_, n', D₀, hn', hD₀, hu⟩ := (hF.2.2 a U).mp haU
  have en := hn'.domain_eq_l hZF.1 ha
  subst n'
  have eD := hZF.1.eq_of_same_members D₀ D (fun s => (hD₀ s).trans (hD s).symm)
  subst D₀
  obtain ⟨D', _, hjD⟩ := hj.2.2 D (space n D hn hD)
  obtain ⟨W, hWX, hDW, hκW⟩ := v_joint_bound_l I hX (space n D hn hD) hc.source
  have hfX := v_relation_mem_l I hX hδ hWX (F := f) (fun p hp => by
    obtain ⟨s, hs, x, hx, hp⟩ := hf.1 p hp
    exact ⟨s, hDW s hs, x, hκW x hx, hp⟩)
  obtain ⟨f', _, hjf⟩ := hj.2.2 f hfX
  have hff := (spred_function_l I hZF hω h ht hY hjD hc.image hjf).mp hf
  have haY := hSY a ((hF.2.2 a U).mp haU).1
  have haD := es_seed_l I hZF hω h ht hY (hc.fixed n (small n hn)) hc.image hjD hD hLk haY ha
  obtain ⟨β, hβk, haβ⟩ := hff.2.1 a haD
  obtain ⟨_, A', hjA, haA⟩ := (hu A).mp hAU
  let φ : Formula 1 4 := Formula.forallMem (.bound 3) (Formula.forallMem (.bound 3)
    (Formula.forallMem (.bound 4) (.imp (.conj (rd_entry0_m (.bound 2) (.bound 1) (.bound 4))
      (rd_entry0_m (.bound 3) .newest (.bound 2))) (.mem (.bound 1) .newest))))
  have tr := spred_delta_l I hZF hω h ht hY φ (by simp -implicitDefEqProofs [φ, Definitional.Formula.FreeClosed])
    (.forallMem _ (.forallMem _ (.forallMem _ (.imp (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..)) (.mem _ _)))))
    ⟨Fin.cases i (Fin.cases f (Fin.cases κ (fun _ => A))), fun _ => n⟩
    ⟨Fin.cases i (Fin.cases f' (Fin.cases k (fun _ => A'))), fun _ => n⟩
    (Fin.cases (hc.fixed i (hc.ordinal.transitive n (small n hn) i (ha.bound_l hiα).1))
      (Fin.cases hjf (Fin.cases hc.image (fun _ => hjA))))
  simp only [φ, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_conj_iff, rd_entry0_sat_l hZF.1, Formula.satisfies_mem_iff] at tr
  have hβα : M.mem β α := tr.mp (fun s hs x _ y _ hh => below s hs x y hh.1 hh.2)
    a haA β hβk α (hLk α (ha.bound_l hiα).2) ⟨haβ, hiα⟩
  obtain ⟨m, b, hm, hb, m', n', endb⟩ := ZF.fseq_end_exists_l I hZF hω hn
    (fn0_function_l (ZF.modelsKP hZF) ha) (hL.transitive α (ha.bound_l hiα).2 β hβα)
  have em := endb.source.2.2.2.eq hZF.1 hb.2.1
  subst m'
  have en := endb.prefix_sequence.2.2.2.eq hZF.1 (fn0_function_l (ZF.modelsKP hZF) ha).2.1
  subst n'
  have hab : M.MemberSubset a b := fun p hp => by
    obtain ⟨i, _, x, _, hpi⟩ := ha.1 p hp
    obtain ⟨q, hq, hqb⟩ := ((endb.prefix_restriction.2 i x).mp ⟨p, hpi, hp⟩).2
    exact (I.unique hpi hq) ▸ hqb
  obtain ⟨V, hbV⟩ := (hF.2.1 b).mp ((hS b).mpr ⟨m, hm, hb⟩)
  obtain ⟨_, m', H, hm', hH, hv⟩ := (hF.2.2 b V).mp hbV
  have em := hm'.domain_eq_l hZF.1 (fn0_of_function_l (ZF.modelsKP hZF) hb)
  subst m'
  obtain ⟨H', _, hjH⟩ := hj.2.2 H (space m H hm hH)
  let ρ : Env M 4 := ⟨Fin.cases f (Fin.cases A (Fin.cases κ (fun _ => n))), fun _ => n⟩
  let ψ : UnarySchema 4 := { body := en_graph_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨B, hs⟩ := ZF.separation_exists_d hZF ψ ρ H
  have spec s : M.mem s B ↔ M.mem s H ∧ En_graph_d n κ A f s :=
    (hs s).trans (and_congr_right fun _ => en_graph_sat_l hZF.1 _ _ _ _ _ _)
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF H
  have hBX := ht P (v_power_mem_l I hX hδ (space m H hm hH) hP) B
    ((hP B).mpr fun s hs => ((spec s).mp hs).1)
  obtain ⟨B', _, hjB⟩ := hj.2.2 B hBX
  let θ : Formula 1 6 := Formula.forallMem (.bound 5) (.iff (.mem .newest (.bound 5))
    (en_graph_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest))
  have transfer := spred_delta_l I hZF hω h ht hY θ (by simp -implicitDefEqProofs [θ, Definitional.Formula.FreeClosed])
    (.forallMem _ (.iff (.mem _ _) (en_graph_delta_l ..)))
    ⟨Fin.cases f (Fin.cases A (Fin.cases κ (Fin.cases n (Fin.cases B (fun _ => H))))), fun _ => n⟩
    ⟨Fin.cases f' (Fin.cases A' (Fin.cases k (Fin.cases n (Fin.cases B' (fun _ => H'))))), fun _ => n⟩
    (Fin.cases hjf (Fin.cases hjA (Fin.cases hc.image (Fin.cases (hc.fixed n (small n hn)) (Fin.cases hjB (fun _ => hjH))))))
  simp only [θ, Formula.satisfies_forallMem_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, en_graph_sat_l hZF.1] at transfer
  have hbH := es_seed_l I hZF hω h ht hY (hc.fixed m (small m hm)) hc.image hjH hH hLk
    (hSY b ((hS b).mpr ⟨m, hm, hb⟩)) (fn0_of_function_l (ZF.modelsKP hZF) hb)
  have hbB := (transfer.mp (fun s hs => (spec s).trans ⟨And.right, fun hh => ⟨hs, hh⟩⟩) b hbH).mpr
    ⟨a, haA, hab, β, hβk, haβ, endb.last_value⟩
  exact ⟨m, b, V, β, B, hm, endb.length_successor, fn0_of_function_l (ZF.modelsKP hZF) hb,
    hab, endb.last_value, hβα, hbV, (hv B).mpr ⟨fun s hs => ((spec s).mp hs).1, B', hjB, hbB⟩,
    fun s hs => ((spec s).mp hs).2⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 扩展器的标准坐标与临界点

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
  have ht := v_transitive_l I hX
  have hj : M.IsSetFunctionFromTo I j X Y := by obtain ⟨_, _, _, _, _, _, hj⟩ := h; exact hj.1.1
  have hκk : M.MemberSubset κ k := fun x hx => (ed_member_l I hZF hω h ht hY (hc.fixed x hx) hc.image).mp hx
  have hfX := v_relation_mem_l I hX hδ hc.source (F := f) (fun p hp => by
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
  have ht := v_transitive_l I hX
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
  obtain ⟨T, _, spec, read⟩ := ed_separate_delta_l I hZF hω h ht hY hP (ht P (v_power_mem_l I hX hδ hDX hP))
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
  have ht := v_transitive_l I hX
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
    obtain ⟨A', _, hjA⟩ := hj.2.2 A (ht P (v_power_mem_l I hX hδ hDX hP) A ((hP A).mpr hAD))
    exact (hU A).mpr ⟨hAD, A', hjA, (ed_member_l I hZF hω h ht hY fixed hjA).mp haA⟩

theorem es_nonprincipal_l (hF : Es_family_d I j κ L S F) {a U i α : M.Domain}
    (haU : Rd_entry_d a U F) (hiα : Rd_entry_d i α a) (hα : ¬ M.mem α κ)
    (hS : Fseq_space_d I ω L S) : Ed_nonprincipal_d U := by
  have ht := v_transitive_l I hX
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

/-! ## 有限列表示中的前缀投影与末项唯一性 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem ex_append_unique_l (hE : Extensional M) {n m κ s t u x : M.Domain}
    (hm : M.SuccessorOf m n) (hs : Fn0_d n κ s) (ht : Fn0_d m κ t) (hu : Fn0_d m κ u)
    (hst : M.MemberSubset s t) (hsu : M.MemberSubset s u) (hnt : Rd_entry_d n x t) (hnu : Rd_entry_d n x u) : t = u := by
  apply ht.ext_l hE hu
  intro i hi
  rcases (hm i).mp hi with hin | he
  · obtain ⟨y, _, hiy⟩ := hs.2.1 i hin
    exact ⟨y, hiy.elim fun p hp => ⟨p, hp.1, hst p hp.2⟩, hiy.elim fun p hp => ⟨p, hp.1, hsu p hp.2⟩⟩
  · have e := hE.eq_of_same_members i n he
    exact ⟨x, e ▸ hnt, e ▸ hnu⟩

theorem ex_prefix_cp_l (hE : Extensional M) {n m κ q s t : M.Domain}
    (hq : ∀ i j, Rd_entry_d i j q ↔ M.mem i n ∧ i = j) (hnm : M.MemberSubset n m)
    (ht : Fn0_d n κ t) : Cp0_d n m κ q s t ↔ M.MemberSubset t s := by
  constructor
  · intro h p hp
    obtain ⟨i, hi, x, hx, hc⟩ := ht.1 p hp
    obtain ⟨j, _, y, hy, hij, hjy, hiy⟩ := h.2 i hi
    have e := ((hq i j).mp hij).2
    subst j
    have ey := ht.2.2 i hi y hy x hx hiy ⟨p, hc, hp⟩
    obtain ⟨r, hr, hrs⟩ := (ey ▸ hjy : Rd_entry_d i x s)
    exact kpair_unique_l M hE hr hc ▸ hrs
  · intro sub
    refine ⟨ht, fun i hi => ?_⟩
    obtain ⟨x, hx, hix⟩ := ht.2.1 i hi
    exact ⟨i, hnm i hi, x, hx, (hq i i).mpr ⟨hi, rfl⟩,
      hix.elim (fun p hp => ⟨p, hp.1, sub p hp.2⟩), hix⟩

theorem ex_prefix_pull_l (hZF : M.Models ZF) {ω κ L F n m a b U V A : M.Domain}
    (hc : Es_coherent_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F)
    (hn : M.mem n ω) (hm : M.mem m ω) (hnm : M.MemberSubset n m)
    (ha : Fn0_d n L a) (hb : Fn0_d m L b) (hab : M.MemberSubset a b)
    (haU : Rd_entry_d a U F) (hbV : Rd_entry_d b V F) (hA : ∀ t, M.mem t A → Fn0_d n κ t) :
    ∃ Z, (∀ s, M.mem s Z ↔ Fn0_d m κ s ∧ ∃ t, M.mem t A ∧ M.MemberSubset t s) ∧
      (M.mem Z V ↔ M.mem A U) := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  let φ : BinarySchema 0 := { body := Formula.extensionalEq (.bound 1) .newest }
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => n⟩
  have sat i j : φ.denote ρ i j ↔ i = j := Formula.satisfies_extensionalEq_iff_eq hZF.1 _ _ _
  obtain ⟨q, hq, qs⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := n) (target := m)
    (fun i _ => ⟨i, (sat i i).mpr rfl⟩) (fun i _ j k hj hk => ((sat i j).mp hj).symm.trans ((sat i k).mp hk))
    (fun i j hi hij => (sat i j).mp hij ▸ hnm i hi)
  have spec i j : Rd_entry_d i j q ↔ M.mem i n ∧ i = j := (qs i j).trans (and_congr_right fun _ => sat i j)
  obtain ⟨Z, hz, hu⟩ := hc n m q b a U V A hn hm (fn0_of_function_l (ZF.modelsKP hZF) hq) hb
    ((ex_prefix_cp_l hZF.1 spec hnm ha).mpr hab) hbV haU hA
  exact ⟨Z, fun s => (hz s).trans (and_congr_right fun _ => exists_congr fun t =>
    and_congr_right fun ht => ex_prefix_cp_l hZF.1 spec hnm (hA t ht)), hu⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 有界投影的实际图条件

最后一项严格小于指定的旧坐标。保留任意指定坐标，第一坐标的通常定义为其实例。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Ex_bp_at_d (κ n i A s x : M.Domain) : Prop := M.mem x κ ∧ ∃ t, M.mem t A ∧ M.MemberSubset s t ∧
  Rd_entry_d n x t ∧ ∃ y, M.mem y κ ∧ Rd_entry_d i y s ∧ M.mem x y

def ex_bp_at_m {d} (κ n i A s x : Term d) : Formula 1 d := .conj (.mem x κ)
  (Formula.existsMem A (.conj (Formula.subset s.weaken .newest) (.conj
    (rd_entry0_m n.weaken x.weaken .newest) (Formula.existsMem κ.weaken
      (.conj (rd_entry0_m i.weaken.weaken .newest s.weaken.weaken) (.mem x.weaken.weaken .newest))))))
derive_free_closed ex_bp_at_m
theorem ex_bp_at_sat_l (hE : Extensional M) {d} (ρ : Env M d) (κ n i A s x : Term d) :
    Formula.satisfies ρ (ex_bp_at_m κ n i A s x) ↔
      Ex_bp_at_d (κ.eval ρ) (n.eval ρ) (i.eval ρ) (A.eval ρ) (s.eval ρ) (x.eval ρ) := by
  simp only [ex_bp_at_m, Ex_bp_at_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_existsMem_iff, Formula.satisfies_subset_iff, rd_entry0_sat_l hE, Definitional.Term.eval_weaken]; rfl

def Ex_bp_d (κ n i A B : M.Domain) : Prop := ∀ s, M.mem s B ↔ Fn0_d n κ s ∧ ∃ x, Ex_bp_at_d κ n i A s x

theorem ex_bp_exists_l (hZF : M.Models ZF) (κ n i A : M.Domain) : ∃ B, Ex_bp_d κ n i A B := by
  obtain ⟨D, hD⟩ := ZF.exists_functionSpace hZF (kp_pair_l (ZF.modelsKP hZF)) n κ
  let ρ := (((⟨fun _ => κ, fun _ => κ⟩ : Env M 1).push n).push i).push A
  let φ : UnarySchema 4 := { body := .existsE (ex_bp_at_m (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest) }
  obtain ⟨B, hb⟩ := ZF.separation_exists_d hZF φ ρ D
  refine ⟨B, fun s => (hb s).trans (and_congr ?_ ?_)⟩
  · exact (hD s).trans ⟨fn0_of_function_l (ZF.modelsKP hZF), fn0_function_l (ZF.modelsKP hZF)⟩
  · simp only [φ, Formula.satisfies_exists_iff, ex_bp_at_sat_l hZF.1]; rfl

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 正规性推出有界投影保持

正向在每个源纤维中取最小序数见证，再用正规性把见证变成新坐标。
反向使用坐标序的测度一集合和前缀协调律。统一化只需 ZF。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem ex_bp_select_l (hZF : M.Models ZF) {κ n i A B D : M.Domain}
    (hκ : M.IsOrdinal κ) (hne : ∃ z, M.mem z κ) (hB : Ex_bp_d κ n i A B) :
    ∃ f, Fn0_d D κ f ∧ ∀ s x, M.mem s B → Rd_entry_d s x f → Ex_bp_at_d κ n i A s x := by
  classical
  obtain ⟨z, hz⟩ := hne
  let ρ := (((((⟨fun _ => κ, fun _ => κ⟩ : Env M 1).push n).push i).push A).push B).push z
  let φ : BinarySchema 6 := {
    body := .disj (.conj (.mem (.bound 1) (.bound 3))
      (ex_bp_at_m (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 1) .newest))
      (.conj (.neg (.mem (.bound 1) (.bound 3))) (Formula.extensionalEq .newest (.bound 2))) }
  have sat s x : φ.denote ρ s x ↔ (M.mem s B ∧ Ex_bp_at_d κ n i A s x) ∨ (¬ M.mem s B ∧ x = z) := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_mem_iff, ex_bp_at_sat_l hZF.1, Formula.satisfies_neg_iff,
      Formula.satisfies_extensionalEq_iff_eq hZF.1]; rfl
  obtain ⟨f, hf, spec⟩ := ZF.ordinal_uniformize_l hZF φ ρ (D := D) hκ
    (fun s _ => by
      by_cases hs : M.mem s B
      · obtain ⟨x, hx⟩ := ((hB s).mp hs).2
        exact ⟨x, (sat s x).mpr (Or.inl ⟨hs, hx⟩)⟩
      · exact ⟨z, (sat s z).mpr (Or.inr ⟨hs, rfl⟩)⟩)
    (fun s x _ hx => ((sat s x).mp hx).elim (fun h => h.2.1) (fun h => h.2 ▸ hz))
  exact ⟨f, hf, fun s x hs hx => ((sat s x).mp (spec s x hx)).elim And.right (fun h => (h.1 hs).elim)⟩

theorem ex_bounded_projection_l (hZF : M.Models ZF) {ω κ L F S n m i A B A' B' : M.Domain}
    (hκ : M.IsOrdinal κ) (hne : ∃ z, M.mem z κ) (hF : Em_family_d ω κ L F)
    (hc : Es_coherent_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F)
    (normal : En_normal_d ω κ L F) (atoms : Ea_atoms_d ω κ L F)
    (hS : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω L S)
    (hn : M.mem n ω) (hm : M.mem m ω) (hsucc : M.SuccessorOf m n) (hi : M.mem i n)
    (hA : ∀ s, M.mem s A → Fn0_d m κ s) (hB : Ex_bp_d κ n i A B)
    (heA : Ex_value_d F S A A') (heB : Ex_value_d F S B B') : Ex_bp_d L n i A' B' := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have hBt s (hs : M.mem s B) := ((hB s).mp hs).1
  have hnm : M.MemberSubset n m := fun x hx => (hsucc x).mpr (Or.inl hx)
  intro a
  constructor
  · intro haB
    have ha := ex_value_type_l hZF.1 hF hBt heB a haB
    have haS := ((heB a).mp haB).1
    obtain ⟨U, haU⟩ := hF.total n a hn ha
    have hBU := (ex_value_at_l hZF.1 hF haS ha haU hBt heB).mp haB
    obtain ⟨r, D, _, hr, hD, _⟩ := hF.measure a U haU
    have er := hr.domain_eq_l hZF.1 ha
    subst r
    obtain ⟨f, hf, select⟩ := ex_bp_select_l hZF (D := D) hκ hne hB
    obtain ⟨α, hα, hiα⟩ := ha.2.1 i hi
    have below s (hs : M.mem s B) x y (hsx : Rd_entry_d s x f) (hiy : Rd_entry_d i y s) : M.mem x y := by
      obtain ⟨_, _, _, _, _, y', hy', hiy', hxy⟩ := select s x hs hsx
      exact (hBt s hs).2.2 i hi y' hy' y ((hBt s hs).bound_l hiy).2 hiy' hiy ▸ hxy
    obtain ⟨r, b, V, β, T, hr, hsn, hb, hab, hnβ, hβα, hbV, hTV, graph⟩ :=
      normal n a U D f i α B hn ha haU hD hf hiα hBU below
    have er := Structure.SuccessorOf.eq hZF.1 hsn hsucc
    subst r
    obtain ⟨r, D', _, hr, hD', hV⟩ := hF.measure b V hbV
    have er := hr.domain_eq_l hZF.1 hb
    subst r
    have sub : M.MemberSubset T A := by
      intro s hs
      obtain ⟨t, ht, hts, x, _, htx, hnx⟩ := graph s hs
      obtain ⟨_, u, huA, htu, hnu, _⟩ := select t x ht htx
      have eq := ex_append_unique_l hZF.1 hsucc (hBt t ht) ((hD' s).mp (hV.1.1 T hTV s hs))
        (hA u huA) hts htu hnx hnu
      exact eq.symm ▸ huA
    have hbA := (heA b).mpr ⟨(hS b).mpr ⟨m, hm, fn0_function_l (ZF.modelsKP hZF) hb⟩, V, T, hbV, hTV, sub⟩
    exact ⟨ha, β, (hb.bound_l hnβ).2, b, hbA, hab, hnβ, α, hα, hiα, hβα⟩
  · rintro ⟨ha, β, hβ, b, hbA, hab, hnβ, α, hα, hiα, hβα⟩
    have hb := ex_value_type_l hZF.1 hF hA heA b hbA
    have haS := (hS a).mpr ⟨n, hn, fn0_function_l (ZF.modelsKP hZF) ha⟩
    have hbS := ((heA b).mp hbA).1
    obtain ⟨U, haU⟩ := hF.total n a hn ha
    obtain ⟨V, hbV⟩ := hF.total m b hm hb
    have hAV := (ex_value_at_l hZF.1 hF hbS hb hbV hA heA).mp hbA
    have hbiα : Rd_entry_d i α b := hiα.elim fun p hp => ⟨p, hp.1, hab p hp.2⟩
    obtain ⟨T, hT, ht⟩ := atoms false m b V n i β α hm hb hbV hnβ hbiα
    have hTV : M.mem T V := ht.mpr hβα
    obtain ⟨Z, hz, hZV⟩ := ex_prefix_pull_l hZF hc hn hm hnm ha hb hab haU hbV hBt
    obtain ⟨r, D, _, hr, hD, hV⟩ := hF.measure b V hbV
    have er := hr.domain_eq_l hZF.1 hb
    subst r
    obtain ⟨G, hG, gA, gT⟩ := hV.1.2.2.2 A T hAV hTV
    have sub : M.MemberSubset G Z := by
      intro s hs
      have hsA := gA s hs
      have hsFn := hA s hsA
      obtain ⟨t, ht⟩ := ZF.exists_restriction hZF I s n
      have htf := ht.isSetFunctionFromTo (fn0_function_l (ZF.modelsKP hZF) hsFn) hnm
      have hts := (Descriptive.ds_restrict_iff_l I htf (fn0_function_l (ZF.modelsKP hZF) hsFn).1).mp ht
      obtain ⟨x, hx, hnx⟩ := hsFn.2.1 n hsucc.predecessor_mem
      obtain ⟨y, hy, hiy⟩ := htf.2.2 i hi
      have his := ((ht.2 i y).mp hiy).2
      have hxy := (ea_test_read_l false hsFn hnx his).mp (((hT s).mp (gT s hs)).2)
      have htB := (hB t).mpr ⟨fn0_of_function_l (ZF.modelsKP hZF) htf, x, hx, s, hsA, hts, hnx, y, hy, hiy, hxy⟩
      exact (hz s).mpr ⟨hsFn, t, htB, hts⟩
    have hZ := hV.1.2.2.1 G Z hG sub (fun s hs => (hD s).mpr (((hz s).mp hs).1))
    exact (ex_value_at_l hZF.1 hF haS ha haU hBt heB).mpr (hZV.mp hZ)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 测度族算子与嵌入限制的精确识别

对任意有限列集合 A，实际算子满足 E(A)=j(A)∩L^{<ω}，不限于同一长度。
这是标准短扩展器的有限列表示；未把原嵌入作为算子的定义参数。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Ex_derived_d (j S E : M.Domain) : Prop := ∀ A B, Rd_entry_d A B E →
  ∃ A', Rd_entry_d A A' j ∧ ∀ a, M.mem a B ↔ M.mem a S ∧ M.mem a A'

variable (hZF : M.Models ZF) {ω δ X C Y Q j κ k L S F : M.Domain}
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable (hω : M.IsOmega ω) (hX : V_d (kp_pair_l (ZF.modelsKP hZF)) δ X) (hδ : M.IsLimitOrdinal δ)
  (h : Spred_emb_d (kp_pair_l (ZF.modelsKP hZF)) ω X C Y Q j) (hY : M.TransitiveSet Y)
  (hc : Wd_crit_d (kp_pair_l (ZF.modelsKP hZF)) X j κ k) (hL : M.MemberSubset L k)
  (hS : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω L S) (hSY : M.MemberSubset S Y)
  (hF : Es_family_d (kp_pair_l (ZF.modelsKP hZF)) j κ L S F)
include hZF hω hX hδ h hY hc hL hS hSY hF

theorem ex_value_trace_l {A A' B : M.Domain} (hjA : Rd_entry_d A A' j) (he : Ex_value_d F S A B) :
    ∀ a, M.mem a B ↔ M.mem a S ∧ M.mem a A' := by
  have ht := v_transitive_l I hX
  have hj : M.IsSetFunctionFromTo I j X Y := by obtain ⟨_, _, _, _, _, _, hj⟩ := h; exact hj.1.1
  have hωκ := ed_critical_omega_l I hZF hω h ht hY hc
  intro a
  constructor
  · intro ha
    obtain ⟨haS, U, D, haU, hDU, hDA⟩ := (he a).mp ha
    obtain ⟨_, _, _, _, _, hu⟩ := (hF.2.2 a U).mp haU
    obtain ⟨_, D', hjD, haD⟩ := (hu D).mp hDU
    exact ⟨haS, (ed_subset_l I hZF hω h ht hY hjD hjA).mp hDA a haD⟩
  · rintro ⟨haS, haA⟩
    obtain ⟨n, hn, hna⟩ := (hS a).mp haS
    have ha := fn0_of_function_l (ZF.modelsKP hZF) hna
    obtain ⟨U, haU⟩ := (hF.2.1 a).mp haS
    obtain ⟨_, m, D, hm, hD, hU⟩ := (hF.2.2 a U).mp haU
    have en := hm.domain_eq_l hZF.1 ha
    subst m
    have hnκ := hc.ordinal.transitive ω hωκ n hn
    have hDX := ZF.v_function_space_mem_l I hZF hX hδ hc.source (hc.ordinal.transitive n hnκ)
      (fun s => (hD s).trans ⟨fn0_function_l (ZF.modelsKP hZF), fn0_of_function_l (ZF.modelsKP hZF)⟩)
    obtain ⟨D', _, hjD⟩ := hj.2.2 D hDX
    have haD := es_seed_l I hZF hω h ht hY (hc.fixed n hnκ) hc.image hjD hD hL (hSY a haS) ha
    obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF D
    let φ : Delta0UnarySchema 1 := { body := .mem .newest (.bound 1), delta0 := .mem _ _ }
    obtain ⟨T, _, spec, read⟩ := ed_separate_delta_l I hZF hω h ht hY hP (ht P (v_power_mem_l I hX hδ hDX hP))
      hjD haD hU φ ⟨fun _ => A, fun _ => A⟩ ⟨fun _ => A', fun _ => A'⟩ (fun _ => hjA)
    simp only [φ, UnarySchema.denote, Formula.satisfies_mem_iff] at spec read
    exact (he a).mpr ⟨haS, U, T, haU, read.mpr haA, fun s hs => ((spec s).mp hs).2⟩

/-- 整张幂集算子等于原嵌入在有限支撑空间上的限制。 -/
theorem ex_derived_l {K E : M.Domain} (hK : Fseq_space_d I ω κ K) (he : Ex_operator_d K S F E) :
    Ex_derived_d j S E := by
  have ht := v_transitive_l I hX
  have hj : M.IsSetFunctionFromTo I j X Y := by obtain ⟨_, _, _, _, _, _, hj⟩ := h; exact hj.1.1
  have hωκ := ed_critical_omega_l I hZF hω h ht hY hc
  have hKX := v_relations_mem_l I hX hδ hc.source (T := K) (fun f hf p hp => by
    obtain ⟨n, hn, hfn⟩ := (hK f).mp hf
    obtain ⟨i, hi, x, hx, hp⟩ := (fn0_of_function_l (ZF.modelsKP hZF) hfn).1 p hp
    exact ⟨i, hc.ordinal.transitive ω hωκ i (hω.transitive (ZF.modelsKP hZF) n hn i hi), x, hx, hp⟩)
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF K
  intro A B hab
  obtain ⟨sub, value⟩ := he.at_l hab
  obtain ⟨A', _, hjA⟩ := hj.2.2 A (ht P (v_power_mem_l I hX hδ hKX hP) A ((hP A).mpr sub))
  exact ⟨A', hjA, ex_value_trace_l hZF hω hX hδ h hY hc hL hS hSY hF hjA value⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 通用短扩展器的有限列接口

预扩展器由实际测度图及其代数、坐标、正规性和临界点性质刻画；可数共同
纤维另列为扩展器条件。全部后续运算读取 F，不以原嵌入为参数。
采用有限列表示，与 Neeman 的有限列集合算子约定相配。证书只依赖实际
配对解释；构造定理所需的集合论公理不写进证书类型。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

structure Ex_pre_d (I : kpair_convention_l.Interpretation M) (ω κ L F : M.Domain) : Prop where
  omega : M.IsOmega ω
  critical : M.IsCardinal I κ
  uncountable : M.mem ω κ
  length : M.IsOrdinal L
  above : M.mem κ L
  graph : M.IsSetFunction I F
  measures : Em_family_d ω κ L F
  coherent : Es_coherent_d I ω κ L F
  complete : ∀ n a U D, Fn0_d n L a → Rd_entry_d a U F →
    (∀ s, M.mem s D ↔ Fn0_d n κ s) → Ed_complete_d κ D U
  atoms : Ea_atoms_d ω κ L F
  normal : En_normal_d ω κ L F
  principal : ∀ n a U, M.mem n ω → Fn0_d n κ a → Rd_entry_d a U F →
    ∀ A, M.mem A U ↔ (∀ s, M.mem s A → Fn0_d n κ s) ∧ M.mem a A
  nonprincipal : ∀ a U i α, Rd_entry_d a U F → Rd_entry_d i α a → ¬ M.mem α κ → Ed_nonprincipal_d U

structure Ex_short_d (I : kpair_convention_l.Interpretation M) (ω κ L F : M.Domain) : Prop
    extends Ex_pre_d I ω κ L F where
  countable : ∀ H f, Ef_levels_d ω κ H →
    Es_fiber_d I ω L F H f → ∃ g, Ef_fiber_d ω κ H g

/-- 实际强嵌入生成全部预扩展器性质，特别是正规性和真正的临界基数。 -/
theorem es_pre_l (hZF : M.Models ZF) {ω δ X C Y E j κ k L S F : M.Domain}
    (hω : M.IsOmega ω) (hX : V_d (kp_pair_l (ZF.modelsKP hZF)) δ X) (hδ : M.IsLimitOrdinal δ)
    (h : Spred_emb_d (kp_pair_l (ZF.modelsKP hZF)) ω X C Y E j) (hY : M.TransitiveSet Y)
    (hc : Wd_crit_d (kp_pair_l (ZF.modelsKP hZF)) X j κ k) (hL : M.IsOrdinal L) (hκL : M.mem κ L)
    (hLk : M.MemberSubset L k) (hS : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω L S)
    (hSY : M.MemberSubset S Y) (hF : Es_family_d (kp_pair_l (ZF.modelsKP hZF)) j κ L S F) :
    Ex_pre_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have ht := v_transitive_l I hX
  have hωκ := ed_critical_omega_l I hZF hω h ht hY hc
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF κ
  obtain ⟨U, hU, hu, hn⟩ := ed_critical_measure_l I hZF hω h ht hY hc (hLk κ hκL) hP
    (v_power_mem_l I hX hδ hc.source hP)
  have hcard := ed_cardinal_l I hZF hc.ordinal hu hn
    (ed_complete_l I hZF hω h hY hX hδ hc hc.image (hLk κ hκL) hU)
  refine ⟨hω, hcard, hωκ, hL, hκL, hF.1, es_measures_l hZF hω hX hδ h hY hc hLk hS hSY hF,
    es_coherent_l I hZF hω hX hδ h hY hc hLk hSY hF, ?_,
    es_atoms_l hZF hω hX hδ h hY hc hLk hSY hF,
    es_normal_l hZF hω hX hδ h hY hc hL hLk hS hSY hF,
    fun n a U hn ha hu => es_principal_l hZF hω hX hδ h hY hc hF (hc.ordinal.transitive ω hωκ n hn) ha hu,
    fun a U i α hu hi hα => es_nonprincipal_l hZF hω hX hδ h hY hc hF hu hi hα hS⟩
  intro n a U D ha hu hd
  obtain ⟨m, D', hm, hD', _, _, complete⟩ := es_family_ultra_l I hZF hω hX hδ h hY hc hLk hS hSY hF hu
  have en := hm.domain_eq_l hZF.1 ha
  subst m
  exact hZF.1.eq_of_same_members D' D (fun s => (hD' s).trans (hd s).symm) ▸ complete

/-- 算子表述的可数完备性：像层有共同纤维，则原层也有共同纤维。 -/
theorem ex_countable_l (hZF : M.Models ZF) {ω κ L F K S E H f : M.Domain}
    (h : Ex_short_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F) (hS : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω L S)
    (he : Ex_operator_d K S F E) (hH : Ef_levels_d ω κ H)
    (hf : Ef_image_fiber_d (kp_pair_l (ZF.modelsKP hZF)) E ω L H f) : ∃ g, Ef_fiber_d ω κ H g := by
  apply h.countable H f hH
  refine ⟨hf.1, fun n hn => ?_⟩
  obtain ⟨A, B, a, hA, hab, haB, ha, sub⟩ := hf.2 n hn
  obtain ⟨U, haU⟩ := h.measures.total n a hn ha
  have haS := (hS a).mpr ⟨n, hn, fn0_function_l (ZF.modelsKP hZF) ha⟩
  exact ⟨A, a, U, hA, ha, sub, haU, (ex_value_at_l hZF.1 h.measures haS ha haU (hH.2 n A hA) (he.at_l hab).2).mp haB⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 扩展器性质的原一阶公式

全部量词绑定对象模型内的集合，有限长度可以非标准。各分量公式直接对应
预扩展器的数学条件；可数完备性以实际层族及共同纤维表达。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def em_family_m {d} (ω κ L F : Term d) : Formula 1 d :=
  (.conj (.forallE (.forallE (.imp (.mem (.bound 1) ω.weaken.weaken) (.imp (fn0_m (.bound 1) L.weaken.weaken
    .newest) (.existsE (rd_entry_m (.bound 1) .newest F.weaken.weaken.weaken)))))) (.conj (.forallE (.forallE
    (.forallE (.imp (rd_entry_m (.bound 2) (.bound 1) F.weaken.weaken.weaken) (.imp (rd_entry_m (.bound 2) .newest
    F.weaken.weaken.weaken) (Formula.extensionalEq (.bound 1) .newest)))))) (.forallE (.forallE (.imp (rd_entry_m
    (.bound 1) .newest F.weaken.weaken) (.existsE (.existsE (.conj (.mem (.bound 1) ω.weaken.weaken.weaken.weaken)
    (.conj (fn0_m (.bound 1) L.weaken.weaken.weaken.weaken (.bound 3)) (.conj (.forallE (.iff (.mem .newest
    (.bound 1)) (fn0_m (.bound 2) κ.weaken.weaken.weaken.weaken.weaken .newest))) (FilterZF.maximal_m .newest
    (.bound 2))))))))))))
derive_free_closed em_family_m

def en_normal_m {d} (ω κ L F : Term d) : Formula 1 d :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound 7)
    ω.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken) (.imp (fn0_m (.bound 7)
    L.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken (.bound 6)) (.imp (rd_entry_m (.bound 6) (.bound 5)
    F.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken) (.imp (.forallE (.iff (.mem .newest (.bound 5))
    (fn0_m (.bound 8) κ.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken .newest))) (.imp (fn0_m
    (.bound 4) κ.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken (.bound 3)) (.imp (rd_entry_m (.bound 2)
    (.bound 1) (.bound 6)) (.imp (.mem .newest (.bound 5)) (.imp (.forallE (.imp (.mem .newest (.bound 1)) (.forallE
    (.forallE (.imp (rd_entry_m (.bound 2) (.bound 1) (.bound 6)) (.imp (rd_entry_m (.bound 5) .newest (.bound 2))
    (.mem (.bound 1) .newest))))))) (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (.mem (.bound 4)
    ω.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken) (.conj
    (Formula.isSuccessor (.bound 4) (.bound 12)) (.conj (fn0_m (.bound 4)
    L.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken (.bound 3)) (.conj
    (Formula.subset (.bound 11) (.bound 3)) (.conj (rd_entry_m (.bound 12) (.bound 1) (.bound 3)) (.conj (.mem
    (.bound 1) (.bound 6)) (.conj (rd_entry_m (.bound 3) (.bound 2)
    F.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken) (.conj (.mem
    .newest (.bound 2)) (.forallE (.imp (.mem .newest (.bound 1)) (en_graph_m (.bound 13)
    κ.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken (.bound 6)
    (.bound 9) .newest))))))))))))))))))))))))))))))))
derive_free_closed en_normal_m

def ea_part_m {d} (p : Bool) (ω κ L F : Term d) : Formula 1 d :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound 6)
    ω.weaken.weaken.weaken.weaken.weaken.weaken.weaken) (.imp (fn0_m (.bound 6)
    L.weaken.weaken.weaken.weaken.weaken.weaken.weaken (.bound 5)) (.imp (rd_entry_m (.bound 5) (.bound 4)
    F.weaken.weaken.weaken.weaken.weaken.weaken.weaken) (.imp (rd_entry_m (.bound 3) (.bound 1) (.bound 5)) (.imp
    (rd_entry_m (.bound 2) .newest (.bound 5)) (.existsE (.conj (.forallE (.iff (.mem .newest (.bound 1)) (.conj
    (fn0_m (.bound 8) κ.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken .newest) (ea_test_m p
    κ.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken (.bound 5) (.bound 4) .newest)))) (.iff (.mem
    .newest (.bound 5)) (if p then (Formula.extensionalEq (.bound 2) (.bound 1)) else (.mem (.bound 2)
    (.bound 1))))))))))))))))))
@[simp] theorem ea_part_m_closed_l {d} (p : Bool) (ω κ L F : Term d)
    (hω : ω.freeSupport = []) (hκ : κ.freeSupport = []) (hL : L.freeSupport = []) (hF : F.freeSupport = []) : (ea_part_m p ω κ L F).FreeClosed := by
  cases p <;> simp -implicitDefEqProofs [ea_part_m, Definitional.Formula.FreeClosed, hω, hκ, hL, hF]

def ex_complete_m {d} (κ L F : Term d) : Formula 1 d :=
  (.forallE (.forallE (.forallE (.forallE (.imp (fn0_m (.bound 3) L.weaken.weaken.weaken.weaken (.bound 2)) (.imp
    (rd_entry_m (.bound 2) (.bound 1) F.weaken.weaken.weaken.weaken) (.imp (.forallE (.iff (.mem .newest (.bound 1))
    (fn0_m (.bound 4) κ.weaken.weaken.weaken.weaken.weaken .newest))) (ed_complete_m κ.weaken.weaken.weaken.weaken
    .newest (.bound 1)))))))))
derive_free_closed ex_complete_m

def ex_principal_m {d} (ω κ F : Term d) : Formula 1 d :=
  (.forallE (.forallE (.forallE (.imp (.mem (.bound 2) ω.weaken.weaken.weaken) (.imp (fn0_m (.bound 2)
    κ.weaken.weaken.weaken (.bound 1)) (.imp (rd_entry_m (.bound 1) .newest F.weaken.weaken.weaken) (.forallE (.iff
    (.mem .newest (.bound 1)) (.conj (.forallE (.imp (.mem .newest (.bound 1)) (fn0_m (.bound 4)
    κ.weaken.weaken.weaken.weaken.weaken .newest))) (.mem (.bound 2) .newest))))))))))
derive_free_closed ex_principal_m

def ex_nonprincipal_m {d} (κ F : Term d) : Formula 1 d :=
  (.forallE (.forallE (.forallE (.forallE (.imp (rd_entry_m (.bound 3) (.bound 2) F.weaken.weaken.weaken.weaken)
    (.imp (rd_entry_m (.bound 1) .newest (.bound 3)) (.imp (.neg (.mem .newest κ.weaken.weaken.weaken.weaken))
    (ed_nonprincipal_m (.bound 2)))))))))
derive_free_closed ex_nonprincipal_m

def ex_countable_m {d} (ω κ L F : Term d) : Formula 1 d :=
  (.forallE (.forallE (.imp (ef_levels_m ω.weaken.weaken κ.weaken.weaken (.bound 1)) (.imp ((es_fiber_m (𝒞 :=
    kpair_convention_l)) ω.weaken.weaken L.weaken.weaken F.weaken.weaken (.bound 1) .newest) (.existsE (ef_fiber_m
    ω.weaken.weaken.weaken κ.weaken.weaken.weaken (.bound 2) .newest))))))
derive_free_closed ex_countable_m

theorem em_family_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω κ L F : Term d) :
    Formula.satisfies ρ (em_family_m ω κ L F) ↔ Em_family_d (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (F.eval ρ) := by
  simp only [em_family_m, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_mem_iff, fn0_sat_l hE, Formula.satisfies_exists_iff, rd_entry_sat_l hE,
    Formula.satisfies_extensionalEq_iff_eq hE, Formula.satisfies_iff_iff, FilterZF.maximal_sat_d, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨ht, hf, hm⟩ => ⟨ht, hf, hm⟩, fun h => ⟨h.total, h.function, h.measure⟩⟩

theorem en_normal_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω κ L F : Term d) :
    Formula.satisfies ρ (en_normal_m ω κ L F) ↔ En_normal_d (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (F.eval ρ) := by
  simp only [en_normal_m, En_normal_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_mem_iff, fn0_sat_l hE, rd_entry_sat_l hE, Formula.satisfies_iff_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_isSuccessor_iff,
    Formula.satisfies_subset_iff, en_graph_sat_l hE, Definitional.Term.eval_weaken]; rfl

theorem ea_part_sat_l (hE : Extensional M) {d} (ρ : Env M d) (p : Bool) (ω κ L F : Term d) :
    Formula.satisfies ρ (ea_part_m p ω κ L F) ↔ Ea_part_d p (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (F.eval ρ) := by
  cases p <;> simp only [ea_part_m, Ea_part_d, Bool.false_eq_true, ↓reduceIte,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff, fn0_sat_l hE,
    rd_entry_sat_l hE, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_iff_iff,
    ea_test_sat_l hE, Formula.satisfies_extensionalEq_iff_eq hE, Definitional.Term.eval_weaken] <;> rfl

def ea_atoms_m {d} (ω κ L F : Term d) : Formula 1 d := .conj (ea_part_m false ω κ L F) (ea_part_m true ω κ L F)
derive_free_closed ea_atoms_m
theorem ea_atoms_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω κ L F : Term d) :
    Formula.satisfies ρ (ea_atoms_m ω κ L F) ↔ Ea_atoms_d (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (F.eval ρ) := by
  simp only [ea_atoms_m, Formula.satisfies_conj_iff, ea_part_sat_l hE]
  exact ⟨fun h p => by cases p; exact h.1; exact h.2, fun h => ⟨h false, h true⟩⟩

theorem ex_complete_sat_l (hE : Extensional M) {d} (ρ : Env M d) (κ L F : Term d) :
    Formula.satisfies ρ (ex_complete_m κ L F) ↔ ∀ n a U D, Fn0_d n (L.eval ρ) a → Rd_entry_d a U (F.eval ρ) →
      (∀ s, M.mem s D ↔ Fn0_d n (κ.eval ρ) s) → Ed_complete_d (κ.eval ρ) D U := by
  simp only [ex_complete_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, fn0_sat_l hE,
    rd_entry_sat_l hE, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, ed_complete_sat_l hE,
    Definitional.Term.eval_weaken]; rfl

theorem ex_principal_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω κ F : Term d) :
    Formula.satisfies ρ (ex_principal_m ω κ F) ↔ ∀ n a U, M.mem n (ω.eval ρ) → Fn0_d n (κ.eval ρ) a →
      Rd_entry_d a U (F.eval ρ) → ∀ A, M.mem A U ↔ (∀ s, M.mem s A → Fn0_d n (κ.eval ρ) s) ∧ M.mem a A := by
  simp only [ex_principal_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, fn0_sat_l hE,
    rd_entry_sat_l hE, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, Formula.satisfies_conj_iff,
    Definitional.Term.eval_weaken]; rfl

theorem ex_nonprincipal_sat_l (hE : Extensional M) {d} (ρ : Env M d) (κ F : Term d) :
    Formula.satisfies ρ (ex_nonprincipal_m κ F) ↔ ∀ a U i α, Rd_entry_d a U (F.eval ρ) → Rd_entry_d i α a →
      ¬ M.mem α (κ.eval ρ) → Ed_nonprincipal_d U := by
  simp only [ex_nonprincipal_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, rd_entry_sat_l hE,
    Formula.satisfies_mem_iff, Formula.satisfies_neg_iff, ed_nonprincipal_sat_l hE, Definitional.Term.eval_weaken]; rfl

theorem ex_countable_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω κ L F : Term d)
    (I : kpair_convention_l.Interpretation M) : Formula.satisfies ρ (ex_countable_m ω κ L F) ↔
      ∀ H f, Ef_levels_d (ω.eval ρ) (κ.eval ρ) H → Es_fiber_d I (ω.eval ρ) (L.eval ρ) (F.eval ρ) H f →
        ∃ g, Ef_fiber_d (ω.eval ρ) (κ.eval ρ) H g := by
  simp only [ex_countable_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, ef_levels_sat_l hE,
    es_fiber_sat_l I hE, Formula.satisfies_exists_iff, ef_fiber_sat_l hE, Definitional.Term.eval_weaken]; rfl

def ex_pre_m {d} (ω κ L F : Term d) : Formula 1 d := .conj (Formula.isOmega ω)
  (.conj (Formula.isCardinal kpair_convention_l κ) (.conj (.mem ω κ) (.conj (Formula.isOrdinal L)
    (.conj (.mem κ L) (.conj (Formula.isFunction kpair_convention_l F) (.conj (em_family_m ω κ L F) (.conj (es_coherent_m (𝒞 := kpair_convention_l) ω κ L F)
      (.conj (ex_complete_m κ L F) (.conj (ea_atoms_m ω κ L F) (.conj (en_normal_m ω κ L F)
        (.conj (ex_principal_m ω κ F) (ex_nonprincipal_m κ F))))))))))))
derive_free_closed ex_pre_m

theorem ex_pre_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {d} (ρ : Env M d) (ω κ L F : Term d) :
    Formula.satisfies ρ (ex_pre_m ω κ L F) ↔ Ex_pre_d I (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (F.eval ρ) := by
  simp only [ex_pre_m, Formula.satisfies_conj_iff, Formula.satisfies_isOmega_iff,
    Formula.satisfies_isCardinal_iff I hE, Formula.satisfies_mem_iff,
    Formula.satisfies_isFunction_iff I hE,
    Formula.satisfies_isOrdinal_iff, em_family_sat_l hE, es_coherent_sat_l I hE,
    ex_complete_sat_l hE, ea_atoms_sat_l hE, en_normal_sat_l hE,
    ex_principal_sat_l hE, ex_nonprincipal_sat_l hE]
  exact ⟨fun ⟨a, b, c, d, e, f, g, h, i, j, k, l, m⟩ => ⟨a, b, c, d, e, f, g, h, i, j, k, l, m⟩,
    fun h => ⟨h.omega, h.critical, h.uncountable, h.length, h.above, h.graph, h.measures, h.coherent,
      h.complete, h.atoms, h.normal, h.principal, h.nonprincipal⟩⟩

def ex_short_m {d} (ω κ L F : Term d) : Formula 1 d := .conj (ex_pre_m ω κ L F) (ex_countable_m ω κ L F)
derive_free_closed ex_short_m
theorem ex_short_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {d} (ρ : Env M d) (ω κ L F : Term d) :
    Formula.satisfies ρ (ex_short_m ω κ L F) ↔ Ex_short_d I (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (F.eval ρ) := by
  simp only [ex_short_m, Formula.satisfies_conj_iff, ex_pre_sat_l I hE,
    ex_countable_sat_l hE ρ ω κ L F I]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.toEx_pre_d, h.countable⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 短扩展器的长度截断

把测度图限制到较短支撑空间，实际得到新的短扩展器。正规性的新增坐标
小于旧坐标，因此仍落在较短长度中；其余测度与共同纤维直接沿限制保持。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem ex_restrict_l (hZF : M.Models ZF) {ω κ L F μ : M.Domain}
    (h : Ex_short_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F) (hμ : M.IsOrdinal μ) (hκμ : M.mem κ μ) (hμL : M.MemberSubset μ L) :
    ∃ G, Ex_short_d (kp_pair_l (ZF.modelsKP hZF)) ω κ μ G ∧ ∀ a U, Rd_entry_d a U G ↔
      (∃ n, M.mem n ω ∧ Fn0_d n μ a) ∧ Rd_entry_d a U F := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨S, hS⟩ := ZF.fseq_space_exists_l I hZF h.omega μ
  obtain ⟨G, hg⟩ := ZF.exists_restriction hZF I F S
  have good a : M.mem a S ↔ ∃ n, M.mem n ω ∧ Fn0_d n μ a := (hS a).trans
    (exists_congr fun n => and_congr_right fun _ => ⟨fn0_of_function_l (ZF.modelsKP hZF), fn0_function_l (ZF.modelsKP hZF)⟩)
  have spec a U : Rd_entry_d a U G ↔ (∃ n, M.mem n ω ∧ Fn0_d n μ a) ∧ Rd_entry_d a U F :=
    (hg.2 a U).trans (and_congr_left fun _ => good a)
  have old a U (ha : Rd_entry_d a U G) := ((spec a U).mp ha).2
  have measures : Em_family_d ω κ μ G := by
    refine ⟨fun n a hn ha => ?_, fun a U V hu hv => h.measures.function a U V (old a U hu) (old a V hv), ?_⟩
    · obtain ⟨U, hu⟩ := h.measures.total n a hn (ha.mono_target_l hμL)
      exact ⟨U, (spec a U).mpr ⟨⟨n, hn, ha⟩, hu⟩⟩
    · intro a U ha
      obtain ⟨n, hn, hna⟩ := ((spec a U).mp ha).1
      obtain ⟨m, D, _, hma, hd, hu⟩ := h.measures.measure a U (old a U ha)
      have e := hma.domain_eq_l hZF.1 hna
      subst m
      exact ⟨n, D, hn, hna, hd, hu⟩
  have normal : En_normal_d ω κ μ G := by
    intro n a U D f i α A hn ha haU hd hf hiα hAU below
    obtain ⟨m, b, V, β, B, hm, hmn, hb, hab, hnβ, hβα, hbV, hBV, read⟩ :=
      h.normal n a U D f i α A hn (ha.mono_target_l hμL) (old a U haU) hd hf hiα hAU below
    have hβμ := hμ.transitive α (ha.bound_l hiα).2 β hβα
    have hbμ : Fn0_d m μ b := hb.retarget_l fun r x hrx => by
      rcases (hmn r).mp (hb.bound_l hrx).1 with hr | he
      · obtain ⟨y, hy, hry⟩ := ha.2.1 r hr
        have hry' : Rd_entry_d r y b := hry.elim fun p hp => ⟨p, hp.1, hab p hp.2⟩
        have e := hb.2.2 r (hb.bound_l hrx).1 y (hb.bound_l hry').2 x (hb.bound_l hrx).2 hry' hrx
        exact e ▸ hy
      · have e := hZF.1.eq_of_same_members r n he
        subst r
        exact hb.2.2 n (hb.bound_l hnβ).1 β (hb.bound_l hnβ).2 x (hb.bound_l hrx).2 hnβ hrx ▸ hβμ
    exact ⟨m, b, V, β, B, hm, hmn, hbμ, hab, hnβ, hβα, (spec b V).mpr ⟨⟨m, hm, hbμ⟩, hbV⟩, hBV, read⟩
  have pre : Ex_pre_d (kp_pair_l (ZF.modelsKP hZF)) ω κ μ G := by
    refine ⟨h.omega, h.critical, h.uncountable, hμ, hκμ,
      ⟨hg.1, fun a U V hu hv => h.graph.2 a U V (old a U hu) (old a V hv)⟩,
      measures, ?_, ?_, ?_, normal, ?_, ?_⟩
    · intro m n q a b U V A hm hn hq ha hab haV hbU hA
      exact h.coherent m n q a b U V A hm hn hq (ha.mono_target_l hμL) (cp0_mono_l hμL hab) (old a V haV) (old b U hbU) hA
    · exact fun n a U D ha hu hd => h.complete n a U D (ha.mono_target_l hμL) (old a U hu) hd
    · exact fun p n a U i r α β hn ha hu hi hr => h.atoms p n a U i r α β hn (ha.mono_target_l hμL) (old a U hu) hi hr
    · exact fun n a U hn ha hu => h.principal n a U hn ha (old a U hu)
    · exact fun a U i α hu hi hα => h.nonprincipal a U i α (old a U hu) hi hα
  refine ⟨G, ⟨pre, fun H f hH hf => ?_⟩, spec⟩
  apply h.countable H f hH
  refine ⟨hf.1.mono_target_l hμL, fun n hn => ?_⟩
  obtain ⟨A, a, U, hA, ha, sub, haU, hAU⟩ := hf.2 n hn
  exact ⟨A, a, U, hA, ha.mono_target_l hμL, sub, old a U haU, hAU⟩

end YesMetaZFC.SetTheory.LargeCardinal
