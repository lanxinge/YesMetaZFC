import YesMetaZFC.SetTheory.LargeCardinal.ExtenderFiberRelative
import YesMetaZFC.Model.SetTheory.Internal.SourceFamily

/-! # 在嵌套施加源之间搬运完整可数层族

先用两源共有的序数编号把任意子集编码成 κ 上的二元关系。
有限幂子集一致性搬运关系码；按有限列长度切片后恢复原来的层族。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 同一实际编号属于两源时，其定义域的任意源内子集均可搬运。 -/
theorem Ea_subset_d.indexed_subset_l {ω κ K X R K' Y S A e T : M.Domain}
    (subsets : Ea_subset_d ω κ X Y) (source : Ep_source_d hZF ω κ K X R)
    (target : Ep_source_d hZF ω κ K' Y S) (hAY : M.mem A Y) (heX : M.mem e X) (heY : M.mem e Y)
    (inj : M.IsSetInjectionFromTo I e A κ) (hT : M.mem T X) (sub : M.MemberSubset T A) : M.mem T Y := by
  obtain ⟨c, hc⟩ := source.code
  obtain ⟨d, hd⟩ := target.code
  obtain ⟨P, hP, ps⟩ := source.square_l hZF source.cardinal_mem
  let ρ : Env M 3 := ⟨Fin.cases T (Fin.cases κ (fun _ => e)), fun _ => κ⟩
  let φ : UnarySchema 3 := { body := Formula.existsMem (.bound 1) (Formula.existsMem (.bound 3)
    (.conj (rd_entry0_m (.bound 1) .newest (.bound 5)) (kpair0_m (.bound 2) .newest .newest))) }
  have read p : φ.denote ρ p ↔ ∃ a, M.mem a T ∧ ∃ x, M.mem x κ ∧ Rd_entry_d a x e ∧ KPair_d M p x x := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      rd_entry0_sat_l hZF.1, kpair0_sat_l hZF.1]; rfl
  obtain ⟨Q, hQ, qs⟩ := sc_separate_source_l I hZF source.omega source.transitive hc source.theory φ
    (.existsMem _ (.existsMem _ (.conj (rd_entry0_delta_l ..) (kpair0_delta_l ..)))) ρ
    (Fin.cases hT (Fin.cases source.cardinal_mem (fun _ => heX))) hP
  have hQY := subsets.relation_l hZF source target hQ (fun p hp => (ps p).mp ((qs p).mp hp).1)
  have entry x : Rd_entry_d x x Q ↔ ∃ a, M.mem a T ∧ Rd_entry_d a x e := by
    constructor
    · rintro ⟨p, pair, hp⟩
      obtain ⟨a, ha, y, _, hay, code⟩ := (read p).mp ((qs p).mp hp).2
      exact ⟨a, ha, (kpair_injective_l M code pair).1 ▸ hay⟩
    · rintro ⟨a, ha, hax⟩
      obtain ⟨p, hp⟩ := (I).total x x
      have hx := inj.1.output_mem_of_pairMember hax
      exact ⟨p, hp, (qs p).mpr ⟨(ps p).mpr ⟨x, hx, x, hx, hp⟩, (read p).mpr ⟨a, ha, x, hx, hax, hp⟩⟩⟩
  let η : Env M 3 := ⟨Fin.cases κ (Fin.cases e (fun _ => Q)), fun _ => κ⟩
  let ψ : UnarySchema 3 := {
    body := Formula.existsMem (.bound 1) (.conj (rd_entry0_m (.bound 1) .newest (.bound 3)) (rd_entry0_m .newest .newest (.bound 4))) }
  have decode a : ψ.denote η a ↔ ∃ x, M.mem x κ ∧ Rd_entry_d a x e ∧ Rd_entry_d x x Q := by
    simp only [ψ, UnarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, rd_entry0_sat_l hZF.1]; rfl
  obtain ⟨B, hB, bs⟩ := sc_separate_source_l I hZF target.omega target.transitive hd target.theory ψ
    (.existsMem _ (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..))) η
    (Fin.cases target.cardinal_mem (Fin.cases heY (fun _ => hQY))) hAY
  have eq : B = T := hZF.1.eq_of_same_members B T (fun a => by
    rw [bs a, decode a]
    constructor
    · rintro ⟨_, x, _, hax, hx⟩
      obtain ⟨b, hb, hbx⟩ := (entry x).mp hx
      exact inj.2 b a x hbx hax ▸ hb
    · intro ha
      obtain ⟨x, hx, hax⟩ := inj.1.2.2 a (sub a ha)
      exact ⟨sub a ha, x, hx, hax, (entry x).mpr ⟨a, ha, hax⟩⟩)
  exact eq ▸ hB

/-- 层族由其全部有限列之并及列长度唯一确定，无须预先共享整张 ω 列。 -/
theorem Ea_subset_d.levels_l {ω κ K X R K' Y S H : M.Domain}
    (subsets : Ea_subset_d ω κ X Y) (source : Ep_source_d hZF ω κ K X R)
    (target : Ep_source_d hZF ω κ K' Y S) (inside : M.MemberSubset Y X) (hκ : M.IsOrdinal κ)
    (hH : M.mem H X) (levels : Ef_levels_d ω κ H) : M.mem H Y := by
  obtain ⟨c, hc⟩ := source.code
  obtain ⟨d, hd⟩ := target.code
  obtain ⟨P, hP, bound⟩ := source.theory.algebra.envelope_l hH
  let ρ : Env M 3 := ⟨Fin.cases ω (Fin.cases P (fun _ => H)), fun _ => ω⟩
  let φ : UnarySchema 3 := { body := Formula.existsMem (.bound 1) (Formula.existsMem (.bound 3)
    (.conj (rd_entry0_m (.bound 1) .newest (.bound 5)) (.mem (.bound 2) .newest))) }
  have read s : φ.denote ρ s ↔ ∃ n, M.mem n ω ∧ ∃ A, M.mem A P ∧ Rd_entry_d n A H ∧ M.mem s A := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      rd_entry0_sat_l hZF.1, Formula.satisfies_mem_iff]; rfl
  obtain ⟨T, hT, ts⟩ := sc_separate_source_l I hZF source.omega source.transitive hc source.theory φ
    (.existsMem _ (.existsMem _ (.conj (rd_entry0_delta_l ..) (.mem _ _)))) ρ
    (Fin.cases source.omega_mem (Fin.cases hP (fun _ => hH))) (inside K' target.finite_mem)
  obtain ⟨e, he, index⟩ := target.finite_index_l hZF hκ
  have hTY := subsets.indexed_subset_l hZF source target target.finite_mem (inside e he) he index hT
    (fun s hs => ((ts s).mp hs).1)
  obtain ⟨P₀, fn⟩ := levels.1
  let η : Env M 1 := ⟨fun _ => κ, fun _ => κ⟩
  let ψ : BinarySchema 1 := { body := fn0_m (.bound 1) (.bound 2) .newest }
  have decode n s : ψ.denote η n s ↔ Fn0_d n κ s := fn0_sat_l hZF.1 ..
  obtain ⟨G, _, hG, _, gf, gs⟩ := sc_separation_function_l hZF target.omega target.transitive hd target.theory ψ
    (fn0_delta_l ..) η (fun _ => target.cardinal_mem) target.omega_mem hTY
  have row n A B (hnA : Rd_entry_d n A H) (hnB : Rd_entry_d n B G) : A = B := by
    apply hZF.1.eq_of_same_members A B
    intro s
    rw [gs n B hnB s, decode n s]
    constructor
    · intro hs
      have fs := levels.2 n A hnA s hs
      exact ⟨(ts s).mpr ⟨(target.finite s).mpr ⟨n, (fn.bound_l hnA).1, fn0_function_l (ZF.modelsKP hZF) fs⟩,
        (read s).mpr ⟨n, (fn.bound_l hnA).1, A, (bound n A hnA).2, hnA, hs⟩⟩, fs⟩
    · rintro ⟨hs, fs⟩
      obtain ⟨m, _, C, _, hmC, hsC⟩ := (read s).mp ((ts s).mp hs).2
      have eq := (levels.2 m C hmC s hsC).domain_eq_l hZF.1 fs
      subst m
      exact (fn0_function_l (ZF.modelsKP hZF) fn).1.2 n C A hmC hnA ▸ hsC
  have eq : H = G := (fn0_function_l (ZF.modelsKP hZF) fn).1.1.eq_of_pairMember_iff hZF.1
    (fn0_function_l (ZF.modelsKP hZF) gf).1.1 (fun n A => ⟨fun hnA => by
      obtain ⟨B, _, hnB⟩ := gf.2.1 n (fn.bound_l hnA).1
      exact (row n A B hnA hnB).symm ▸ hnB, fun hnA => by
      obtain ⟨B, _, hnB⟩ := fn.2.1 n (gf.bound_l hnA).1
      exact row n B A hnB hnA ▸ hnB⟩)
  exact eq.symm ▸ hG

/-- 较小所属模型的局部短扩展器，决定较大施加源中已有层族的共同纤维。 -/
theorem It_local_d.source_fiber_l {ω κ K X R K' Y S L F H f : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (owner : Ep_source_d hZF ω κ K' Y S)
    (inside : M.MemberSubset Y X) (agree : Ea_agree_d ω κ X Y)
    (branches : Sc_branch_d ω Y) (loc : It_local_d ω Y κ L F)
    (hH : M.mem H X) (levels : Ef_levels_d ω κ H) (fiber : Es_fiber_d I ω L F H f) :
    ∃ g, M.mem g Y ∧ Ef_fiber_d ω κ H g :=
  loc.fiber_l hZF owner branches
    (agree.subset_l.levels_l hZF source owner inside (loc.ordinals_l (ZF.modelsKP hZF) owner.transitive).1 hH levels) levels fiber

end YesMetaZFC.SetTheory.LargeCardinal
