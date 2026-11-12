import YesMetaZFC.SetTheory.LargeCardinal.Extender.TreeBranch
import YesMetaZFC.SetTheory.LargeCardinal.Extender.NormalSyntax
import YesMetaZFC.SetTheory.Card.FiniteSequenceJoin
import YesMetaZFC.Model.SetTheory.Source.Relation

/-! # 用有限 κ 幂的子集编码 κ 值代表

把函数值追加为末坐标，实际构造其图的有限列编码。子集一致的两个源
因而具有完全相同的 κ 值代表；正规性的跨模型施加将使用这一结论。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_function_code_l {ω κ K X R n D f : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (hn : M.mem n ω) (hD : Ep_space_d κ n D)
    (hfX : M.mem f X) (hf : Fn0_d D κ f) :
    ∃ m E A, M.mem m ω ∧ M.SuccessorOf m n ∧ Ep_space_d κ m E ∧ M.mem A X ∧ M.MemberSubset A E ∧
      ∀ t x, Rd_entry_d t x f ↔ M.mem t D ∧ M.mem x κ ∧
        ∃ s, M.mem s A ∧ M.MemberSubset t s ∧ Rd_entry_d n x s := by
  obtain ⟨m, hm, hmω⟩ := source.omega.1.2 n hn
  obtain ⟨E, hEX, hE⟩ := source.space_l hZF hmω
  obtain ⟨c, code⟩ := source.code
  let ρ : Env M 4 := ⟨Fin.cases f (Fin.cases D (Fin.cases κ (fun _ => n))), fun _ => n⟩
  let φ : UnarySchema 4 := { body := en_graph_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨A, hAX, spec⟩ := sc_separate_source_l I hZF source.omega source.transitive code source.theory
    φ (en_graph_delta_l ..) ρ
    (Fin.cases hfX (Fin.cases (source.space_mem_l hZF hn hD)
      (Fin.cases source.cardinal_mem (fun _ => source.transitive ω source.omega_mem n hn)))) hEX
  have read s : M.mem s A ↔ M.mem s E ∧ En_graph_d n κ D f s :=
    (spec s).trans (and_congr_right fun _ => en_graph_sat_l hZF.1 ..)
  refine ⟨m, E, A, hmω, hm, hE, hAX, fun s hs => ((read s).mp hs).1, fun t x => ⟨?_, ?_⟩⟩
  · intro htx
    have ht := (hD t).mp (hf.bound_l htx).1
    obtain ⟨m', s, _, hs, u, v, last⟩ := ZF.fseq_end_exists_l I hZF source.omega hn
      (fn0_function_l (ZF.modelsKP hZF) ht) (hf.bound_l htx).2
    have eu := last.source.2.2.2.eq hZF.1 hs.2.1
    subst u
    have ev := last.prefix_sequence.2.2.2.eq hZF.1 (fn0_function_l (ZF.modelsKP hZF) ht).2.1
    subst v
    have em := Structure.SuccessorOf.eq hZF.1 last.length_successor hm
    subst m'
    have sub : M.MemberSubset t s := fun p hp => by
      obtain ⟨i, _, y, _, hpi⟩ := ht.1 p hp
      obtain ⟨q, hq, hqs⟩ := ((last.prefix_restriction.2 i y).mp ⟨p, hpi, hp⟩).2
      exact (I).unique hpi hq ▸ hqs
    exact ⟨(hf.bound_l htx).1, (hf.bound_l htx).2, s,
      (read s).mpr ⟨(hE s).mpr (fn0_of_function_l (ZF.modelsKP hZF) hs),
        t, (hf.bound_l htx).1, sub, x, (hf.bound_l htx).2, htx, last.last_value⟩, sub, last.last_value⟩
  · rintro ⟨htD, hxκ, s, hsA, hts, hnx⟩
    obtain ⟨hsE, v, hvD, hvs, y, _, hvy, hny⟩ := (read s).mp hsA
    have ht := (hD t).mp htD
    have hv := (hD v).mp hvD
    have hs := fn0_function_l (ZF.modelsKP hZF) ((hE s).mp hsE)
    have et : v = t := hv.ext_l hZF.1 ht fun i hi => by
      obtain ⟨z, _, hiv⟩ := hv.2.1 i hi
      obtain ⟨w, _, hit⟩ := ht.2.1 i hi
      have ez := hs.1.2 i z w (hiv.elim fun p hp => ⟨p, hp.1, hvs p hp.2⟩)
        (hit.elim fun p hp => ⟨p, hp.1, hts p hp.2⟩)
      exact ⟨z, hiv, ez.symm ▸ hit⟩
    exact et ▸ hs.1.2 n y x hny hnx ▸ hvy

/-- 一致性直接搬运代表函数本身，不要求其定义域上的背景函数全都属于任一源。 -/
theorem Ea_subset_d.function_l {ω κ K X R K' Y S n D f : M.Domain}
    (subsets : Ea_subset_d ω κ X Y) (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R)
    (target : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K' Y S) (hn : M.mem n ω) (hD : Ep_space_d κ n D)
    (hfX : M.mem f X) (hf : Fn0_d D κ f) : M.mem f Y := by
  obtain ⟨m, E, A, hm, _, hE, hAX, sub, read⟩ := ep_function_code_l hZF source hn hD hfX hf
  have hAY := subsets m E A hm hE sub hAX
  obtain ⟨c, code⟩ := target.code
  let ρ : Env M 3 := ⟨Fin.cases A (Fin.cases n (fun _ => κ)), fun _ => n⟩
  let φ : BinarySchema 3 := {
    body := .conj (.mem .newest (.bound 4)) (Formula.existsMem (.bound 2)
      (.conj (Formula.subset (.bound 2) .newest) (rd_entry0_m (.bound 4) (.bound 1) .newest))) }
  have sat t x : φ.denote ρ t x ↔ M.mem x κ ∧ ∃ s, M.mem s A ∧ M.MemberSubset t s ∧ Rd_entry_d n x s := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_existsMem_iff, Formula.satisfies_subset_iff, rd_entry0_sat_l hZF.1]; rfl
  obtain ⟨g, hgY, hg, select⟩ := sc_uniform_source_l hZF target.omega target.transitive code target.theory
    φ (.conj (.mem _ _) (.existsMem _ (.conj (.atom _ _ _) (rd_entry0_delta_l ..)))) ρ
    (Fin.cases hAY (Fin.cases (target.transitive ω target.omega_mem n hn) (fun _ => target.cardinal_mem)))
    (target.space_mem_l hZF hn hD) target.cardinal_mem (fun t ht => by
      obtain ⟨x, hx, htx⟩ := hf.2.1 t ht
      exact ⟨x, hx, (sat t x).mpr ((read t x).mp htx).2⟩)
  have entry t x (htx : Rd_entry_d t x g) : Rd_entry_d t x f :=
    (read t x).mpr ⟨(hg.bound_l htx).1, (sat t x).mp (select t x htx)⟩
  have eq : g = f := (fn0_function_l (ZF.modelsKP hZF) hg).1.1.eq_of_pairMember_iff hZF.1
    (fn0_function_l (ZF.modelsKP hZF) hf).1.1 fun t x => ⟨entry t x, fun htx => by
      obtain ⟨y, _, hty⟩ := hg.2.1 t (hf.bound_l htx).1
      exact (fn0_function_l (ZF.modelsKP hZF) hf).1.2 t y x (entry t y hty) htx ▸ hty⟩
  exact eq ▸ hgY

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 两段有限坐标的实际分块投影

序数加法只用于定位第二段；编码对象仍是有限函数图。返回两张投影图，
并实际拼接任意两段 κ 值列，供集合值代表的图编码使用。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem ep_tuple_l (hZF : M.Models ZF) {ω κ n m : M.Domain} (hω : M.IsOmega ω)
    (hn : M.mem n ω) (hm : M.mem m ω) : ∃ l q r, M.mem l ω ∧ Fn0_d n l q ∧ Fn0_d m l r ∧
      ∀ s t, Fn0_d n κ s → Fn0_d m κ t → ∃ u, Fn0_d l κ u ∧ Cp0_d n l κ q u s ∧ Cp0_d m l κ r u t := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have mo := hω.members_areOrdinals (ZF.modelsKP hZF) m hm
  obtain ⟨l, hl, unique⟩ := ZF.ordinalAddition_existsUnique hZF I n mo
  have hlω := ZF.ordinalAddition_mem_omega hZF I hω hn hm hl
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => n⟩
  have idread i j := Formula.denote_identityValue_iff hZF.1 ρ i j
  obtain ⟨q, hq, qs⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I BinarySchema.identityValue ρ (source := n) (target := l)
    (fun i _ => ⟨i, (idread i i).mpr rfl⟩) (fun i _ j k hj hk => ((idread i j).mp hj).symm.trans ((idread i k).mp hk))
    (fun i j hi hij => (idread i j).mp hij ▸ (ZF.ordinalAddition_mem_iff hZF I mo hl).mpr (Or.inl hi))
  have qread i j : Rd_entry_d i j q ↔ M.mem i n ∧ i = j := (qs i j).trans (and_congr_right fun _ => idread i j)
  let η : Env M 1 := ⟨fun _ => n, fun _ => n⟩
  let φ : BinarySchema 1 := { body := Formula.isOrdinalAddition kpair_convention_l .newest (.bound 2) (.bound 1) }
  have sat i j : φ.denote η i j ↔ M.IsOrdinalAddition I j n i := Formula.satisfies_isOrdinalAddition_iff I hZF.1 ..
  obtain ⟨r, hr, rs⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ η (source := m) (target := l)
    (fun i hi => (ZF.ordinalAddition_existsUnique hZF I n (mo.mem hi)).imp fun j hj => (sat i j).mpr hj.1)
    (fun i hi j k hj hk => by
      obtain ⟨v, _, uniq⟩ := ZF.ordinalAddition_existsUnique hZF I n (mo.mem hi)
      exact (uniq j ((sat i j).mp hj)).trans (uniq k ((sat i k).mp hk)).symm)
    (fun i j hi hj => (ZF.ordinalAddition_mem_iff hZF I mo hl).mpr (Or.inr ⟨i, hi, (sat i j).mp hj⟩))
  have rread i j : Rd_entry_d i j r ↔ M.mem i m ∧ M.IsOrdinalAddition I j n i :=
    (rs i j).trans (and_congr_right fun _ => sat i j)
  refine ⟨l, q, r, hlω, fn0_of_function_l (ZF.modelsKP hZF) hq, fn0_of_function_l (ZF.modelsKP hZF) hr, fun s t hs ht => ?_⟩
  obtain ⟨l', u, _, hl', hu, head, tail⟩ := ZF.fseq_join_l I hZF hω hn hm
    (fn0_function_l (ZF.modelsKP hZF) hs) (fn0_function_l (ZF.modelsKP hZF) ht)
  have el := unique l' hl'
  subst l'
  refine ⟨u, fn0_of_function_l (ZF.modelsKP hZF) hu, ⟨hs, fun i hi => ?_⟩, ht, fun i hi => ?_⟩
  · obtain ⟨x, hx, hix⟩ := hs.2.1 i hi
    exact ⟨i, (ZF.ordinalAddition_mem_iff hZF I mo hl).mpr (Or.inl hi), x, hx,
      (qread i i).mpr ⟨hi, rfl⟩, ((head.2 i x).mp hix).2, hix⟩
  · obtain ⟨x, hx, hix⟩ := ht.2.1 i hi
    obtain ⟨_, j, hj, hju⟩ := (tail.2 i x).mp hix
    exact ⟨j, (ZF.ordinalAddition_mem_iff hZF I mo hl).mpr (Or.inr ⟨i, hi, hj⟩), x, hx,
      (rread i j).mpr ⟨hi, hj⟩, hju, hix⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 集合值代表的共同编码

若 f 的值是有限 κ 幂的子集，把成员关系编码为两段坐标的一个集合。
在另一源中先分离每条纤维，再统一收集实际函数图，因此子集一致性
也搬运所有这种集合值代表，包含后继子集一致性所需的代表。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def ep_pair_at_m {d} (κ n m l q r A t x : Term d) : Formula 1 d := Formula.existsMem A
  (.conj (cp0_m n.weaken l.weaken κ.weaken q.weaken .newest t.weaken)
    (cp0_m m.weaken l.weaken κ.weaken r.weaken .newest x.weaken))
derive_free_closed ep_pair_at_m

theorem ep_pair_at_delta_l {d} (κ n m l q r A t x : Term d) : (ep_pair_at_m κ n m l q r A t x).IsDelta0 :=
  .existsMem _ (.conj (cp0_delta_l ..) (cp0_delta_l ..))

theorem ep_pair_at_sat_l (hE : Extensional M) {d} (ρ : Env M d) (κ n m l q r A t x : Term d) :
    Formula.satisfies ρ (ep_pair_at_m κ n m l q r A t x) ↔ ∃ s, M.mem s (A.eval ρ) ∧
      Cp0_d (n.eval ρ) (l.eval ρ) (κ.eval ρ) (q.eval ρ) s (t.eval ρ) ∧
      Cp0_d (m.eval ρ) (l.eval ρ) (κ.eval ρ) (r.eval ρ) s (x.eval ρ) := by
  simp only [ep_pair_at_m, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    cp0_sat_l hE, Definitional.Term.eval_weaken]; rfl

/-- 两段有限坐标编码集合值函数，解码只使用有界量词。 -/
theorem ep_set_function_code_l (hZF : M.Models ZF) {ω κ K X R n m D E f : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (hn : M.mem n ω) (hm : M.mem m ω)
    (hD : Ep_space_d κ n D) (hE : Ep_space_d κ m E) (hfX : M.mem f X) (hf : Fn0_d D X f)
    (bound : ∀ t B, Rd_entry_d t B f → M.MemberSubset B E) :
    ∃ l q r H A, M.mem l ω ∧ Fn0_d n l q ∧ Fn0_d m l r ∧ Ep_space_d κ l H ∧
      M.mem A X ∧ M.MemberSubset A H ∧ ∀ t B, Rd_entry_d t B f → ∀ x,
        M.mem x B ↔ ∃ s, M.mem s A ∧ Cp0_d n l κ q s t ∧ Cp0_d m l κ r s x := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨l, q, r, hl, hq, hr, join⟩ := ep_tuple_l hZF (κ := κ) source.omega hn hm
  obtain ⟨H, hHX, hH⟩ := source.space_l hZF hl
  have lκ := fun i hi => source.below i (source.omega.transitive (ZF.modelsKP hZF) l hl i hi)
  have hqX := source.transitive K source.finite.mem_l q (((source.finite_l (ZF.modelsKP hZF)) q).mpr
    ⟨n, hn, fn0_function_l (ZF.modelsKP hZF) (hq.mono_target_l lκ)⟩)
  have hrX := source.transitive K source.finite.mem_l r (((source.finite_l (ZF.modelsKP hZF)) r).mpr
    ⟨m, hm, fn0_function_l (ZF.modelsKP hZF) (hr.mono_target_l lκ)⟩)
  obtain ⟨_, C, hCX, hfC⟩ := source.function_l hZF hfX hf
  obtain ⟨c, code⟩ := source.code
  let ρ : Env M 9 := ⟨Fin.cases κ (Fin.cases n (Fin.cases m (Fin.cases l (Fin.cases q
    (Fin.cases r (Fin.cases D (Fin.cases C (fun _ => f)))))))), fun _ => f⟩
  let φ : UnarySchema 9 := {
    body := Formula.existsMem (.bound 7) (Formula.existsMem (.bound 9) (Formula.existsMem .newest
      (.conj (rd_entry0_m (.bound 2) (.bound 1) (.bound 12))
        (.conj (cp0_m (.bound 5) (.bound 7) (.bound 4) (.bound 8) (.bound 3) (.bound 2))
          (cp0_m (.bound 6) (.bound 7) (.bound 4) (.bound 9) (.bound 3) .newest))))) }
  have natX t ht := source.transitive ω source.omega_mem t ht
  obtain ⟨A, hAX, as⟩ := sc_separate_source_l I hZF source.omega source.transitive code source.theory φ
    (.existsMem _ (.existsMem _ (.existsMem _ (.conj (rd_entry0_delta_l ..) (.conj (cp0_delta_l ..) (cp0_delta_l ..)))))) ρ
    (Fin.cases source.cardinal_mem (Fin.cases (natX n hn) (Fin.cases (natX m hm) (Fin.cases (natX l hl)
      (Fin.cases hqX (Fin.cases hrX (Fin.cases (source.space_mem_l hZF hn hD) (Fin.cases hCX (fun _ => hfX))))))))) hHX
  have read s : M.mem s A ↔ M.mem s H ∧ ∃ t, M.mem t D ∧ ∃ B, M.mem B C ∧ ∃ x, M.mem x B ∧
      Rd_entry_d t B f ∧ Cp0_d n l κ q s t ∧ Cp0_d m l κ r s x := by
    refine (as s).trans (and_congr_right fun _ => ?_)
    simp only [φ, UnarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      rd_entry0_sat_l hZF.1, cp0_sat_l hZF.1]; rfl
  have decode t B (htB : Rd_entry_d t B f) x : M.mem x B ↔
      ∃ s, M.mem s A ∧ Cp0_d n l κ q s t ∧ Cp0_d m l κ r s x := by
    constructor
    · intro hx
      obtain ⟨s, hs, hqs, hrs⟩ := join t x ((hD t).mp (hf.bound_l htB).1) ((hE x).mp (bound t B htB x hx))
      exact ⟨s, (read s).mpr ⟨(hH s).mpr hs, t, (hf.bound_l htB).1, B, (hfC.bound_l htB).2,
        x, hx, htB, hqs, hrs⟩, hqs, hrs⟩
    · rintro ⟨s, hs, hqs, hrs⟩
      obtain ⟨hsH, t', _, B', _, x', hx', ht'B', hqs', hrs'⟩ := (read s).mp hs
      have et := cp0_unique_l hZF.1 hq ((hH s).mp hsH) hqs' hqs
      have eB := (fn0_function_l (ZF.modelsKP hZF) hf).1.2 t B' B (et ▸ ht'B') htB
      exact eB ▸ cp0_unique_l hZF.1 hr ((hH s).mp hsH) hrs' hrs ▸ hx'
  exact ⟨l, q, r, H, A, hl, hq, hr, hH, hAX, fun s hs => ((read s).mp hs).1, decode⟩

theorem Ea_subset_d.set_function_l (hZF : M.Models ZF) {ω κ K X R K' Y S n m D E f : M.Domain}
    (subsets : Ea_subset_d ω κ X Y) (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R)
    (target : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K' Y S) (hn : M.mem n ω) (hm : M.mem m ω)
    (hD : Ep_space_d κ n D) (hE : Ep_space_d κ m E) (hfX : M.mem f X) (hf : Fn0_d D X f)
    (bound : ∀ t B, Rd_entry_d t B f → M.MemberSubset B E) : M.mem f Y := by
  obtain ⟨l, q, r, H, A, hl, hq, hr, hH, hAX, sub, decode⟩ :=
    ep_set_function_code_l hZF source hn hm hD hE hfX hf bound
  have lκ := fun i hi => source.below i (source.omega.transitive (ZF.modelsKP hZF) l hl i hi)
  have hqY := target.transitive K' target.finite.mem_l q (((target.finite_l (ZF.modelsKP hZF)) q).mpr
    ⟨n, hn, fn0_function_l (ZF.modelsKP hZF) (hq.mono_target_l lκ)⟩)
  have hrY := target.transitive K' target.finite.mem_l r (((target.finite_l (ZF.modelsKP hZF)) r).mpr
    ⟨m, hm, fn0_function_l (ZF.modelsKP hZF) (hr.mono_target_l lκ)⟩)
  have hAY := subsets l H A hl hH sub hAX
  obtain ⟨d, targetCode⟩ := target.code
  let η : Env M 8 := ⟨Fin.cases κ (Fin.cases n (Fin.cases m (Fin.cases l
    (Fin.cases q (Fin.cases r (Fin.cases A (fun _ => E))))))), fun _ => E⟩
  have natY t ht := target.transitive ω target.omega_mem t ht
  have params : ∀ i, M.mem (η.bound i) Y := Fin.cases target.cardinal_mem (Fin.cases (natY n hn)
    (Fin.cases (natY m hm) (Fin.cases (natY l hl) (Fin.cases hqY (Fin.cases hrY
      (Fin.cases hAY (fun _ => target.space_mem_l hZF hm hE)))))))
  let ψ : BinarySchema 8 := {
    body := ep_pair_at_m (.bound 2) (.bound 3) (.bound 4) (.bound 5)
      (.bound 6) (.bound 7) (.bound 8) (.bound 1) .newest }
  have fiber t x : ψ.denote η t x ↔ ∃ s, M.mem s A ∧ Cp0_d n l κ q s t ∧ Cp0_d m l κ r s x :=
    ep_pair_at_sat_l hZF.1 ..
  obtain ⟨g, B, hgY, _, hg, row⟩ := sc_separation_function_l hZF target.omega target.transitive targetCode target.theory
    ψ (ep_pair_at_delta_l ..) η params (target.space_mem_l hZF hn hD) (target.space_mem_l hZF hm hE)
  have select t C (htC : Rd_entry_d t C g) : M.MemberSubset C E ∧ ∀ x, M.mem x E →
      (M.mem x C ↔ ∃ s, M.mem s A ∧ Cp0_d n l κ q s t ∧ Cp0_d m l κ r s x) := by
    refine ⟨fun x hx => ((row t C htC x).mp hx).1, fun x hx => ?_⟩
    exact (row t C htC x).trans ((and_iff_right hx).trans (fiber t x))
  have same t B C (htB : Rd_entry_d t B g) (htC : Rd_entry_d t C f) : B = C := by
    obtain ⟨sub, spec⟩ := select t B htB
    exact hZF.1.eq_of_same_members B C fun x => ⟨fun hx => (decode t C htC x).mpr ((spec x (sub x hx)).mp hx),
      fun hx => (spec x (bound t C htC x hx)).mpr ((decode t C htC x).mp hx)⟩
  have eq : g = f := hg.ext_l hZF.1 hf fun t ht => by
    obtain ⟨B, _, htB⟩ := hg.2.1 t ht
    obtain ⟨C, _, htC⟩ := hf.2.1 t ht
    exact ⟨B, htB, (same t B C htB htC).symm ▸ htC⟩
  exact eq ▸ hgY

end YesMetaZFC.SetTheory.LargeCardinal
