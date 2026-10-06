import YesMetaZFC.Model.SetTheory.Internal.SourceFamily
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderTuple

/-! # 集合值代表的共同编码

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
    (source : Ep_source_d hZF ω κ K X R) (hn : M.mem n ω) (hm : M.mem m ω)
    (hD : Ep_space_d κ n D) (hE : Ep_space_d κ m E) (hfX : M.mem f X) (hf : Fn0_d D X f)
    (bound : ∀ t B, Rd_entry_d t B f → M.MemberSubset B E) :
    ∃ l q r H A, M.mem l ω ∧ Fn0_d n l q ∧ Fn0_d m l r ∧ Ep_space_d κ l H ∧
      M.mem A X ∧ M.MemberSubset A H ∧ ∀ t B, Rd_entry_d t B f → ∀ x,
        M.mem x B ↔ ∃ s, M.mem s A ∧ Cp0_d n l κ q s t ∧ Cp0_d m l κ r s x := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨l, q, r, hl, hq, hr, join⟩ := ep_tuple_l hZF (κ := κ) source.omega hn hm
  obtain ⟨H, hHX, hH⟩ := source.space_l hZF hl
  have lκ := fun i hi => source.below i (source.omega.transitive hZF l hl i hi)
  have hqX := source.transitive K source.finite_mem q ((source.finite q).mpr
    ⟨n, hn, fn0_function_l (ZF.modelsKP hZF) (hq.mono_target_l lκ)⟩)
  have hrX := source.transitive K source.finite_mem r ((source.finite r).mpr
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
    (subsets : Ea_subset_d ω κ X Y) (source : Ep_source_d hZF ω κ K X R)
    (target : Ep_source_d hZF ω κ K' Y S) (hn : M.mem n ω) (hm : M.mem m ω)
    (hD : Ep_space_d κ n D) (hE : Ep_space_d κ m E) (hfX : M.mem f X) (hf : Fn0_d D X f)
    (bound : ∀ t B, Rd_entry_d t B f → M.MemberSubset B E) : M.mem f Y := by
  obtain ⟨l, q, r, H, A, hl, hq, hr, hH, hAX, sub, decode⟩ :=
    ep_set_function_code_l hZF source hn hm hD hE hfX hf bound
  have lκ := fun i hi => source.below i (source.omega.transitive hZF l hl i hi)
  have hqY := target.transitive K' target.finite_mem q ((target.finite q).mpr
    ⟨n, hn, fn0_function_l (ZF.modelsKP hZF) (hq.mono_target_l lκ)⟩)
  have hrY := target.transitive K' target.finite_mem r ((target.finite r).mpr
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
