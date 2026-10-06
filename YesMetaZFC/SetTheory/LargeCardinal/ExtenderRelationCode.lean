import YesMetaZFC.SetTheory.LargeCardinal.ExtenderRelative

/-! # 有限幂一致性搬运小关系及其传递塌缩

二元关系先编码为二项 κ 值列的集合。搬运此集合后，在目标源内逐项还原
Kuratowski 有序对，并分离出原关系。目标的实际塌缩闭包和唯一性随后还原
同一个传递集合；这正是小模型的关系编码跨源搬运所需的步骤。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

include hZF in
/-- 两个不同坐标可指定任意值，其余坐标取第二个值；只用实际 ZF 函数构造。 -/
theorem ep_two_values_l {κ n z o a b : M.Domain} (hne : z ≠ o)
    (hz : M.mem z n) (ho : M.mem o n) (ha : M.mem a κ) (hb : M.mem b κ) :
    ∃ s, Fn0_d n κ s ∧ Rd_entry_d z a s ∧ Rd_entry_d o b s := by
  classical
  let ρ : Env M 3 := ⟨Fin.cases z (Fin.cases a (fun _ => b)), fun _ => z⟩
  let φ : BinarySchema 3 := {
    body := .disj
      (.conj (Formula.extensionalEq (.bound 1) (.bound 2)) (Formula.extensionalEq .newest (.bound 3)))
      (.conj (.neg (Formula.extensionalEq (.bound 1) (.bound 2))) (Formula.extensionalEq .newest (.bound 4))) }
  have sat i x : φ.denote ρ i x ↔ (i = z ∧ x = a) ∨ (i ≠ z ∧ x = b) := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_neg_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1]; rfl
  obtain ⟨s, hs, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := n) (target := κ)
    (fun i _ => by
      by_cases hi : i = z
      · exact ⟨a, (sat i a).mpr (Or.inl ⟨hi, rfl⟩)⟩
      · exact ⟨b, (sat i b).mpr (Or.inr ⟨hi, rfl⟩)⟩)
    (fun i _ x y hx hy => by
      rcases (sat i x).mp hx with ⟨hi, rfl⟩ | ⟨hi, rfl⟩ <;>
        rcases (sat i y).mp hy with ⟨hj, rfl⟩ | ⟨hj, rfl⟩
      · rfl
      · exact (hj hi).elim
      · exact (hi hj).elim
      · rfl)
    (fun i x _ hx => ((sat i x).mp hx).elim (fun h => h.2.symm ▸ ha) (fun h => h.2.symm ▸ hb))
  exact ⟨s, fn0_of_function_l (ZF.modelsKP hZF) hs,
    (spec z a).mpr ⟨hz, (sat z a).mpr (Or.inl ⟨rfl, rfl⟩)⟩,
    (spec o b).mpr ⟨ho, (sat o b).mpr (Or.inr ⟨Ne.symm hne, rfl⟩)⟩⟩

def ep_binary_pair_m {d} (κ z o s p : Term d) : Formula 1 d :=
  Formula.existsMem κ (Formula.existsMem κ.weaken
    (.conj (rd_entry0_m z.weaken.weaken (.bound 1) s.weaken.weaken)
      (.conj (rd_entry0_m o.weaken.weaken .newest s.weaken.weaken)
        (kpair0_m p.weaken.weaken (.bound 1) .newest))))
derive_free_closed ep_binary_pair_m

theorem ep_binary_pair_delta_l {d} (κ z o s p : Term d) : (ep_binary_pair_m κ z o s p).IsDelta0 :=
  .existsMem _ (.existsMem _ (.conj (rd_entry0_delta_l ..) (.conj (rd_entry0_delta_l ..) (kpair0_delta_l ..))))

theorem ep_binary_pair_sat_l (hE : Extensional M) {d} (ρ : Env M d) (κ z o s p : Term d) :
    Formula.satisfies ρ (ep_binary_pair_m κ z o s p) ↔
      ∃ a, M.mem a (κ.eval ρ) ∧ ∃ b, M.mem b (κ.eval ρ) ∧
        Rd_entry_d (z.eval ρ) a (s.eval ρ) ∧ Rd_entry_d (o.eval ρ) b (s.eval ρ) ∧ KPair_d M (p.eval ρ) a b := by
  simp only [ep_binary_pair_m, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    rd_entry0_sat_l hE, kpair0_sat_l hE, Definitional.Term.eval_weaken]; rfl

/-- 源内基本配对给出任意两个已知对象的 Kuratowski 对。 -/
theorem Ep_source_d.kpair_l {ω κ K X R a b : M.Domain} (source : Ep_source_d hZF ω κ K X R)
    (ha : M.mem a X) (hb : M.mem b X) : ∃ p, M.mem p X ∧ KPair_d M p a b :=
  source.theory.algebra.kpair_l ha hb

/-- 源的实际乘积闭包直接给出任意字母表的平方。 -/
theorem Ep_source_d.square_l {ω κ K X R A : M.Domain} (source : Ep_source_d hZF ω κ K X R)
    (hA : M.mem A X) : ∃ P, M.mem P X ∧ M.IsCartesianProduct I P A A :=
  source.theory.algebra.product A A hA hA

/-- 任意源内二元关系在 κ 上的部分，编码为一个实际有限 κ 幂子集。 -/
theorem ep_relation_code_l {ω κ K X R T : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (hT : M.mem T X) :
    ∃ n z o D C, M.mem n ω ∧ M.mem z ω ∧ M.mem o ω ∧ Ep_space_d κ n D ∧ M.mem C X ∧ M.MemberSubset C D ∧
      ∀ a b, M.mem a κ → M.mem b κ → (Rd_entry_d a b T ↔ ∃ s, M.mem s C ∧ Rd_entry_d z a s ∧ Rd_entry_d o b s) := by
  obtain ⟨z, hz, hzω⟩ := source.omega.1.1
  obtain ⟨o, ho, hoω⟩ := source.omega.1.2 z hzω
  obtain ⟨n, hn, hnω⟩ := source.omega.1.2 o hoω
  have hzo : z ≠ o := by intro e; subst o; exact hz z ho.predecessor_mem
  have hzn := (hn z).mpr (Or.inl ho.predecessor_mem)
  obtain ⟨D, hDX, hD⟩ := source.space_l hZF hnω
  obtain ⟨c, hc⟩ := source.code
  let ρ : Env M 4 := ⟨Fin.cases z (Fin.cases o (Fin.cases κ (fun _ => T))), fun _ => z⟩
  let φ : UnarySchema 4 := { body := Formula.existsMem (.bound 3) (Formula.existsMem (.bound 4)
    (.conj (rd_entry0_m (.bound 3) (.bound 1) (.bound 2))
      (.conj (rd_entry0_m (.bound 4) .newest (.bound 2)) (rd_entry0_m (.bound 1) .newest (.bound 6))))) }
  have sat s : φ.denote ρ s ↔ ∃ a, M.mem a κ ∧ ∃ b, M.mem b κ ∧
      Rd_entry_d z a s ∧ Rd_entry_d o b s ∧ Rd_entry_d a b T := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      rd_entry0_sat_l hZF.1]; rfl
  obtain ⟨C, hCX, spec⟩ := sc_separate_source_l I hZF source.omega source.transitive hc source.theory φ
    (.existsMem _ (.existsMem _ (.conj (rd_entry0_delta_l ..) (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..)))))
    ρ (Fin.cases (source.transitive ω source.omega_mem z hzω)
      (Fin.cases (source.transitive ω source.omega_mem o hoω) (Fin.cases source.cardinal_mem (fun _ => hT)))) hDX
  have code s : M.mem s C ↔ M.mem s D ∧ ∃ a, M.mem a κ ∧ ∃ b, M.mem b κ ∧
      Rd_entry_d z a s ∧ Rd_entry_d o b s ∧ Rd_entry_d a b T := (spec s).trans (and_congr_right fun _ => sat s)
  refine ⟨n, z, o, D, C, hnω, hzω, hoω, hD, hCX, fun s hs => ((code s).mp hs).1, fun a b ha hb => ⟨?_, ?_⟩⟩
  · intro hab
    obtain ⟨s, hs, hza, hob⟩ := ep_two_values_l hZF hzo hzn hn.predecessor_mem ha hb
    exact ⟨s, (code s).mpr ⟨(hD s).mpr hs, a, ha, b, hb, hza, hob, hab⟩, hza, hob⟩
  · rintro ⟨s, hs, hza, hob⟩
    obtain ⟨hsD, a', _, b', _, hza', hob', hab⟩ := (code s).mp hs
    have fn := fn0_function_l (ZF.modelsKP hZF) ((hD s).mp hsD)
    exact fn.1.2 z a' a hza' hza ▸ fn.1.2 o b' b hob' hob ▸ hab

/-- 有限幂子集的单向包含搬运源中的实际二元关系。 -/
theorem Ea_subset_d.relation_l {ω κ K X R K' Y S T : M.Domain}
    (subsets : Ea_subset_d ω κ X Y) (source : Ep_source_d hZF ω κ K X R)
    (target : Ep_source_d hZF ω κ K' Y S) (hT : M.mem T X)
    (bound : ∀ p, M.mem p T → ∃ a, M.mem a κ ∧ ∃ b, M.mem b κ ∧ KPair_d M p a b) : M.mem T Y := by
  obtain ⟨n, z, o, D, C, hnω, hzω, hoω, hD, hCX, sub, code⟩ := ep_relation_code_l hZF source hT
  have hCY := subsets n D C hnω hD sub hCX
  obtain ⟨d, hd⟩ := target.code
  have hzY := target.transitive ω target.omega_mem z hzω
  have hoY := target.transitive ω target.omega_mem o hoω
  let η : Env M 3 := ⟨Fin.cases z (Fin.cases o (fun _ => κ)), fun _ => z⟩
  let ψ : BinarySchema 3 := { body := ep_binary_pair_m (.bound 4) (.bound 2) (.bound 3) (.bound 1) .newest }
  have read s p : ψ.denote η s p ↔ ∃ a, M.mem a κ ∧ ∃ b, M.mem b κ ∧
      Rd_entry_d z a s ∧ Rd_entry_d o b s ∧ KPair_d M p a b := ep_binary_pair_sat_l hZF.1 ..
  obtain ⟨B, hBY, product⟩ := target.theory.algebra.product κ κ target.cardinal_mem target.cardinal_mem
  let ξ : Env M 4 := ⟨Fin.cases z (Fin.cases o (Fin.cases κ (fun _ => C))), fun _ => z⟩
  let χ : UnarySchema 4 := {
    body := Formula.existsMem (.bound 4)
      (ep_binary_pair_m (.bound 4) (.bound 2) (.bound 3) .newest (.bound 1)) }
  have decoded p : χ.denote ξ p ↔ ∃ s, M.mem s C ∧ ψ.denote η s p := by
    simp only [χ, UnarySchema.denote, Formula.satisfies_existsMem_iff, ep_binary_pair_sat_l hZF.1]
    exact exists_congr fun s => and_congr_right fun _ => (read s p).symm
  obtain ⟨Q, hQY, qs⟩ := sc_separate_source_l I hZF target.omega target.transitive hd target.theory
    χ (.existsMem _ (ep_binary_pair_delta_l ..)) ξ
    (Fin.cases hzY (Fin.cases hoY (Fin.cases target.cardinal_mem (fun _ => hCY)))) hBY
  have eq : Q = T := hZF.1.eq_of_same_members Q T (fun p => by
    rw [qs p, decoded p]
    constructor
    · rintro ⟨_, s, hs, hp⟩
      obtain ⟨a, ha, b, hb, hza, hob, hp⟩ := (read s p).mp hp
      obtain ⟨q, hq, hqT⟩ := (code a b ha hb).mpr ⟨s, hs, hza, hob⟩
      exact (kpair_unique_l M hZF.1 hq hp) ▸ hqT
    · intro hpT
      obtain ⟨a, ha, b, hb, hp⟩ := bound p hpT
      obtain ⟨s, hsC, hza, hob⟩ := (code a b ha hb).mp ⟨p, hp, hpT⟩
      exact ⟨(product p).mpr ⟨a, ha, b, hb, hp⟩, s, hsC, (read s p).mpr ⟨a, ha, b, hb, hza, hob, hp⟩⟩)
  exact eq ▸ hQY

/-- 搬运小关系码并在目标源内重新塌缩，得到同一个实际传递集合。 -/
theorem Ea_subset_d.collapse_l {ω κ K X R K' Y S A T B F : M.Domain}
    (subsets : Ea_subset_d ω κ X Y) (source : Ep_source_d hZF ω κ K X R)
    (target : Ep_source_d hZF ω κ K' Y S) (hA : M.mem A Y) (small : Sc_small_d Y A) (hT : M.mem T X)
    (bound : ∀ p, M.mem p T → ∃ a, M.mem a κ ∧ ∃ b, M.mem b κ ∧ KPair_d M p a b)
    (h : Wc_iso_d A T B F) : M.mem B Y ∧ M.mem F Y := by
  obtain ⟨C, G, hC, hG, g⟩ := target.collapse.collapse_l hA
    (subsets.relation_l hZF source target hT bound) small (h.well_founded_l (ZF.modelsKP hZF)) (h.extensional_l hZF.1)
  exact ⟨(h.unique_l hZF g).symm ▸ hC, (h.graph_unique_l hZF g).symm ▸ hG⟩

/-- 诱导隶属关系由源内平方中的有界分离得到，无须另假设关系码属于源。 -/
theorem Ep_source_d.membership_relation_l {ω κ K Z W c A R : M.Domain}
    (source : Ep_source_d hZF ω κ K Z W) (hA : M.mem A Z) (hm : Smem_d I c A R) : M.mem R Z := by
  obtain ⟨P, hPZ, hP⟩ := source.square_l hZF hA
  obtain ⟨c₀, hc⟩ := source.code
  let ρ : Env M 1 := ⟨fun _ => A, fun _ => A⟩
  let φ : UnarySchema 1 := {
    body := Formula.existsMem (.bound 1) (Formula.existsMem (.bound 2)
      (.conj (kpair0_m (.bound 2) (.bound 1) .newest) (.mem (.bound 1) .newest))) }
  have sat p : φ.denote ρ p ↔ ∃ x, M.mem x A ∧ ∃ y, M.mem y A ∧ KPair_d M p x y ∧ M.mem x y := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      kpair0_sat_l hZF.1, Formula.satisfies_mem_iff]; rfl
  obtain ⟨Q, hQZ, spec⟩ := sc_separate_source_l I hZF source.omega source.transitive hc source.theory φ
    (.existsMem _ (.existsMem _ (.conj (kpair0_delta_l ..) (.mem _ _)))) ρ (fun _ => hA) hPZ
  have eq : Q = R := hZF.1.eq_of_same_members Q R (fun p => ⟨fun hp => by
    obtain ⟨x, hx, y, hy, hpair, hxy⟩ := (sat p).mp ((spec p).mp hp).2
    obtain ⟨q, hq, hqR⟩ := (hm.2 x y).mpr ⟨hx, hy, hxy⟩
    exact kpair_unique_l M hZF.1 hq hpair ▸ hqR, fun hp => by
    obtain ⟨x, y, hpair⟩ := hm.1.2.2.1 p hp
    obtain ⟨hx, hy, hxy⟩ := (hm.2 x y).mp ⟨p, hpair, hp⟩
    exact (spec p).mpr ⟨(hP p).mpr ⟨x, hx, y, hy, hpair⟩, (sat p).mpr ⟨x, hx, y, hy, hpair, hxy⟩⟩⟩)
  exact eq ▸ hQZ

end YesMetaZFC.SetTheory.LargeCardinal
