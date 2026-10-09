import YesMetaZFC.Model.SetTheory.Internal.TypeMinus

/-! # 前驱算子的自然数矩阵

把已经核验的纯语法转换收集为 ω 上的实际关系。给定这张矩阵，
查询转换和类型逆像都是有界公式；初等映射因而可直接搬运整个算子。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Tm_table_d (ω B : M.Domain) : Prop := M.IsSetRelationOn I B ω ∧
  ∀ z w, M.PairMember I z w B ↔ Tm_code_d I ω z w

theorem tm_table_exists_l (hZF : M.Models ZF) {ω : M.Domain} (hω : M.IsOmega ω) : ∃ B, Tm_table_d I ω B := by
  let φ : BinarySchema 1 := { body := tm_code_m (.bound 2) (.bound 1) .newest }
  let ρ : Env M 1 := ⟨fun _ => ω, fun _ => ω⟩
  obtain ⟨B, hB, val⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ρ ω
  have read z w : φ.denote ρ z w ↔ Tm_code_d I ω z w := tm_code_sat_l I hZF.1 ..
  refine ⟨B, hB, fun z w => (val z w).trans ⟨fun h => (read z w).mp h.2.2, ?_⟩⟩
  intro h
  have zw := h.natural_l I hZF hω
  exact ⟨zw.1, zw.2, (read z w).mpr h⟩

def tm_link0_m {d} (ω B p q : Term d) : Formula 1 d := set[d] ⟪
  ∃ z ∈ ⌜ω⌝ₛ, ∃ w ∈ ⌜ω⌝ₛ, ∃ a ∈ ⌜p⌝ₛ, ∃ e ∈ a,
    ⌜kpair0_m⌝ₚ(⌜p⌝ₛ, z, e) ∧ ⌜kpair0_m⌝ₚ(⌜q⌝ₛ, w, e) ∧ ⌜rd_entry0_m⌝ₚ(z, w, ⌜B⌝ₛ)⟫
derive_free_closed tm_link0_m

theorem tm_link0_delta_l {d} (ω B p q : Term d) : (tm_link0_m ω B p q).IsDelta0 :=
  .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
    (.conj (kpair0_delta_l ..) (.conj (kpair0_delta_l ..) (rd_entry0_delta_l ..))))))

theorem tm_link0_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω B p q : Term d)
    (hB : Tm_table_d (kp_pair_l hKP) (ω.eval ρ) (B.eval ρ)) :
    Formula.satisfies ρ (tm_link0_m ω B p q) ↔ Tm_query_d (kp_pair_l hKP) (ω.eval ρ) (p.eval ρ) (q.eval ρ) := by
  simp only [tm_link0_m, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, kpair0_sat_l hKP.1,
    rd_entry0_sat_l hKP.1, Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨z, _, w, _, _, _, e, _, cp, cq, code⟩
    exact ⟨z, e, w, cp, cq, (hB.2 z w).mp code⟩
  · rintro ⟨z, e, w, cp, cq, code⟩
    have entry := (hB.2 z w).mpr code
    have zw := hB.1.2 z w entry
    obtain ⟨a, ha, he⟩ := (kpair_union_l M cp e).mpr (Or.inr rfl)
    exact ⟨z, zw.1, w, zw.2, a, ha, e, he, cp, cq, entry⟩

def tm_cut0_m {d} (ω B D t u : Term d) : Formula 1 d := set[d] ⟪
  ⌜u⌝ₛ ⊆ ⌜D⌝ₛ ∧ (∀ p ∈ ⌜D⌝ₛ,
    p ∈ ⌜u⌝ₛ ↔ (∃ q ∈ ⌜t⌝ₛ, ⌜tm_link0_m⌝ₚ(⌜ω⌝ₛ, ⌜B⌝ₛ, p, q)))⟫
derive_free_closed tm_cut0_m

theorem tm_cut0_delta_l {d} (ω B D t u : Term d) : (tm_cut0_m ω B D t u).IsDelta0 :=
  .conj (.atom _ _ _) (.forallMem _ (.iff (.mem _ _) (.existsMem _ (tm_link0_delta_l ..))))

theorem tm_cut0_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω B D t u : Term d)
    (hB : Tm_table_d (kp_pair_l hKP) (ω.eval ρ) (B.eval ρ)) :
    Formula.satisfies ρ (tm_cut0_m ω B D t u) ↔
      Tm_minus_d (kp_pair_l hKP) (ω.eval ρ) (D.eval ρ) (t.eval ρ) (u.eval ρ) := by
  have link p q := tm_link0_sat_l hKP ((ρ.push p).push q) ω.weaken.weaken B.weaken.weaken
    (.newest : Term (d+1)).weaken .newest (by simpa only [Definitional.Term.eval_weaken] using hB)
  simp only [tm_cut0_m, Formula.satisfies_conj_iff, Formula.satisfies_subset_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, Formula.satisfies_existsMem_iff, link, Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨sub, read⟩ p
    exact ⟨fun hp => ⟨sub p hp, ((read p (sub p hp)).mp hp).imp fun q h => ⟨h.2, h.1⟩⟩,
      fun ⟨hp, q, code, hq⟩ => (read p hp).mpr ⟨q, hq, code⟩⟩
  · intro read
    exact ⟨fun p hp => ((read p).mp hp).1, fun p hp => ⟨fun hu =>
      ((read p).mp hu).2.imp fun q h => ⟨h.2, h.1⟩, fun ⟨q, hq, code⟩ => (read p).mpr ⟨hp, q, code, hq⟩⟩⟩

end YesMetaZFC.SetTheory.Internal
