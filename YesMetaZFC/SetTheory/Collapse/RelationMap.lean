import YesMetaZFC.SetTheory.Collapse.RelationBounded

/-! # 任意良基关系的有界塌缩证书

允许不同节点具有同一塌缩值。全部检查均为 Δ₀，因此内部良基关系的
实际塌缩图给出背景良基性；外延关系再由递归唯一性恢复 Mostowski 同构。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

structure Wc_map_d (A R B F : M.Domain) : Prop where
  transitive : M.TransitiveSet B
  function : Fn0_d A B F
  onto : ∀ x, M.mem x B → ∃ a, M.mem a A ∧ Rd_entry_d a x F
  equation : ∀ a, M.mem a A → ∀ x, M.mem x B → Rd_entry_d a x F →
    ∀ y, M.mem y B → (M.mem y x ↔ ∃ b, M.mem b A ∧ Rd_entry_d b a R ∧ Rd_entry_d b y F)

def wc_map_m {n} (A R B F : Term n) : Formula 1 n :=
  .conj (Formula.forallMem B (Formula.subset .newest B.weaken))
    (.conj (fn0_m A B F) (.conj
      (Formula.forallMem B (Formula.existsMem A.weaken (rd_entry0_m .newest (.bound 1) F.weaken.weaken)))
      (Formula.forallMem A (Formula.forallMem B.weaken (.imp
        (rd_entry0_m (.bound 1) .newest F.weaken.weaken)
        (Formula.forallMem B.weaken.weaken (.iff (.mem .newest (.bound 1))
          (Formula.existsMem A.weaken.weaken.weaken (.conj
            (rd_entry0_m .newest (.bound 3) R.weaken.weaken.weaken.weaken)
            (rd_entry0_m .newest (.bound 1) F.weaken.weaken.weaken.weaken))))))))))
derive_free_closed wc_map_m

theorem wc_map_delta_l {n} (A R B F : Term n) : (wc_map_m A R B F).IsDelta0 :=
  .conj (.forallMem _ (.atom _ _ _)) (.conj (fn0_delta_l ..) (.conj
    (.forallMem _ (.existsMem _ (rd_entry0_delta_l ..)))
    (.forallMem _ (.forallMem _ (.imp (rd_entry0_delta_l ..) (.forallMem _
      (.iff (.mem _ _) (.existsMem _ (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..))))))))))

theorem wc_map_sat_l (hE : Extensional M) {n} (ρ : Env M n) (A R B F : Term n) :
    Formula.satisfies ρ (wc_map_m A R B F) ↔ Wc_map_d (A.eval ρ) (R.eval ρ) (B.eval ρ) (F.eval ρ) := by
  simp only [wc_map_m, Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_existsMem_iff, Formula.satisfies_subset_iff, fn0_sat_l hE,
    Formula.satisfies_imp_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
    rd_entry0_sat_l hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  exact ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩, fun h => ⟨h.transitive, h.function, h.onto, h.equation⟩⟩

theorem Wc_map_d.graph_l {A R B F : M.Domain} (h : Wc_map_d A R B F) : Wc_graph_d A R F := by
  refine ⟨fun p hp => (h.function.1 p hp).elim fun a ha => ha.2.elim fun x hx => ⟨a, x, hx.2⟩, ?_⟩
  intro a x ha
  have hA := (h.function.bound_l ha).1
  have hB := (h.function.bound_l ha).2
  refine ⟨hA, fun b hb _ => (h.function.2.1 b hb).imp fun y hy => hy.2, fun y => ⟨?_, ?_⟩⟩
  · intro hy
    exact (h.equation a hA x hB ha y (h.transitive x hB y hy)).mp hy
  · rintro ⟨b, hb, hr, hf⟩
    exact (h.equation a hA x hB ha y (h.function.bound_l hf).2).mpr ⟨b, hb, hr, hf⟩

theorem wc_map_exists_l (hZF : M.Models ZF) {A R : M.Domain} (hw : Wf_rel_d A R) :
    ∃ B F, Wc_map_d A R B F := by
  obtain ⟨B, F, hf, hg, onto, ht⟩ := wc_collapse_l hZF hw
  exact ⟨B, F, ht, hf, fun x hx => ((onto x).mp hx).imp fun a ha => ⟨(hf.bound_l ha).1, ha⟩,
    fun a _ x _ ha y _ => (hg.2 a x ha).2.2 y⟩

theorem Wc_map_d.well_founded_l (hKP : M.Models KP) {A R B F : M.Domain} (h : Wc_map_d A R B F) :
    Wf_rel_d A R := by
  intro Y hs ⟨a, ha⟩
  let ρ : Env M 2 := ⟨Fin.cases Y (fun _ => F), fun _ => Y⟩
  let φ : Delta0UnarySchema 2 := {
    body := Formula.existsMem (.bound 1) (rd_entry0_m .newest (.bound 1) (.bound 3))
    delta0 := .existsMem _ (rd_entry0_delta_l ..) }
  have sat x : φ.toUnarySchema.denote ρ x ↔ ∃ a, M.mem a Y ∧ Rd_entry_d a x F := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_existsMem_iff, rd_entry0_sat_l hKP.1]; rfl
  obtain ⟨Z, spec⟩ := KP.separation_exists_d hKP φ ρ B
  have read x : M.mem x Z ↔ M.mem x B ∧ ∃ a, M.mem a Y ∧ Rd_entry_d a x F :=
    (spec x).trans (and_congr_right fun _ => sat x)
  obtain ⟨x, hx, hax⟩ := h.function.2.1 a (hs a ha)
  obtain ⟨y, hy, minimal⟩ := KP.mem_minimal_exists_d hKP ⟨x, (read x).mpr ⟨hx, a, ha, hax⟩⟩
  obtain ⟨hyB, b, hb, hby⟩ := (read y).mp hy
  refine ⟨b, hb, fun c hc hcb => ?_⟩
  obtain ⟨v, hv, hcv⟩ := h.function.2.1 c (hs c hc)
  exact minimal v ((read v).mpr ⟨hv, c, hc, hcv⟩)
    ((h.equation b (hs b hb) y hyB hby v hv).mpr ⟨c, hs c hc, hcb, hcv⟩)

theorem Wc_map_d.iso_l (hZF : M.Models ZF) {A R B F : M.Domain}
    (h : Wc_map_d A R B F) (he : Wc_ext_d A R) : Wc_iso_d A R B F := by
  have hw := h.well_founded_l (ZF.modelsKP hZF)
  have inj a b x (ha : Rd_entry_d a x F) (hb : Rd_entry_d b x F) : a = b :=
    wc_value_injective_l hZF hw he (h.function.bound_l ha).1 (h.function.bound_l hb).1
      ⟨F, h.graph_l, ha⟩ ⟨F, h.graph_l, hb⟩
  exact ⟨h.transitive, h.function, h.onto, fun a _ b _ x _ => inj a b x,
    fun a _ b _ x _ y _ => h.graph_l.member_l h.function inj⟩

end YesMetaZFC.SetTheory
