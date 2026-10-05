import YesMetaZFC.SetTheory.Collapse.RelationIso
import YesMetaZFC.SetTheory.InnerModel.Recursion.Composition

/-! # Mostowski 同构的有界证书

把传递像、满射、单射和隶属保持全部限制在给定载体内。证书是 Δ₀，
故传递模型中的实际同构也是背景模型中的同构；存在性仍由原关系递归给出。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def wc_ext_m {n} (A R : Term n) : Formula 1 n :=
  Formula.forallMem A (Formula.forallMem A.weaken (.imp
    (Formula.forallMem A.weaken.weaken
      (.iff (rd_entry0_m .newest (.bound 2) R.weaken.weaken.weaken)
        (rd_entry0_m .newest (.bound 1) R.weaken.weaken.weaken)))
    (Formula.extensionalEq (.bound 1) .newest)))
derive_free_closed wc_ext_m

theorem wc_ext_delta_l {n} (A R : Term n) : (wc_ext_m A R).IsDelta0 :=
  .forallMem _ (.forallMem _ (.imp (.forallMem _ (.iff (rd_entry0_delta_l ..) (rd_entry0_delta_l ..))) (.atom _ _ _)))

theorem wc_ext_sat_l (hE : Extensional M) {n} (ρ : Env M n) (A R : Term n) :
    Formula.satisfies ρ (wc_ext_m A R) ↔ Wc_ext_d (A.eval ρ) (R.eval ρ) := by
  simp only [wc_ext_m, Wc_ext_d, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_iff_iff, rd_entry0_sat_l hE, Formula.satisfies_extensionalEq_iff_eq hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

structure Wc_iso_d (A R B F : M.Domain) : Prop where
  transitive : M.TransitiveSet B
  function : Fn0_d A B F
  onto : ∀ x, M.mem x B → ∃ a, M.mem a A ∧ Rd_entry_d a x F
  injective : ∀ a, M.mem a A → ∀ b, M.mem b A → ∀ x, M.mem x B →
    Rd_entry_d a x F → Rd_entry_d b x F → a = b
  member : ∀ a, M.mem a A → ∀ b, M.mem b A → ∀ x, M.mem x B → ∀ y, M.mem y B →
    Rd_entry_d a x F → Rd_entry_d b y F → (Rd_entry_d a b R ↔ M.mem x y)

def wc_iso_m {n} (A R B F : Term n) : Formula 1 n :=
  .conj (Formula.forallMem B (Formula.subset .newest B.weaken))
    (.conj (fn0_m A B F) (.conj
      (Formula.forallMem B (Formula.existsMem A.weaken (rd_entry0_m .newest (.bound 1) F.weaken.weaken)))
      (.conj (Formula.forallMem A (Formula.forallMem A.weaken (Formula.forallMem B.weaken.weaken
        (.imp (rd_entry0_m (.bound 2) .newest F.weaken.weaken.weaken)
          (.imp (rd_entry0_m (.bound 1) .newest F.weaken.weaken.weaken) (Formula.extensionalEq (.bound 2) (.bound 1)))))))
        (Formula.forallMem A (Formula.forallMem A.weaken (Formula.forallMem B.weaken.weaken
          (Formula.forallMem B.weaken.weaken.weaken
            (.imp (rd_entry0_m (.bound 3) (.bound 1) F.weaken.weaken.weaken.weaken)
              (.imp (rd_entry0_m (.bound 2) .newest F.weaken.weaken.weaken.weaken)
                (.iff (rd_entry0_m (.bound 3) (.bound 2) R.weaken.weaken.weaken.weaken) (.mem (.bound 1) .newest)))))))))))
derive_free_closed wc_iso_m

theorem wc_iso_delta_l {n} (A R B F : Term n) : (wc_iso_m A R B F).IsDelta0 :=
  .conj (.forallMem _ (.atom _ _ _)) (.conj (fn0_delta_l ..) (.conj
    (.forallMem _ (.existsMem _ (rd_entry0_delta_l ..)))
    (.conj (.forallMem _ (.forallMem _ (.forallMem _
      (.imp (rd_entry0_delta_l ..) (.imp (rd_entry0_delta_l ..) (.atom _ _ _))))))
      (.forallMem _ (.forallMem _ (.forallMem _ (.forallMem _
        (.imp (rd_entry0_delta_l ..) (.imp (rd_entry0_delta_l ..) (.iff (rd_entry0_delta_l ..) (.mem _ _)))))))))))

theorem wc_iso_sat_l (hE : Extensional M) {n} (ρ : Env M n) (A R B F : Term n) :
    Formula.satisfies ρ (wc_iso_m A R B F) ↔ Wc_iso_d (A.eval ρ) (R.eval ρ) (B.eval ρ) (F.eval ρ) := by
  simp only [wc_iso_m, Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_existsMem_iff, Formula.satisfies_subset_iff, fn0_sat_l hE,
    Formula.satisfies_imp_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_extensionalEq_iff_eq hE, rd_entry0_sat_l hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  exact ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩,
    fun h => ⟨h.transitive, h.function, h.onto, h.injective, h.member⟩⟩

theorem wc_iso_exists_l (hZF : M.Models ZF) {A R : M.Domain}
    (hw : Wf_rel_d A R) (he : Wc_ext_d A R) : ∃ B F, Wc_iso_d A R B F := by
  obtain ⟨B, F, ht, _, hf, hm⟩ := wc_iso_l hZF hw he
  exact ⟨B, F, ht, fn0_of_function_l (ZF.modelsKP hZF) hf.1.1, hf.2,
    fun a _ b _ x _ => hf.1.2 a b x, fun a _ b _ x _ y _ => hm a b x y⟩

theorem Wc_iso_d.bijection_l (hKP : M.Models KP) {A R B F : M.Domain} (h : Wc_iso_d A R B F) :
    M.IsSetBijectionFromTo (kp_pair_l hKP) F A B :=
  ⟨⟨fn0_function_l hKP h.function, fun a b x ha hb =>
    h.injective a (h.function.bound_l ha).1 b (h.function.bound_l hb).1 x (h.function.bound_l ha).2 ha hb⟩, h.onto⟩

theorem Wc_iso_d.graph_l {A R B F : M.Domain} (h : Wc_iso_d A R B F) : Wc_graph_d A R F := by
  refine ⟨fun p hp => (h.function.1 p hp).elim fun a ha => ha.2.elim fun x hx => ⟨a, x, hx.2⟩, ?_⟩
  intro a x ha
  have haA := (h.function.bound_l ha).1
  have hxB := (h.function.bound_l ha).2
  refine ⟨haA, fun b hb _ => (h.function.2.1 b hb).imp fun y hy => hy.2, fun y => ⟨?_, ?_⟩⟩
  · intro hy
    have hyB := h.transitive x hxB y hy
    obtain ⟨b, hb, hby⟩ := h.onto y hyB
    exact ⟨b, hb, (h.member b hb a haA y hyB x hxB hby ha).mpr hy, hby⟩
  · rintro ⟨b, hb, hba, hby⟩
    exact (h.member b hb a haA y (h.function.bound_l hby).2 x hxB hby ha).mp hba

/-- 传递像中的成员外延性回拉为原关系的外延性。 -/
theorem Wc_iso_d.extensional_l (hE : Extensional M) {A R B F : M.Domain} (h : Wc_iso_d A R B F) :
    Wc_ext_d A R := by
  intro a ha b hb same
  obtain ⟨x, hx, hax⟩ := h.function.2.1 a ha
  obtain ⟨y, hy, hby⟩ := h.function.2.1 b hb
  have sub {a b x y} (ha : M.mem a A) (hb : M.mem b A) (hx : M.mem x B) (hy : M.mem y B)
      (hax : Rd_entry_d a x F) (hby : Rd_entry_d b y F)
      (same : ∀ z, M.mem z A → (Rd_entry_d z a R ↔ Rd_entry_d z b R)) : M.MemberSubset x y := by
    intro v hv
    have hvB := h.transitive x hx v hv
    obtain ⟨z, hz, hzv⟩ := h.onto v hvB
    exact (h.member z hz b hb v hvB y hy hzv hby).mp ((same z hz).mp
      ((h.member z hz a ha v hvB x hx hzv hax).mpr hv))
  have eq : x = y := hE.eq_of_same_members x y (fun v =>
    ⟨sub ha hb hx hy hax hby same v, sub hb ha hy hx hby hax (fun z hz => (same z hz).symm) v⟩)
  exact h.injective a ha b hb y hy (eq ▸ hax) hby

/-- 对非空子集取像，再从其成员极小元回拉原关系的极小元；仅需 KP。 -/
theorem Wc_iso_d.well_founded_l (hKP : M.Models KP) {A R B F : M.Domain} (h : Wc_iso_d A R B F) :
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
    ((h.member c (hs c hc) b (hs b hb) v hv y hyB hcv hby).mp hcb)

/-- 同一关系的两个传递塌缩具有同一实际集合像，而非仅有一个外部同构。 -/
theorem Wc_iso_d.unique_l (hZF : M.Models ZF) {A R B C F G : M.Domain}
    (h : Wc_iso_d A R B F) (g : Wc_iso_d A R C G) : B = C := by
  have hw := h.well_founded_l (ZF.modelsKP hZF)
  have sub {B C F G} (h : Wc_iso_d A R B F) (g : Wc_iso_d A R C G) : M.MemberSubset B C := by
    intro x hx
    obtain ⟨a, ha, hax⟩ := h.onto x hx
    obtain ⟨y, hy, hay⟩ := g.function.2.1 a ha
    exact (wc_value_unique_l hZF hw ⟨F, h.graph_l, hax⟩ ⟨G, g.graph_l, hay⟩).symm ▸ hy
  exact hZF.1.eq_of_same_members B C (fun x => ⟨sub h g x, sub g h x⟩)

/-- 传递塌缩的枚举图也唯一，因而可在另一模型内还原原枚举本身。 -/
theorem Wc_iso_d.graph_unique_l (hZF : M.Models ZF) {A R B C F G : M.Domain}
    (h : Wc_iso_d A R B F) (g : Wc_iso_d A R C G) : F = G := by
  apply h.function.ext_l hZF.1 g.function
  intro a ha
  obtain ⟨x, _, hax⟩ := h.function.2.1 a ha
  obtain ⟨y, _, hay⟩ := g.function.2.1 a ha
  exact ⟨x, hax, (wc_value_unique_l hZF (h.well_founded_l (ZF.modelsKP hZF))
    ⟨F, h.graph_l, hax⟩ ⟨G, g.graph_l, hay⟩).symm ▸ hay⟩

end YesMetaZFC.SetTheory
