import YesMetaZFC.SetTheory.InnerModel.Rudimentary.Construction

/-! # 内部递归证书中的有界函数图与限制 -/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def Fn0_d (A B F : M.Domain) : Prop :=
  (∀ p, M.mem p F → ∃ a, M.mem a A ∧ ∃ b, M.mem b B ∧ KPair_d M p a b) ∧
  (∀ a, M.mem a A → ∃ b, M.mem b B ∧ Rd_entry_d a b F) ∧
  ∀ a, M.mem a A → ∀ b, M.mem b B → ∀ c, M.mem c B → Rd_entry_d a b F → Rd_entry_d a c F → b = c

def fn0_m {n} (A B F : Term n) : Formula 1 n :=
  .conj (Formula.forallMem F (Formula.existsMem A.weaken (Formula.existsMem B.weaken.weaken
    (kpair0_m (.bound 2) (.bound 1) .newest))))
    (.conj (Formula.forallMem A (Formula.existsMem B.weaken (rd_entry0_m (.bound 1) .newest F.weaken.weaken)))
      (Formula.forallMem A (Formula.forallMem B.weaken (Formula.forallMem B.weaken.weaken
        (.imp (rd_entry0_m (.bound 2) (.bound 1) F.weaken.weaken.weaken)
          (.imp (rd_entry0_m (.bound 2) .newest F.weaken.weaken.weaken) (Formula.extensionalEq (.bound 1) .newest)))))))
derive_free_closed fn0_m

theorem fn0_delta_l {n} (A B F : Term n) : (fn0_m A B F).IsDelta0 :=
  .conj (.forallMem _ (.existsMem _ (.existsMem _ (kpair0_delta_l ..))))
    (.conj (.forallMem _ (.existsMem _ (rd_entry0_delta_l ..)))
      (.forallMem _ (.forallMem _ (.forallMem _ (.imp (rd_entry0_delta_l ..) (.imp (rd_entry0_delta_l ..) (.atom _ _ _)))))))

theorem fn0_sat_l (hE : Extensional M) {n} (ρ : Env M n) (A B F : Term n) :
    Formula.satisfies ρ (fn0_m A B F) ↔ Fn0_d (A.eval ρ) (B.eval ρ) (F.eval ρ) := by
  simp only [fn0_m, Fn0_d, Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_existsMem_iff, Formula.satisfies_imp_iff, kpair0_sat_l hE, rd_entry0_sat_l hE,
    Formula.satisfies_extensionalEq_iff_eq hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

def kp_pair_l (hKP : M.Models KP) : kpair_convention_l.Interpretation M :=
  kpair_interpretation_l M hKP.1 (KP.exists_pair hKP)

theorem Fn0_d.bound_l {A B F a b : M.Domain} (h : Fn0_d A B F) (ha : Rd_entry_d a b F) :
    M.mem a A ∧ M.mem b B := by
  obtain ⟨p, hp, hpf⟩ := ha
  obtain ⟨x, hx, y, hy, hxy⟩ := h.1 p hpf
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M hp hxy
  exact ⟨hx, hy⟩

theorem fn0_function_l (hKP : M.Models KP) {A B F : M.Domain} (h : Fn0_d A B F) :
    M.IsSetFunctionFromTo (kp_pair_l hKP) F A B := by
  refine ⟨⟨?_, ?_⟩, ?_, h.2.1⟩
  · intro p hp
    obtain ⟨a, _, b, _, hab⟩ := h.1 p hp
    exact ⟨a, b, hab⟩
  · intro a b c hb hc
    exact h.2.2 a (h.bound_l hb).1 b (h.bound_l hb).2 c (h.bound_l hc).2 hb hc
  · exact fun a => ⟨fun ha => (h.2.1 a ha).elim fun b hb => ⟨b, hb.2⟩,
      fun ⟨b, hb⟩ => (h.bound_l hb).1⟩

theorem fn0_of_function_l (hKP : M.Models KP) {A B F : M.Domain}
    (h : M.IsSetFunctionFromTo (kp_pair_l hKP) F A B) : Fn0_d A B F := by
  refine ⟨?_, h.2.2, fun a _ b _ c _ => h.1.2 a b c⟩
  intro p hp
  obtain ⟨a, b, hab⟩ := h.1.1 p hp
  have he : M.PairMember (kp_pair_l hKP) a b F := ⟨p, hab, hp⟩
  exact ⟨a, h.input_mem_of_pairMember he, b, h.output_mem_of_pairMember he, hab⟩

def Res0_d (R F A B : M.Domain) : Prop := M.MemberSubset R F ∧
  (∀ p, M.mem p R → ∃ a, M.mem a A ∧ ∃ b, M.mem b B ∧ KPair_d M p a b) ∧
  ∀ a, M.mem a A → ∀ b, M.mem b B → (Rd_entry_d a b R ↔ Rd_entry_d a b F)

def res0_m {n} (R F A B : Term n) : Formula 1 n :=
  .conj (Formula.subset R F) (.conj
    (Formula.forallMem R (Formula.existsMem A.weaken (Formula.existsMem B.weaken.weaken
      (kpair0_m (.bound 2) (.bound 1) .newest))))
    (Formula.forallMem A (Formula.forallMem B.weaken
      (.iff (rd_entry0_m (.bound 1) .newest R.weaken.weaken) (rd_entry0_m (.bound 1) .newest F.weaken.weaken)))))
derive_free_closed res0_m

theorem res0_delta_l {n} (R F A B : Term n) : (res0_m R F A B).IsDelta0 :=
  .conj (.atom _ _ _) (.conj (.forallMem _ (.existsMem _ (.existsMem _ (kpair0_delta_l ..))))
    (.forallMem _ (.forallMem _ (.iff (rd_entry0_delta_l ..) (rd_entry0_delta_l ..)))))

theorem res0_sat_l (hE : Extensional M) {n} (ρ : Env M n) (R F A B : Term n) :
    Formula.satisfies ρ (res0_m R F A B) ↔ Res0_d (R.eval ρ) (F.eval ρ) (A.eval ρ) (B.eval ρ) := by
  simp only [res0_m, Res0_d, Formula.satisfies_conj_iff, Formula.satisfies_subset_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_existsMem_iff, Formula.satisfies_iff_iff,
    kpair0_sat_l hE, rd_entry0_sat_l hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem res0_restriction_l (hKP : M.Models KP) {R F X Y A : M.Domain}
    (hF : Fn0_d X Y F) (h : Res0_d R F A Y) : M.IsRestrictionOf (kp_pair_l hKP) R F A := by
  refine ⟨fun p hp => (h.2.1 p hp).elim fun a ha => ha.2.elim fun b hb => ⟨a, b, hb.2⟩, fun a b => ?_⟩
  constructor
  · rintro ⟨p, hp, hpr⟩
    obtain ⟨x, hx, y, _, hxy⟩ := h.2.1 p hpr
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M hp hxy
    exact ⟨hx, p, hp, h.1 p hpr⟩
  · rintro ⟨ha, hab⟩
    exact (h.2.2 a ha b (hF.bound_l hab).2).mpr hab

theorem res0_exists_l (hKP : M.Models KP) (F A Y : M.Domain) :
    ∃ R, Res0_d R F A Y := by
  let ρ : Env M 2 := (⟨fun _ => A, fun _ => A⟩ : Env M 1).push Y
  let φ : Delta0UnarySchema 2 := {
    body := Formula.existsMem (.bound 2) (Formula.existsMem (.bound 2) (kpair0_m (.bound 2) (.bound 1) .newest))
    delta0 := .existsMem _ (.existsMem _ (kpair0_delta_l ..)) }
  have hφ p : φ.toUnarySchema.denote ρ p ↔ ∃ a, M.mem a A ∧ ∃ b, M.mem b Y ∧ KPair_d M p a b := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_existsMem_iff, kpair0_sat_l hKP.1]
    rfl
  obtain ⟨R, hR⟩ := KP.separation_exists_d hKP φ ρ F
  have hr p : M.mem p R ↔ M.mem p F ∧ ∃ a, M.mem a A ∧ ∃ b, M.mem b Y ∧ KPair_d M p a b :=
    (hR p).trans (and_congr_right fun _ => hφ p)
  refine ⟨R, fun p hp => ((hr p).mp hp).1, fun p hp => ((hr p).mp hp).2, fun a ha b hb => ?_⟩
  exact ⟨fun ⟨p, hp, hpr⟩ => ⟨p, hp, ((hr p).mp hpr).1⟩,
    fun ⟨p, hp, hpf⟩ => ⟨p, hp, (hr p).mpr ⟨hpf, a, ha, b, hb, hp⟩⟩⟩

theorem res0_of_restriction_l (hKP : M.Models KP) {R F X Y A : M.Domain}
    (hF : Fn0_d X Y F) (h : M.IsRestrictionOf (kp_pair_l hKP) R F A) : Res0_d R F A Y := by
  have row p (hp : M.mem p R) : ∃ a, M.mem a A ∧ ∃ b, M.mem b Y ∧ KPair_d M p a b := by
    obtain ⟨a, b, hab⟩ := h.1 p hp
    have hh := (h.2 a b).mp ⟨p, hab, hp⟩
    exact ⟨a, hh.1, b, (hF.bound_l hh.2).2, hab⟩
  refine ⟨fun p hp => ?_, row, fun a ha b _ => (h.2 a b).trans ⟨And.right, fun h => ⟨ha, h⟩⟩⟩
  obtain ⟨a, _, b, _, hab⟩ := row p hp
  obtain ⟨q, hq, hqf⟩ := ((h.2 a b).mp ⟨p, hab, hp⟩).2
  exact (kpair_unique_l M hKP.1 hq hab) ▸ hqf

end YesMetaZFC.SetTheory.InnerModel
